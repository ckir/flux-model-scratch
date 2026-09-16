#!/usr/bin/env python3
"""Runner for the lock-protocol model check.

Design: docs/superpowers/specs/2026-09-11-lock-protocol-model-check-design.md, Section 4.
Reads expected.toml, runs TLC for each selected run, judges each result against its
expectation, and exits 0 (every run matched), 1 (a run did not match), or 2 (a tooling
failure). Standard library only.
"""

from __future__ import annotations

import sys

if sys.version_info < (3, 11):
    sys.stderr.write("run.py: Python 3.11 or later is required (it reads TOML with tomllib)\n")
    sys.exit(2)

import argparse  # noqa: E402
import hashlib  # noqa: E402
import json  # noqa: E402
import re  # noqa: E402
import shutil  # noqa: E402
import subprocess  # noqa: E402
import time  # noqa: E402
import tomllib  # noqa: E402
import urllib.request  # noqa: E402
from dataclasses import dataclass  # noqa: E402
from pathlib import Path  # noqa: E402
from typing import Callable  # noqa: E402

# tla2tools.jar pin (TLC 2.19). v1.8.0 is a rolling prerelease whose asset changes; do not pin it.
TLA_TAG = "v1.7.4"
TLA_SHA256 = "936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"
TLA_URL = f"https://github.com/tlaplus/tlaplus/releases/download/{TLA_TAG}/tla2tools.jar"

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
TARGET = REPO / "target" / "tla"

KINDS = ("check", "liveness", "seeded", "witness")
RUN_KEYS = {"name", "module", "config", "scenario", "kind", "violated", "open_findings", "unreached", "timeout_minutes",
            "constants", "symmetry", "tightened"}
FINDING_KEYS = {"name", "tracking", "fix_flag"}
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
FIX_FLAG = re.compile(r"FIX_[A-Z0-9_]+")

# TLC -tool message codes, measured against TLC 2.19 (tla2tools v1.7.4).
C_INVARIANT_INITIAL = 2107  # "Invariant X is violated by the initial state:"
C_INVARIANT = 2110  # "Invariant X is violated."
C_DEADLOCK = 2114  # "Deadlock reached."
C_TEMPORAL = 2116  # "Temporal properties were violated." (names no property)
C_BEHAVIOR = 2121  # "The behavior up to this point is:"
C_FINISHED = 2186  # "Finished in ..."; printed at the end of every run, errors included
C_SUCCESS = 2193  # "Model checking completed. No error has been found."
C_STATE = 2217  # one state of a trace (severity 4)
C_COUNTEREXAMPLE = 2264  # "The following behavior constitutes a counter-example:"
ALLOWED_ERROR_CODES = {C_INVARIANT_INITIAL, C_INVARIANT, C_DEADLOCK, C_TEMPORAL, C_BEHAVIOR, C_COUNTEREXAMPLE}
SEVERITY_ERROR = 1

# '-coverage 1' message codes (design Section 4, "Five things about reading that report").
C_COVERAGE_START = 2201  # "The coverage statistics at ..."
C_COVERAGE_ACTION = 2772  # one action's line: <Name ...>: DISTINCT:TOTAL - a label
C_COVERAGE_INIT = 2773  # the Init action's line, same shape - not a label
C_COVERAGE_DEF = 2774  # an invariant or definition being evaluated, no counts - not a label
C_COVERAGE_COST = 2221  # an indented cost sub-line for an expression - not a label
C_COVERAGE_END = 2202  # "End of statistics[...]"
C_COVERAGE_END_LONG = 2777  # "End of statistics (please note that for performance reasons ...)";
# TLC prints this form, instead of 2202, once a run has gone on long enough to warn about the cost
# of leaving coverage/cost statistics on.

DEADLOCK = "DEADLOCK"
TRACE_STATES_SHOWN = 60

# TLC .cfg keywords, each mapped to its singular form.
CFG_KEYWORDS = {
    "CONSTANT": "CONSTANT", "CONSTANTS": "CONSTANT", "INIT": "INIT", "NEXT": "NEXT",
    "SPECIFICATION": "SPECIFICATION", "INVARIANT": "INVARIANT", "INVARIANTS": "INVARIANT",
    "PROPERTY": "PROPERTY", "PROPERTIES": "PROPERTY", "SYMMETRY": "SYMMETRY",
    "CONSTRAINT": "CONSTRAINT", "CONSTRAINTS": "CONSTRAINT", "ACTION_CONSTRAINT": "ACTION_CONSTRAINT",
    "ACTION_CONSTRAINTS": "ACTION_CONSTRAINT", "VIEW": "VIEW", "CHECK_DEADLOCK": "CHECK_DEADLOCK",
    "POSTCONDITION": "POSTCONDITION", "ALIAS": "ALIAS", "TYPE": "TYPE", "TYPE_CONSTRAINT": "TYPE_CONSTRAINT",
}


class ExpectedError(Exception):
    """expected.toml or a file it names is invalid (exit code 2)."""


class ToolingError(Exception):
    """Java, the jar, or TLC failed in a way that says nothing about the model (exit code 2)."""


@dataclass(frozen=True)
class OpenFinding:
    name: str
    tracking: str
    fix_flag: str


@dataclass(frozen=True)
class Run:
    name: str
    module: str
    config: str
    scenario: str
    kind: str
    violated: tuple[str, ...]
    open_findings: tuple[OpenFinding, ...]
    unreached: tuple[tuple[str, str], ...]
    timeout_minutes: int
    constants: tuple[tuple[str, object], ...]
    symmetry: tuple[str, str] | None
    tightened: tuple[str, str] | None


@dataclass(frozen=True)
class Expected:
    scenarios: list[str]
    runs: list[Run]
    never_reached: tuple[tuple[str, str], ...]
    deferred: tuple[tuple[str, str, str], ...]


@dataclass(frozen=True)
class Message:
    code: int
    severity: int
    text: str


@dataclass(frozen=True)
class Outcome:
    tooling_error: str | None
    observed: frozenset[str]
    distinct_states: int | None
    trace: tuple[str, ...]


@dataclass(frozen=True)
class Result:
    name: str
    status: str  # "ok", "mismatch", or "tooling"
    expected: frozenset[str]
    observed: frozenset[str]
    distinct_states: int | None
    seconds: float
    detail: str
    trace: tuple[str, ...]
    log: Path | None


# ---------------------------------------------------------------------------------------
# TLC configuration files


# A .cfg token: a block comment, a line comment, a string, `<-`, a word, or any other character.
_CFG_TOKEN = re.compile(r'\(\*.*?\*\)|\\\*[^\n]*|"(?:[^"\\\n]|\\.)*"|<-|[A-Za-z0-9_]+|\S', re.S)


def _is_comment(token: str) -> bool:
    return token.startswith(("(*", "\\*"))


def cfg_sections(text: str) -> dict[str, list[str]]:
    """Map each keyword of a TLC .cfg file (singular form) to the tokens that follow it.

    Comments are skipped, and a string literal is a value, never a keyword."""
    sections: dict[str, list[str]] = {}
    current: str | None = None
    for match in _CFG_TOKEN.finditer(text):
        token = match.group(0)
        if _is_comment(token):
            continue
        if token.startswith('"'):
            token = '""'
        if token in CFG_KEYWORDS:
            current = CFG_KEYWORDS[token]
            sections.setdefault(current, [])
        elif current is not None:
            sections[current].append(token)
    return sections


def cfg_properties(text: str) -> list[str]:
    return [t for t in cfg_sections(text).get("PROPERTY", []) if IDENT.fullmatch(t)]


def cfg_constants(text: str) -> dict[str, object]:
    """Parse the literal-valued assignments in a TLC .cfg's CONSTANT/CONSTANTS section.

    An entry is returned only for a literal value: an integer literal (int, optionally negative), TRUE/FALSE
    (bool), a double-quoted string (str, unquoted), or a set literal of identifiers ({a, b} or {}, frozenset[str]).
    A model-value assignment (NAME = someIdentifier) is omitted: it names no literal the runner can compare
    against 'constants'. The .cfg is the one file a person can edit to make a failing run pass, so this parser
    fails CLOSED (raises ExpectedError) rather than silently skipping anything else it cannot read: a `<-`
    substitution, the same constant assigned twice, a value that is none of the literal shapes above and is not
    a single identifier, or any token sequence that is not `NAME = VALUE` (a missing '=', a stray token, an
    unterminated set, or a set element that is not an identifier)."""
    tokens: list[tuple[str, int, int]] = []
    current: str | None = None
    for match in _CFG_TOKEN.finditer(text):
        token = match.group(0)
        if _is_comment(token):
            continue
        if token in CFG_KEYWORDS:
            current = CFG_KEYWORDS[token]
            continue
        if current == "CONSTANT":
            tokens.append((token, match.start(), match.end()))

    result: dict[str, object] = {}
    seen: set[str] = set()
    i, n = 0, len(tokens)
    while i < n:
        name, _, _ = tokens[i]
        if IDENT.fullmatch(name) is None:
            raise ExpectedError(f"the config's CONSTANT section has an unexpected token where a constant name "
                                 f"was expected: {name!r}")
        i += 1
        if i >= n:
            raise ExpectedError(f"the config's CONSTANT section ends after {name!r} with no '=' and value")
        op, _, _ = tokens[i]
        i += 1
        if op == "<-":
            raise ExpectedError(f"the config substitutes an operator for {name!r} ('{name} <- ...'), which this "
                                 "runner cannot read as a literal constant")
        if op != "=":
            raise ExpectedError(f"the config's CONSTANT section has {name!r} not followed by '=' (found {op!r})")
        if name in seen:
            raise ExpectedError(f"the config assigns {name!r} more than once in its CONSTANT section")
        seen.add(name)
        if i >= n:
            raise ExpectedError(f"the config's CONSTANT section assigns {name!r} no value")
        value, vstart, vend = tokens[i]
        i += 1
        if value.startswith('"'):
            result[name] = value[1:-1]
        elif value == "{":
            elements: list[str] = []
            expect_element = True
            closed = False
            while i < n:
                tok, _, _ = tokens[i]
                if tok == "}":
                    if expect_element and elements:
                        raise ExpectedError(f"the config's set for {name!r} has a trailing comma before '}}'")
                    i += 1
                    closed = True
                    break
                if expect_element:
                    if IDENT.fullmatch(tok) is None:
                        raise ExpectedError(f"the config's set for {name!r} has a non-identifier element {tok!r}")
                    elements.append(tok)
                    expect_element = False
                else:
                    if tok != ",":
                        raise ExpectedError(f"the config's set for {name!r} is missing a comma before {tok!r}")
                    expect_element = True
                i += 1
            if not closed:
                raise ExpectedError(f"the config's set for {name!r} is never closed with '}}'")
            result[name] = frozenset(elements)
        elif value.isdigit():
            result[name] = int(value)
        elif value == "-" and i < n and tokens[i][0].isdigit() and tokens[i][1] == vend:
            digits, _, _ = tokens[i]
            i += 1
            result[name] = -int(digits)
        elif value in ("TRUE", "FALSE"):
            result[name] = value == "TRUE"
        elif IDENT.fullmatch(value) is not None:
            pass  # a model value; not a literal, and not an error
        else:
            raise ExpectedError(f"the config assigns {name!r} a value this runner cannot read: {value!r}")
    return result


def fixed_cfg_text(text: str, flags: list[str]) -> str:
    """Return the .cfg text with each fix flag switched from FALSE to TRUE (comments are left alone)."""
    for flag in flags:
        comments = [m.span() for m in _CFG_TOKEN.finditer(text) if _is_comment(m.group(0))]
        pattern = re.compile(rf"\b{re.escape(flag)}\s*=\s*FALSE\b")
        hits = [m for m in pattern.finditer(text) if not any(a <= m.start() < b for a, b in comments)]
        if len(hits) != 1:
            raise ExpectedError(f"fix flag {flag} must appear exactly once as '{flag} = FALSE' in the config "
                                "(outside comments)")
        text = text[: hits[0].start()] + f"{flag} = TRUE" + text[hits[0].end():]
    return text


# ---------------------------------------------------------------------------------------
# expected.toml


def _require(cond: bool, message: str) -> None:
    if not cond:
        raise ExpectedError(message)


def _str_list(value: object, where: str) -> tuple[str, ...]:
    _require(isinstance(value, list) and all(isinstance(v, str) and IDENT.fullmatch(v) for v in value),
             f"{where} must be a list of TLA+ identifiers")
    assert isinstance(value, list)
    _require(len(set(value)) == len(value), f"{where} has duplicates")
    return tuple(value)


def _load_label_reasons(value: object, subject: str) -> tuple[tuple[str, str], ...]:
    """Parse a list of {label, reason} tables, as used by 'unreached' and 'never_reached'.

    `subject` names the field for error messages, e.g. "run 'x-check': unreached" or "'never_reached'".
    A label must be a non-empty TLA+ identifier: real PlusCal labels (e.g. `plain_recover`) do not all
    start with `S<digits>_`, so that stricter shape is not checked here. Whether the label exists in the
    model at all is a later task's concern."""
    _require(isinstance(value, list), f"{subject} must be an array of tables")
    assert isinstance(value, list)
    entries: list[tuple[str, str]] = []
    for item in value:
        _require(isinstance(item, dict) and set(item) == {"label", "reason"},
                 f"{subject}: each entry has exactly 'label' and 'reason'")
        label, reason = item.get("label"), item.get("reason")
        _require(isinstance(label, str) and IDENT.fullmatch(label) is not None,
                 f"{subject}: each label must be a TLA+ identifier")
        _require(isinstance(reason, str) and reason, f"{subject}: each reason must be a non-empty string")
        entries.append((label, reason))
    labels = [label for label, _ in entries]
    _require(len(set(labels)) == len(labels), f"{subject} has duplicate labels")
    return tuple(entries)


def _load_deferred(value: object, subject: str) -> tuple[tuple[str, str, str], ...]:
    """Parse the top-level 'deferred' list (design Section 4): {label, scenario, reason} tables
    holding a label that no BUILT scenario covers but a planned one will. Unlike 'never_reached', a
    deferred label is reachable and keeps its trace.toml entries. Whether the label exists in some
    run's module, whether it collides with 'never_reached', and whether its scenario is already
    built are checked by the caller, which has the label universe and 'scenarios' list to hand."""
    _require(isinstance(value, list), f"{subject} must be an array of tables")
    assert isinstance(value, list)
    entries: list[tuple[str, str, str]] = []
    for item in value:
        _require(isinstance(item, dict) and set(item) == {"label", "scenario", "reason"},
                 f"{subject}: each entry has exactly 'label', 'scenario', 'reason'")
        label, scenario, reason = item.get("label"), item.get("scenario"), item.get("reason")
        _require(isinstance(label, str) and IDENT.fullmatch(label) is not None,
                 f"{subject}: each label must be a TLA+ identifier")
        _require(isinstance(scenario, str) and scenario, f"{subject}: each scenario must be a non-empty string")
        _require(isinstance(reason, str) and reason, f"{subject}: each reason must be a non-empty string")
        entries.append((label, scenario, reason))
    labels = [label for label, _, _ in entries]
    _require(len(set(labels)) == len(labels), f"{subject} has duplicate labels")
    return tuple(entries)


def load_expected(path: Path) -> Expected:
    """Load and validate expected.toml; module and config paths are resolved beside it."""
    base = path.parent
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as err:
        raise ExpectedError(f"cannot read {path}: {err}") from err

    _require(set(data) <= {"scenarios", "run", "never_reached", "deferred"},
             f"unknown top-level keys: {sorted(set(data) - {'scenarios', 'run', 'never_reached', 'deferred'})}")
    never_reached = _load_label_reasons(data.get("never_reached", []), "'never_reached'")
    deferred = _load_deferred(data.get("deferred", []), "'deferred'")
    scenarios = data.get("scenarios")
    _require(isinstance(scenarios, list) and scenarios and all(isinstance(s, str) for s in scenarios),
             "'scenarios' must be a non-empty list of names")
    assert isinstance(scenarios, list)
    _require(len(set(scenarios)) == len(scenarios), "'scenarios' has duplicates")
    for s in scenarios:
        _require(re.fullmatch(r"[a-z][a-z0-9-]*", s) is not None, f"scenario name {s!r} must be lowercase words joined by '-'")

    raw_runs = data.get("run", [])
    _require(isinstance(raw_runs, list), "'run' must be an array of tables")
    runs: list[Run] = []
    for i, raw in enumerate(raw_runs):
        _require(isinstance(raw, dict), f"run #{i + 1} must be a table")
        runs.append(_load_run(raw, i, scenarios, base))

    names = [r.name for r in runs]
    _require(len(set(names)) == len(names), f"duplicate run names: {sorted({n for n in names if names.count(n) > 1})}")
    for s in scenarios:
        _require(any(r.scenario == s for r in runs), f"scenario {s!r} has no runs")
    for run in runs:
        if run.kind == "seeded":
            open_names = {f.name for r in runs if r.scenario == run.scenario for f in r.open_findings}
            _require(run.violated[0] not in open_names,
                     f"{run.name}: its scenario carries an open finding on {run.violated[0]}, so the seed cannot be judged")

    # 'never_reached' excuses a label from every run's coverage; it must exist in some run's module.
    module_universes = {r.module: module_labels((base / f"{r.module}.tla").read_text(encoding="utf-8"))
                         for r in runs}
    every_label = frozenset(label for u in module_universes.values() for label in u.labels)
    for label, _reason in never_reached:
        _require(label in every_label,
                 f"'never_reached': label {label!r} is not in the label universe of any run's module")

    # 'deferred' names a reachable label a scenario not yet built will cover (design Section 4): it
    # must not collide with 'never_reached', must exist in some run's module, and its scenario must
    # not already be one of 'scenarios' (the runner does not read trace.toml's planned_scenarios).
    never_reached_labels = {label for label, _reason in never_reached}
    for label, scenario, _reason in deferred:
        _require(label not in never_reached_labels,
                 f"'deferred': label {label!r} is also in 'never_reached'")
        _require(label in every_label,
                 f"'deferred': label {label!r} is not in the label universe of any run's module")
        _require(scenario not in scenarios,
                 f"'deferred': scenario {scenario!r} is in 'scenarios' (the scenario is already built)")
    return Expected(scenarios, runs, never_reached, deferred)


def _constants_equal(a: object, b: object) -> bool:
    """Compare two constants values: an int never equals a bool, even though bool is an int subclass."""
    if isinstance(a, bool) or isinstance(b, bool):
        return isinstance(a, bool) and isinstance(b, bool) and a == b
    if isinstance(a, int) and isinstance(b, int):
        return a == b
    if isinstance(a, str) and isinstance(b, str):
        return a == b
    if isinstance(a, frozenset) and isinstance(b, frozenset):
        return a == b
    return False


def _load_constants(raw: dict, where: str) -> dict[str, object]:
    """Parse and shape-check the 'constants' table: int (not bool), bool, str, or a set of strings."""
    _require("constants" in raw, f"{where}: 'constants' is required")
    value = raw["constants"]
    _require(isinstance(value, dict), f"{where}: constants must be a table")
    assert isinstance(value, dict)
    result: dict[str, object] = {}
    for key, v in value.items():
        _require(isinstance(key, str) and IDENT.fullmatch(key) is not None,
                 f"{where}: constants key {key!r} must be a TLA+ identifier")
        _require(FIX_FLAG.fullmatch(key) is None, f"{where}: constants must not contain a fix flag ({key})")
        if isinstance(v, bool):
            result[key] = v
        elif isinstance(v, int):
            result[key] = v
        elif isinstance(v, str):
            result[key] = v
        elif isinstance(v, list) and all(isinstance(e, str) for e in v):
            _require(len(set(v)) == len(v), f"{where}: constants {key!r} has duplicate elements")
            result[key] = frozenset(v)
        else:
            _require(False, f"{where}: constants {key!r} must be an int, bool, string, or array of strings")
    return result


def strip_tla_comments(text: str) -> str:
    """Remove TLA+ comments from `text`: block comments `(* ... *)`, which nest (a depth counter),
    and line comments from `\\*` to end of line. Used before a textual search for a definition, so a
    definition that exists only inside a comment cannot satisfy the search."""
    out: list[str] = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth > 0:
            if text.startswith("(*", i):
                depth += 1
                i += 2
            elif text.startswith("*)", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text.startswith("(*", i):
            depth = 1
            i += 2
            continue
        if text.startswith("\\*", i):
            nl = text.find("\n", i)
            if nl == -1:
                i = n
            else:
                out.append("\n")
                i = nl + 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


# ---------------------------------------------------------------------------------------
# The model's labels and who owns them (design Section 4: the coverage gate's "four rules")


_ALGORITHM_START = re.compile(r"\(\*\s*--(?:fair\s+algorithm|algorithm)\b")
_PROCESS_HEADER = re.compile(r"\bprocess\s*\(\s*([A-Za-z_]\w*)\s*(\\in|=)\s*")
_PROCEDURE_HEADER = re.compile(r"\bprocedure\s+([A-Za-z_]\w*)\s*\(")
_CALL = re.compile(r"\bcall\s+([A-Za-z_]\w*)\s*\(")
_LABEL_LINE = re.compile(r"^[ \t]*([A-Za-z_]\w*):(?!=)")
_TOPLEVEL_DEF = re.compile(r"^([A-Za-z_]\w*)\s*==", re.M)


@dataclass(frozen=True)
class LabelUniverse:
    """A module's label universe (design Section 4) and, for a PlusCal module, how to tell whether
    a run's constants make a label exempt from the coverage gate.

    `owners[label]` is the set of process-block ids (a process's bound name, e.g. "own", "env")
    that own `label`, directly or by calling (transitively, through `procedure`s) the block it is
    in; a label absent from `owners` (or mapped to an empty set) is inside a procedure no process
    reaches, which is never exempt, so a dead procedure fails the per-run gate instead of passing it
    vacuously (design Section 4). `blocks[block_id]` is that process block's `\\in` set
    constant name, or None if it is declared `= VALUE` (always instantiated, so any label it owns is
    never exempt). Both dicts are empty, and nothing is ever exempt, for a non-PlusCal module."""
    pluscal: bool
    labels: frozenset[str]
    owners: dict[str, frozenset[str]]
    blocks: dict[str, str | None]

    def is_exempt(self, label: str, constants: dict[str, object]) -> bool:
        if not self.pluscal:
            return False
        owners = self.owners.get(label, frozenset())
        if not owners:  # a procedure no process calls: dead code the gate must catch, never exempt
            return False
        for block in owners:
            setname = self.blocks.get(block)
            if setname is None:  # a `= VALUE` process: always instantiated, never exempt
                return False
            value = constants.get(setname)
            if not (isinstance(value, frozenset) and len(value) == 0):
                return False
        return True


def _strip_line_comments(text: str) -> str:
    """Truncate each line of `text` at its first '\\*' (a TLA+ line comment); code is left intact."""
    return "\n".join(line.split("\\*", 1)[0] for line in text.split("\n"))


def _find_matching_close(text: str, open_pos: int) -> int:
    """Return the index just past the '*)' that matches the '(*' at open_pos (nesting-aware)."""
    depth, i, n = 0, open_pos, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        else:
            i += 1
    raise ExpectedError("the module's PlusCal algorithm comment is never closed with '*)'")


def _pcal_block(module_text: str) -> str | None:
    """Return the source of the module's PlusCal algorithm (the whole '(* --algorithm ... *)' or
    '(* --fair algorithm ... *)' comment, nesting-aware), or None if it has none."""
    match = _ALGORITHM_START.search(module_text)
    if match is None:
        return None
    return module_text[match.start(): _find_matching_close(module_text, match.start())]


def module_labels(module_text: str) -> LabelUniverse:
    """The label universe of a .tla module, and (for a PlusCal module) each label's owners."""
    block = _pcal_block(module_text)
    if block is None:
        labels = frozenset(m.group(1) for m in _TOPLEVEL_DEF.finditer(strip_tla_comments(module_text)))
        return LabelUniverse(False, labels, {}, {})

    text = _strip_line_comments(block)

    # (position, block id, kind, `\in` set name or None) for every process/procedure header, in
    # the order they appear; a block runs from its header to the next header or the block's end.
    headers: list[tuple[int, str, str, str | None]] = []
    for m in _PROCESS_HEADER.finditer(text):
        proc_name, op = m.group(1), m.group(2)
        if op == "\\in":
            setname_match = re.match(r"([A-Za-z_]\w*)\s*\)", text[m.end():])
            if setname_match is None:
                raise ExpectedError(f"process ({proc_name} \\in ...) must name a single identifier "
                                     "as its process set")
            headers.append((m.start(), proc_name, "process", setname_match.group(1)))
        else:
            headers.append((m.start(), proc_name, "process", None))
    for m in _PROCEDURE_HEADER.finditer(text):
        headers.append((m.start(), m.group(1), "procedure", None))
    headers.sort(key=lambda h: h[0])

    process_sets: dict[str, str | None] = {}
    block_kind: dict[str, str] = {}
    block_labels: dict[str, set[str]] = {}
    block_calls: dict[str, set[str]] = {}
    for idx, (pos, block_id, kind, setname) in enumerate(headers):
        end = headers[idx + 1][0] if idx + 1 < len(headers) else len(text)
        span = text[pos:end]
        block_kind[block_id] = kind
        if kind == "process":
            process_sets[block_id] = setname
        block_labels[block_id] = {match.group(1) for line in span.split("\n")
                                   for match in [_LABEL_LINE.match(line)] if match}
        block_calls[block_id] = {m.group(1) for m in _CALL.finditer(span)}

    # Forward reachability from each process block, over call edges through procedures: a label is
    # owned by every process block whose call graph reaches the block the label is defined in.
    owners: dict[str, set[str]] = {}
    for root, kind in block_kind.items():
        if kind != "process":
            continue
        seen: set[str] = set()
        stack = [root]
        while stack:
            current = stack.pop()
            if current in seen or current not in block_labels:
                continue
            seen.add(current)
            for label in block_labels[current]:
                owners.setdefault(label, set()).add(root)
            stack.extend(block_calls.get(current, ()))

    all_labels = frozenset(label for labels in block_labels.values() for label in labels)
    return LabelUniverse(True, all_labels, {k: frozenset(v) for k, v in owners.items()}, process_sets)


def _load_run(raw: dict, i: int, scenarios: list[str], base: Path) -> Run:
    where = f"run #{i + 1}"
    _require(set(raw) <= RUN_KEYS, f"{where}: unknown keys {sorted(set(raw) - RUN_KEYS)}")
    for key in ("name", "module", "config", "scenario", "kind"):
        _require(isinstance(raw.get(key), str) and raw[key], f"{where}: '{key}' must be a non-empty string")
    name, module, config, scenario, kind = (raw[k] for k in ("name", "module", "config", "scenario", "kind"))
    where = f"run {name!r}"

    _require(kind in KINDS, f"{where}: kind must be one of {KINDS}")
    _require(scenario in scenarios, f"{where}: scenario {scenario!r} is not in 'scenarios'")

    # violated: forbidden for check/liveness (reachability comes from coverage, a later task), required
    # (exactly one) for seeded/witness.
    if kind in ("check", "liveness"):
        _require("violated" not in raw, f"{where}: a {kind} run must not declare 'violated'")
        violated: tuple[str, ...] = ()
    else:
        _require("violated" in raw, f"{where}: a {kind} run needs 'violated'")
        violated = _str_list(raw["violated"], f"{where}: violated")
        _require(len(violated) == 1, f"{where}: a {kind} run names exactly one invariant or property")

    if kind == "seeded":
        suffix = r"-[A-Z][A-Z0-9_]*"
        suffix_help = ", plus '-<SEED_FLAG>' exactly when it is seeded"
    elif kind == "witness":
        suffix = "-" + re.escape(violated[0])
        suffix_help = ", plus '-<Invariant>' equal to violated[0] when it is a witness"
    else:
        suffix = ""
        suffix_help = ", plus '-<SEED_FLAG>' exactly when it is seeded"
    _require(re.fullmatch(rf"{re.escape(scenario)}-[a-z0-9]+(-[a-z0-9]+)*-{kind}{suffix}", name) is not None,
             f"{where}: name must be '<scenario>-<variant>-<kind>'{suffix_help}")
    _require(IDENT.fullmatch(module) is not None and (base / f"{module}.tla").is_file(),
             f"{where}: module {module}.tla not found beside expected.toml")
    _require(re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]*(/[A-Za-z0-9_][A-Za-z0-9_.-]*)*\.cfg", config) is not None
             and ".." not in config.split("/"),
             f"{where}: config must be a relative path inside the model directory, with '/' separators")
    cfg_path = base / config
    _require(cfg_path.resolve().is_relative_to(base.resolve()) and cfg_path.is_file(),
             f"{where}: config {config} not found")

    timeout = raw.get("timeout_minutes")
    _require(isinstance(timeout, int) and not isinstance(timeout, bool) and timeout >= 1,
             f"{where}: timeout_minutes must be a whole number of minutes, at least 1")

    findings: list[OpenFinding] = []
    _require(kind in ("check", "liveness") or "open_findings" not in raw,
             f"{where}: open_findings is only allowed for check and liveness runs")
    raw_findings = raw.get("open_findings", [])
    _require(isinstance(raw_findings, list), f"{where}: open_findings must be an array of tables")
    for f in raw_findings:
        _require(isinstance(f, dict) and set(f) == FINDING_KEYS,
                 f"{where}: each open finding has exactly name, tracking, fix_flag")
        _require(all(isinstance(f[k], str) and f[k] for k in FINDING_KEYS), f"{where}: open finding fields must be non-empty strings")
        _require(IDENT.fullmatch(f["name"]) is not None, f"{where}: open finding name must be a TLA+ identifier")
        _require(FIX_FLAG.fullmatch(f["fix_flag"]) is not None, f"{where}: fix_flag must look like FIX_NAME")
        _require(f["name"] not in violated, f"{where}: {f['name']} is both expected and an open finding")
        findings.append(OpenFinding(f["name"], f["tracking"], f["fix_flag"]))
    _require(len({f.name for f in findings}) == len(findings), f"{where}: duplicate open findings")

    _require(kind in ("check", "liveness") or "unreached" not in raw,
             f"{where}: unreached is only allowed for check and liveness runs")
    unreached = _load_label_reasons(raw.get("unreached", []), f"{where}: unreached")

    raw_tightened = raw.get("tightened")
    _require(kind == "liveness" or raw_tightened is None, f"{where}: tightened is only allowed for liveness runs")
    tightened: tuple[str, str] | None = None
    if raw_tightened is not None:
        _require(isinstance(raw_tightened, dict) and set(raw_tightened) == {"rung", "measurement"},
                 f"{where}: tightened must be a table with 'rung' and 'measurement'")
        rung, measurement = raw_tightened.get("rung"), raw_tightened.get("measurement")
        _require(isinstance(rung, str) and rung, f"{where}: tightened.rung must be a non-empty string")
        _require(isinstance(measurement, str) and measurement, f"{where}: tightened.measurement must be a non-empty string")
        tightened = (rung, measurement)

    declared_constants = _load_constants(raw, where)

    module_text = (base / f"{module}.tla").read_text(encoding="utf-8")
    universe = module_labels(module_text)
    for label, _reason in unreached:
        _require(label in universe.labels, f"{where}: unreached label {label!r} is not in {module}.tla's labels")
        _require(not universe.is_exempt(label, declared_constants),
                 f"{where}: unreached label {label!r} needs no entry: its actor does not run here")

    raw_symmetry = raw.get("symmetry")
    _require(kind != "liveness" or raw_symmetry is None, f"{where}: a liveness run must not declare symmetry")
    symmetry: tuple[str, str] | None = None
    if raw_symmetry is not None:
        _require(isinstance(raw_symmetry, dict) and set(raw_symmetry) == {"definition", "over"},
                 f"{where}: symmetry must be a table with 'definition' and 'over'")
        definition, over = raw_symmetry.get("definition"), raw_symmetry.get("over")
        _require(isinstance(definition, str) and IDENT.fullmatch(definition) is not None,
                 f"{where}: symmetry.definition must be a non-empty TLA+ identifier")
        _require(isinstance(over, str) and IDENT.fullmatch(over) is not None,
                 f"{where}: symmetry.over must be a non-empty TLA+ identifier")
        symmetry = (definition, over)

    text = cfg_path.read_text(encoding="utf-8")
    sections = cfg_sections(text)
    _require("CHECK_DEADLOCK" not in sections, f"{where}: the config must not set CHECK_DEADLOCK (deadlock checking stays on)")
    # A state or action constraint, or a VIEW, cuts or merges states while every constant still agrees with
    # expected.toml, so a .cfg could make a failing run pass through them (design Section 4). TYPE and
    # TYPE_CONSTRAINT are TLC 2.19 keywords too (its ModelConfig lists them) whose effect on the explored states
    # the runner cannot vouch for, so they are refused with the rest.
    for shrinking in ("CONSTRAINT", "ACTION_CONSTRAINT", "VIEW", "TYPE", "TYPE_CONSTRAINT"):
        _require(shrinking not in sections,
                 f"{where}: the config must not shrink the state space with {shrinking}; bound the run through its constants")
    _require(kind != "check" or "PROPERTY" not in sections,
             f"{where}: a check run's config must not declare a PROPERTY (TLC reports a temporal violation "
             "without naming it)")
    if kind == "witness":
        invariants = [t for t in sections.get("INVARIANT", []) if IDENT.fullmatch(t)]
        _require(invariants == [violated[0]],
                 f"{where}: a witness run's config lists exactly one invariant, {violated[0]!r}")
        _require("PROPERTY" not in sections, f"{where}: a witness run's config must not declare a PROPERTY")
    properties = cfg_properties(text)
    temporal_run = kind == "liveness" or (kind == "seeded" and violated[0] in properties)
    if temporal_run:
        _require(len(properties) == 1, f"{where}: a run that checks a temporal property lists exactly one PROPERTY "
                                       "(TLC does not name the property it reports violated)")
        _require("SYMMETRY" not in sections, f"{where}: symmetry is unsound with liveness checking")

    _require(("SYMMETRY" in sections) == (symmetry is not None),
             f"{where}: the config has a SYMMETRY section if and only if the run declares 'symmetry'")
    if symmetry is not None:
        definition, over = symmetry
        _require(sections["SYMMETRY"] == [definition],
                 f"{where}: the config's SYMMETRY must name exactly {definition!r}")
        def_pattern = re.compile(rf"\b{re.escape(definition)}\b\s*==\s*Permutations\s*\(\s*{re.escape(over)}\s*\)")
        _require(def_pattern.search(strip_tla_comments(module_text)) is not None,
                 f"{where}: {module}.tla must define {definition} == Permutations({over})")
        over_value = declared_constants.get(over)
        _require(isinstance(over_value, frozenset) and len(over_value) >= 2,
                 f"{where}: symmetry.over ({over}) must be a 'constants' entry that is a set of at least two elements")

    cfg_consts = cfg_constants(text)
    for cname, cvalue in cfg_consts.items():
        if FIX_FLAG.fullmatch(cname):
            continue
        _require(cname in declared_constants,
                 f"{where}: the config assigns {cname}, which is not declared in 'constants'")
        _require(_constants_equal(cvalue, declared_constants[cname]),
                 f"{where}: constants.{cname} does not match the config's {cname} = {cvalue!r}")
    for dname in declared_constants:
        _require(dname in cfg_consts, f"{where}: constants has {dname!r}, which the config does not assign")

    if findings:
        fixed_cfg_text(text, [f.fix_flag for f in findings])  # raises if a flag is missing

    constants = tuple(sorted(declared_constants.items()))
    return Run(name, module, config, scenario, kind, violated, tuple(findings), unreached, timeout,
               constants, symmetry, tightened)


# ---------------------------------------------------------------------------------------
# TLC output


_MESSAGE = re.compile(r"@!@!@STARTMSG (\d+):(\d+) @!@!@\n(.*?)@!@!@ENDMSG \1 @!@!@", re.S)
_INVARIANT_NAME = re.compile(r"Invariant (\w+) is violated")
_DISTINCT = re.compile(r"([\d,]+) distinct states? found")


def parse_messages(output: str) -> list[Message]:
    output = output.replace("\r\n", "\n")
    return [Message(int(c), int(s), t.strip()) for c, s, t in _MESSAGE.findall(output)]


def distinct_states(messages: list[Message]) -> int | None:
    for m in reversed(messages):
        found = _DISTINCT.search(m.text)
        if found:
            return int(found.group(1).replace(",", ""))
    return None


def interpret(exit_code: int, output: str, properties: list[str]) -> Outcome:
    """Turn TLC's exit status and -tool output into the set of violations it reported."""
    messages = parse_messages(output)
    states = distinct_states(messages)
    trace = tuple(m.text for m in messages if m.code == C_STATE)[:TRACE_STATES_SHOWN]

    def tooling(reason: str) -> Outcome:
        return Outcome(reason, frozenset(), states, trace)

    codes = {m.code for m in messages}
    if C_FINISHED not in codes:
        return tooling("TLC did not finish (no 'Finished' message)")
    errors = [m for m in messages if m.severity == SEVERITY_ERROR and m.code not in ALLOWED_ERROR_CODES]
    if errors:
        return tooling(f"TLC error {errors[0].code}: {errors[0].text.splitlines()[0] if errors[0].text else ''}")

    observed = set()
    for m in messages:
        if m.code in (C_INVARIANT, C_INVARIANT_INITIAL):
            name = _INVARIANT_NAME.search(m.text)
            if not name:
                return tooling(f"cannot read the invariant name in: {m.text[:80]}")
            observed.add(name.group(1))
    if C_DEADLOCK in codes:
        observed.add(DEADLOCK)
    if C_TEMPORAL in codes:
        if len(properties) != 1:
            return tooling(f"TLC reported a temporal violation but the config has {len(properties)} properties")
        observed.add(properties[0])

    agrees = {
        0: C_SUCCESS in codes and not codes & {C_DEADLOCK, C_TEMPORAL},
        11: C_DEADLOCK in codes,
        12: bool(codes & {C_INVARIANT, C_INVARIANT_INITIAL}),
        13: C_TEMPORAL in codes,
    }
    if not agrees.get(exit_code, False):
        return tooling(f"TLC exit status {exit_code} does not match its messages")
    return Outcome(None, frozenset(observed), states, trace)


_COVERAGE_ACTION_NAME = re.compile(r"^<([A-Za-z_]\w*)\b")
_COVERAGE_COUNTS = re.compile(r"(\d+):(\d+)\s*$")


def parse_coverage(messages: list[Message]) -> dict[str, tuple[int, int]] | None:
    """Parse the FINAL '-coverage 1' block (the one starting at the LAST 2201) in `messages` into
    {action name: (distinct, total)}, summing the counts of a name that appears twice in that
    block. '-coverage 1' prints a snapshot every minute and a final block; TLC ends a block with
    2202 ("End of statistics.") normally, but switches to 2777 (the same message, plus a note
    about the cost of leaving coverage/cost statistics on) once a run has gone on long enough - both
    end a block equally. Only the block starting at the LAST 2201 can be the whole run's final
    report, so this fails CLOSED: if that last 2201 is not followed by a 2202 or 2777 (the run was
    killed mid-write, or -coverage output was cut short), this returns None rather than falling
    back to an earlier complete block, because an earlier block is only a partial snapshot and
    judging coverage from it can pass a run wrongly (or fail one wrongly, for a label that finishes
    covered only late). Returns None when there is no 2201 at all, too."""
    last_start: int | None = None
    for i, m in enumerate(messages):
        if m.code == C_COVERAGE_START:
            last_start = i
    if last_start is None:
        return None
    # last_start is the LAST 2201 in `messages`, so nothing after it can be another 2201; scan
    # forward for its terminator only.
    last_block: list[Message] | None = None
    for i in range(last_start + 1, len(messages)):
        if messages[i].code in (C_COVERAGE_END, C_COVERAGE_END_LONG):
            last_block = messages[last_start: i + 1]
            break
    if last_block is None:
        return None

    result: dict[str, tuple[int, int]] = {}
    for m in last_block:
        if m.code != C_COVERAGE_ACTION:
            continue  # 2773 (Init), 2774 (a definition, no counts), 2221 (a cost sub-line): not labels
        name_match = _COVERAGE_ACTION_NAME.match(m.text)
        counts_match = _COVERAGE_COUNTS.search(m.text)
        if not name_match or not counts_match:
            continue
        name = name_match.group(1)
        distinct, total = int(counts_match.group(1)), int(counts_match.group(2))
        prev = result.get(name, (0, 0))
        result[name] = (prev[0] + distinct, prev[1] + total)
    return result


def judge_coverage(run: Run, universe: LabelUniverse, coverage: dict[str, tuple[int, int]]) -> list[str]:
    """The per-run coverage gate (design Section 4, "four rules"): failures for one check/liveness
    run that is not -fixed and finished without a tooling error or timeout (the caller decides
    whether the gate applies at all; this only judges `coverage` against `universe`). Empty means
    the gate passed."""
    unreached_labels = {label for label, _ in run.unreached}
    if universe.pluscal:
        gated = {label for label in universe.labels if not universe.is_exempt(label, dict(run.constants))}
    else:
        gated = {name for name in coverage if name in universe.labels}

    failures: list[str] = []
    for label in sorted(gated):
        if coverage.get(label, (0, 0))[1] == 0 and label not in unreached_labels:
            failures.append(f"{label}: gated label not covered (TOTAL 0)")
    for label in sorted(unreached_labels):
        if coverage.get(label, (0, 0))[1] > 0:
            failures.append(f"{label}: covered - remove it from unreached")
    return failures


def expected_set(run: Run, fixed: bool) -> frozenset[str]:
    names = set(run.violated)
    if not fixed:
        names |= {f.name for f in run.open_findings}
    return frozenset(names)


def judge(run: Run, outcome: Outcome, fixed: bool) -> str:
    if outcome.tooling_error is not None:
        return "tooling"
    return "ok" if outcome.observed == expected_set(run, fixed) else "mismatch"


def exit_code(results: list[Result]) -> int:
    """A mismatch outranks a tooling failure: 1 if any run mismatched, else 2 if any failed, else 0."""
    statuses = {r.status for r in results}
    if "mismatch" in statuses:
        return 1
    if "tooling" in statuses:
        return 2
    return 0


# ---------------------------------------------------------------------------------------
# tla2tools.jar


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def download(url: str, dest: Path) -> None:
    tmp = dest.with_suffix(".part")
    try:
        with urllib.request.urlopen(url, timeout=120) as response, tmp.open("wb") as out:
            shutil.copyfileobj(response, out)
        tmp.replace(dest)
    except OSError as err:
        raise ToolingError(f"cannot download {url} to {dest}: {err}") from err


def ensure_jar(target: Path = TARGET, fetch: Callable[[str, Path], None] = download,
               expected_sha: str = TLA_SHA256) -> Path:
    """Return a tla2tools.jar whose SHA-256 matches the pin, downloading at most twice.

    A download that fails, or that yields the wrong hash, uses up one of the two attempts."""
    target.mkdir(parents=True, exist_ok=True)
    jar = target / "tla2tools.jar"
    if jar.is_file() and sha256(jar) == expected_sha:
        return jar
    mismatch = f"tla2tools.jar {TLA_TAG} does not match its pinned SHA-256"
    failure = mismatch
    for _ in range(2):
        jar.unlink(missing_ok=True)
        try:
            fetch(TLA_URL, jar)
        except ToolingError as err:
            failure = str(err)
            continue
        got = sha256(jar) if jar.is_file() else "no file"
        if got == expected_sha:
            return jar
        failure = f"{mismatch} (expected {expected_sha}, got {got})"
    jar.unlink(missing_ok=True)
    raise ToolingError(f"{failure} (after two download attempts)")


# ---------------------------------------------------------------------------------------
# Running TLC


def tlc_command(jar: Path, run: Run, cfg: Path, metadir: Path, fixed: bool) -> list[str]:
    cmd = ["java", "-XX:+UseParallelGC", "-cp", str(jar), "tlc2.TLC", "-tool", "-workers", "auto",
           "-metadir", str(metadir), "-config", str(cfg)]
    if run.kind in ("check", "liveness"):
        cmd.append("-continue")
    if not fixed:
        # Every non-fixed run carries coverage: the per-run gate needs it for check/liveness, and
        # the suite-wide union needs it for every kind (design Section 4).
        cmd.extend(["-coverage", "1"])
    cmd.append(run.module)
    return cmd


def execute(run: Run, jar: Path, base: Path, fixed: bool) -> Result:
    name = f"{run.name}-fixed" if fixed else run.name
    cfg = base / run.config
    text = cfg.read_text(encoding="utf-8")
    if fixed:
        text = fixed_cfg_text(text, [f.fix_flag for f in run.open_findings])
        cfg = TARGET / "cfg" / f"{name}.cfg"
        cfg.parent.mkdir(parents=True, exist_ok=True)
        cfg.write_text(text, encoding="utf-8")
    metadir = TARGET / "states" / name
    shutil.rmtree(metadir, ignore_errors=True)
    log = TARGET / "out" / f"{name}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    expected = expected_set(run, fixed)

    start = time.monotonic()
    with log.open("w", encoding="utf-8") as out:
        proc = subprocess.Popen(tlc_command(jar, run, cfg, metadir, fixed), cwd=base, stdout=out,
                                stderr=subprocess.STDOUT)
        try:
            code = proc.wait(timeout=run.timeout_minutes * 60)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            code = None
        except BaseException:  # KeyboardInterrupt: never leave TLC running
            proc.kill()
            proc.wait()
            raise
    seconds = time.monotonic() - start
    output = log.read_text(encoding="utf-8", errors="replace")

    if code is None:
        states = distinct_states(parse_messages(output))
        return Result(name, "tooling", expected, frozenset(), states, seconds,
                      f"TIMEOUT after {run.timeout_minutes} min", (), log)
    outcome = interpret(code, output, cfg_properties(text))
    status = judge(run, outcome, fixed)
    detail = outcome.tooling_error or ""

    # The per-run coverage gate (design Section 4): check/liveness only, not -fixed, and only when
    # the run finished without a tooling error (a timed-out run never reaches this point at all).
    if run.kind in ("check", "liveness") and not fixed and outcome.tooling_error is None:
        coverage = parse_coverage(parse_messages(output))
        if coverage is None:
            status = "tooling"
            detail = "no coverage report"
        else:
            universe = module_labels((base / f"{run.module}.tla").read_text(encoding="utf-8"))
            failures = judge_coverage(run, universe, coverage)
            if failures:
                status = "mismatch"
                detail = "; ".join(f for f in [detail, "; ".join(failures)] if f)

    return Result(name, status, expected, outcome.observed, outcome.distinct_states, seconds,
                  detail, outcome.trace, log)


def report(result: Result, tightened: tuple[str, str] | None = None) -> None:
    def names(s: frozenset[str]) -> str:
        return ",".join(sorted(s)) or "-"

    states = "?" if result.distinct_states is None else f"{result.distinct_states:,}"
    print(f"{result.status.upper():8} {result.name}  expected={names(result.expected)}  "
          f"observed={names(result.observed)}  states={states}  {result.seconds:.0f}s")
    if tightened is not None:
        rung, measurement = tightened
        print(f"         tightened: {rung} ({measurement})")
    if result.status != "ok":
        if result.detail:
            print(f"         {result.detail}")
        for state in result.trace:
            print("         " + state.replace("\n", "\n         "))
        if result.log is not None:
            print(f"         full TLC output: {result.log}")


def judge_union(executed: list[tuple[Run, bool, Result]], base: Path,
                 never_reached: tuple[tuple[str, str], ...],
                 deferred: tuple[tuple[str, str, str], ...]) -> bool:
    """The suite-wide coverage union (design Section 4), judged only when every run in
    expected.toml was selected (no --scenario). `executed` is every (run, fixed, result) this
    invocation ran. A label of any run's module is covered if ANY run of that module - any
    scenario, any kind, not -fixed - reports it with TOTAL > 0 in its last coverage block; whatever
    is not covered that way must be listed in `never_reached` or `deferred`, and a listed label
    that IS covered that way fails too. Prints the one-line report and returns whether the union
    failed (which counts like a run mismatch in the exit code)."""
    if any(result.status == "tooling" for _run, _fixed, result in executed):
        print("run.py: suite-wide coverage not judged: a run failed or timed out")
        return False

    never_reached_labels = {label for label, _ in never_reached}
    deferred_labels = {label for label, _scenario, _reason in deferred}
    universes: dict[str, LabelUniverse] = {}
    covered: dict[str, set[str]] = {}
    reported: dict[str, set[str]] = {}
    for run, fixed, result in executed:
        if fixed:
            continue
        if run.module not in universes:
            universes[run.module] = module_labels((base / f"{run.module}.tla").read_text(encoding="utf-8"))
        assert result.log is not None, "a non-tooling result always has a log"
        coverage = parse_coverage(parse_messages(result.log.read_text(encoding="utf-8", errors="replace"))) or {}
        reported.setdefault(run.module, set()).update(coverage)
        covered.setdefault(run.module, set()).update(name for name, (_d, total) in coverage.items() if total > 0)

    all_covered: set[str] = set().union(*covered.values()) if covered else set()
    uncovered: set[str] = set()
    covered_in_universe: set[str] = set()
    for module, universe in universes.items():
        gated = universe.labels if universe.pluscal else (universe.labels & reported.get(module, set()))
        module_covered = covered.get(module, set())
        covered_in_universe |= gated & module_covered
        uncovered |= ({label for label in gated if label not in module_covered}
                      - never_reached_labels - deferred_labels)
    wrongly_covered = never_reached_labels & all_covered
    wrongly_covered_deferred = deferred_labels & all_covered

    if uncovered or wrongly_covered or wrongly_covered_deferred:
        print(f"MISMATCH suite coverage  uncovered: {','.join(sorted(uncovered)) or '-'}; "
              f"never_reached but covered: {','.join(sorted(wrongly_covered)) or '-'}; "
              f"deferred but covered: {','.join(sorted(wrongly_covered_deferred)) or '-'}")
        return True
    print(f"COVERAGE suite  {len(covered_in_universe)} labels covered, {len(never_reached_labels)} never_reached, "
          f"{len(deferred_labels)} deferred")
    return False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run the lock-protocol model check.")
    parser.add_argument("--expected", type=Path, default=HERE / "expected.toml")
    parser.add_argument("--scenario", help="run only this scenario")
    parser.add_argument("--platform", help="with --scenario, run only this platform")
    parser.add_argument("--list-scenarios", action="store_true", help="print the scenario names as JSON")
    parser.add_argument("--list-jobs", action="store_true",
                         help="print the distinct {scenario, platform} pairs as JSON")
    args = parser.parse_args(argv)

    if args.platform is not None and args.scenario is None:
        print("run.py: --platform requires --scenario", file=sys.stderr)
        return 2

    try:
        expected = load_expected(args.expected)
    except ExpectedError as err:
        print(f"run.py: {err}", file=sys.stderr)
        return 2
    scenarios = expected.scenarios
    if args.list_scenarios:
        print(json.dumps(scenarios))
        return 0
    if args.list_jobs:
        jobs: list[dict[str, str]] = []
        for s in scenarios:
            platforms: list[str] = []
            for r in expected.runs:
                if r.scenario != s:
                    continue
                platform = r.name[len(s) + 1:].split("-", 1)[0]
                if platform not in platforms:
                    platforms.append(platform)
            jobs.extend({"scenario": s, "platform": p} for p in platforms)
        print(json.dumps(jobs))
        return 0
    if args.scenario is not None and args.scenario not in scenarios:
        print(f"run.py: unknown scenario {args.scenario!r}; known: {', '.join(scenarios)}", file=sys.stderr)
        return 2
    selected = [r for r in expected.runs if args.scenario is None or r.scenario == args.scenario]
    if args.platform is not None:
        selected = [r for r in selected if r.name.startswith(f"{args.scenario}-{args.platform}-")]
        if not selected:
            print(f"run.py: no runs for scenario {args.scenario} on platform {args.platform}", file=sys.stderr)
            return 2

    if shutil.which("java") is None:
        print("run.py: java is not on PATH (TLC needs Java 11 or later; CI uses Temurin 21)", file=sys.stderr)
        return 2
    try:
        jar = ensure_jar()
    except (ToolingError, OSError) as err:
        print(f"run.py: {err}", file=sys.stderr)
        return 2

    base = args.expected.resolve().parent
    results: list[Result] = []
    executed: list[tuple[Run, bool, Result]] = []
    try:
        for run in selected:
            for fixed in (False, True) if run.open_findings else (False,):
                try:
                    result = execute(run, jar, base, fixed)
                except (OSError, ExpectedError) as err:
                    result = Result(run.name, "tooling", frozenset(), frozenset(), None, 0.0, str(err), (), None)
                report(result, run.tightened)
                results.append(result)
                executed.append((run, fixed, result))
    except KeyboardInterrupt:
        print(f"run.py: interrupted after {len(results)} runs", file=sys.stderr)
        return 2
    code = exit_code(results)

    if args.scenario is not None:
        print("run.py: suite-wide coverage not judged for a single scenario")
    elif judge_union(executed, base, expected.never_reached, expected.deferred):
        code = 1  # a union failure counts like a run mismatch: it outranks a tooling failure too

    print(f"run.py: {len(results)} runs, exit {code}")
    return code


if __name__ == "__main__":
    sys.exit(main())
