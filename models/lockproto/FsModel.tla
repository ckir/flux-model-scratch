---- MODULE FsModel ----
\* The abstract filesystem both protocol models run on (design Section 5 of
\* docs/superpowers/specs/2026-09-11-lock-protocol-model-check-design.md).
\*
\* The whole filesystem is ONE record, `fs`, and this module is pure operators over it: each
\* operation takes an `fs` and returns a result record, so the protocol models declare the variable
\* and this module decides what every call does. Nothing here is nondeterministic: a call whose real
\* behaviour the platform may choose (a weak identity read, a Windows unlink, a directory listing)
\* takes the choice as an argument, and the caller picks it with a PlusCal `with`, so TLC explores
\* every outcome and the operators stay functions.
\*
\* Each operator is one atomic step (design Section 5.2): a protocol step that makes two calls is
\* two labels, and other actors run in between.
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Dirs,             \* the directories the scenario uses
    Names,            \* every entry name that can exist in them
    Procs,            \* the processes (actors) of the scenario
    NoProc,           \* a model value that is not a process: "nobody holds this"
    MaxObjs,          \* how many objects a run may create; bounds the state space
    Fold,             \* [Names -> Classes]: names the filesystem treats as one entry fold together
    Platform,         \* "posix" or "windows"
    IdentityStrength, \* "strong" or "weak" (Section 5.1)
    LockCapability    \* "strong" or "weak" (Section 235.1); "weak" has no OS-native lock

ASSUME Platform \in {"posix", "windows"}
ASSUME IdentityStrength \in {"strong", "weak"}
ASSUME LockCapability \in {"strong", "remote", "weak"}
ASSUME MaxObjs \in Nat \ {0}
ASSUME NoProc \notin Procs
ASSUME DOMAIN Fold = Names

Windows == Platform = "windows"
Posix == Platform = "posix"

\* ------------------------------------------------------------------------------------------
\* Values

Objs == 1..MaxObjs          \* object ids, never reused; ids are handed out in order
NoObj == 0                  \* "this name has no entry"

\* Every content value is a tagged record, so that no comparison mixes a record with a string or
\* a number: TLC refuses those, and the protocol compares contents it has not inspected.
Kinds == {"operation", "cleanup"}
Rec(p, k) == [tag |-> "record", op |-> p, kind |-> k]
Records == {Rec(p, k) : p \in Procs, k \in Kinds}
Torn == [tag |-> "torn"]            \* a record write interrupted between its two steps
Foreign == [tag |-> "foreign"]      \* an object at a lock path that is not a Flux lock record
EmptyFile == [tag |-> "empty"]      \* created, nothing written yet
NoContent == [tag |-> "none"]       \* the object id is not allocated
Contents == Records \cup {Torn, Foreign, EmptyFile}
IsRecord(c) == c.tag = "record"

Classes == {Fold[n] : n \in Names}
ClassOf(n) == Fold[n]

\* An in-flight call (Section 5.2): issued by a process, lands or is dropped later.
InFlight == [proc: Procs, obj: Objs, content: Contents]

\* ------------------------------------------------------------------------------------------
\* The filesystem state

FsType ==
    [ entries: [Dirs -> [Classes -> Objs \cup {NoObj}]],   \* what a name class maps to now
      dentries: [Dirs -> [Classes -> Objs \cup {NoObj}]],  \* what survives a host crash
      content: [Objs -> Contents \cup {NoContent}],
      durable: [Objs -> Contents \cup {NoContent}],
      handles: SUBSET [proc: Procs, obj: Objs, del: BOOLEAN],
      oslock: [Objs -> Procs \cup {NoProc}],
      inflight: SUBSET InFlight,
      past: [Dirs -> [Classes -> SUBSET Objs]],            \* ids a class has held (weak identity)
      deleted: SUBSET Objs,                                \* Windows: name gone when last handle closes
      next: 0..MaxObjs ]                                   \* how many objects are allocated

FsInit ==
    [ entries |-> [d \in Dirs |-> [c \in Classes |-> NoObj]],
      dentries |-> [d \in Dirs |-> [c \in Classes |-> NoObj]],
      content |-> [o \in Objs |-> NoContent],
      durable |-> [o \in Objs |-> NoContent],
      handles |-> {},
      oslock |-> [o \in Objs |-> NoProc],
      inflight |-> {},
      past |-> [d \in Dirs |-> [c \in Classes |-> {}]],
      deleted |-> {},
      next |-> 0 ]

\* An initial state that already holds one object with given content at one name, for a scenario
\* that starts from a lock another invocation left behind.
FsWith(d, n, c) ==
    LET o == 1 IN
    [ FsInit EXCEPT
        !.entries[d][ClassOf(n)] = o,
        !.dentries[d][ClassOf(n)] = o,
        !.content[o] = c,
        !.durable[o] = c,
        !.next = 1 ]

\* ------------------------------------------------------------------------------------------
\* Reading the state (no step of its own; used by the operators and by the properties)

At(fs, d, n) == fs.entries[d][ClassOf(n)]
Exists(fs, d, n) == At(fs, d, n) # NoObj
ContentAt(fs, d, n) == IF Exists(fs, d, n) THEN fs.content[At(fs, d, n)] ELSE NoContent
HandlesOf(fs, o) == {h \in fs.handles : h.obj = o}
OpenBy(fs, p, o) == \E h \in fs.handles : h.proc = p /\ h.obj = o
HoldsLock(fs, p, o) == fs.oslock[o] = p
Allocated(fs) == {o \in Objs : fs.content[o] # NoContent}

\* Windows refuses to rename or delete an object any handle holds without delete sharing
\* (design Section 5.1; probe FS-6). POSIX allows it (FS-4, FS-5).
DeleteAllowed(fs, o) == Posix \/ \A h \in HandlesOf(fs, o) : h.del

\* A failed call and a successful one. `val` carries what the call reports. A failed call returns the
\* filesystem UNCHANGED, which is both what a failed call does and what lets a caller that ignores
\* the failure - as 240.3 step 5 does, where Flux warns and continues - write `...fs` safely.
Fail(fs) == [ok |-> FALSE, fs |-> fs, val |-> NoObj]
Ok(newFs, v) == [ok |-> TRUE, fs |-> newFs, val |-> v]
Succeeded(r) == r.ok

\* ------------------------------------------------------------------------------------------
\* Operations (design Section 5.1: one row, one atomic step). Every operator that takes an object id
\* treats NoObj as a failed call: the protocol reads an id out of the state (`At(fs, ...)`), and a
\* concurrent actor may have removed the name in between, so the id can be NoObj at any call site.

\* Exclusive create. Fails if an entry of the same class exists; otherwise creates an empty object
\* and a handle for the caller. `del` is the Windows delete-sharing mode of that handle.
FsCreate(fs, d, n, p, del) ==
    IF Exists(fs, d, n) \/ fs.next = MaxObjs THEN Fail(fs)
    ELSE LET o == fs.next + 1
             share == IF Posix THEN TRUE ELSE del IN
         Ok([ fs EXCEPT
                !.entries[d][ClassOf(n)] = o,
                !.content[o] = EmptyFile,
                !.past[d][ClassOf(n)] = IF IdentityStrength = "weak" THEN @ \cup {o} ELSE @,
                !.handles = @ \cup {[proc |-> p, obj |-> o, del |-> share]},
                !.next = o ], o)

\* Open an existing name without creating. Fails if absent, or (Windows) if the object has a
\* pending delete. A process never opens a name it already has open in these models; the protocol
\* keeps one handle per object per process, and `NoDoubleOpen` below checks that.
FsOpen(fs, d, n, p, del) ==
    LET o == At(fs, d, n) IN
    IF o = NoObj \/ (Windows /\ o \in fs.deleted) THEN Fail(fs)
    ELSE LET share == IF Posix THEN TRUE ELSE del IN
         Ok([fs EXCEPT !.handles = @ \cup {[proc |-> p, obj |-> o, del |-> share]}], o)

\* Close one handle: drops it, releases its OS-native lock, and on Windows removes a pending-delete
\* object's name when its last handle goes.
FsClose(fs, p, o) ==
    IF o = NoObj \/ ~OpenBy(fs, p, o) THEN Fail(fs) ELSE
    LET rest == fs.handles \ {h \in fs.handles : h.proc = p /\ h.obj = o}
        lock == IF fs.oslock[o] = p THEN NoProc ELSE fs.oslock[o]
        gone == Windows /\ o \in fs.deleted /\ {h \in rest : h.obj = o} = {}
        names == {<<d, c>> \in Dirs \X Classes : fs.entries[d][c] = o}
    IN Ok([ fs EXCEPT
              !.handles = rest,
              !.oslock[o] = lock,
              !.entries = IF gone
                          THEN [d \in Dirs |-> [c \in Classes |->
                                  IF <<d, c>> \in names THEN NoObj ELSE fs.entries[d][c]]]
                          ELSE fs.entries,
              !.deleted = IF gone THEN @ \ {o} ELSE @ ], o)

\* The OS-native lock, scoped to the handle that takes it (probe FS-11) and unavailable when the
\* capability is weak (Section 235.1).
FsTryLock(fs, p, o) ==
    IF o = NoObj \/ LockCapability = "weak" \/ ~OpenBy(fs, p, o) \/ fs.oslock[o] # NoProc THEN Fail(fs)
    ELSE Ok([fs EXCEPT !.oslock[o] = p], o)

\* A remote lock's lease lapses (design Section 5.1): the lock is gone, the holder keeps its handle and
\* is not told.
FsLeaseExpiry(fs, o) ==
    IF o = NoObj \/ fs.oslock[o] = NoProc THEN Fail(fs) ELSE Ok([fs EXCEPT !.oslock[o] = NoProc], o)

FsUnlock(fs, p, o) ==
    IF o = NoObj \/ fs.oslock[o] # p THEN Fail(fs) ELSE Ok([fs EXCEPT !.oslock[o] = NoProc], o)

\* Rename without replacing: fails if the target class exists. On POSIX it succeeds even while the
\* object is open and OS-locked (FS-4); on Windows every open handle must allow delete sharing
\* (FS-6, FS-7).
FsRenameNoReplace(fs, d, from, to) ==
    LET o == At(fs, d, from) IN
    IF o = NoObj \/ Exists(fs, d, to) \/ ~DeleteAllowed(fs, o) THEN Fail(fs)
    ELSE Ok([ fs EXCEPT
                !.entries[d][ClassOf(from)] = NoObj,
                !.entries[d][ClassOf(to)] = o,
                !.past[d][ClassOf(to)] =
                    IF IdentityStrength = "weak" THEN @ \cup {o} ELSE @ ], o)

\* Rename, replacing (design Section 5.1): atomically points the target at the source object whether or
\* not the target existed; the replaced object keeps its open handles and loses its name. Windows needs
\* delete sharing on every handle of both objects.
FsRenameReplace(fs, d, from, to) ==
    LET o == At(fs, d, from)
        old == At(fs, d, to) IN
    IF o = NoObj \/ ~DeleteAllowed(fs, o) \/ (old # NoObj /\ ~DeleteAllowed(fs, old)) THEN Fail(fs)
    ELSE Ok([ fs EXCEPT
                !.entries[d][ClassOf(from)] = NoObj,
                !.entries[d][ClassOf(to)] = o,
                !.past[d][ClassOf(to)] =
                    IF IdentityStrength = "weak" THEN @ \cup {o} ELSE @ ], o)

\* Unlink. POSIX always succeeds and the open handles keep the now-unnamed object (FS-5). Windows
\* needs delete sharing on every handle, and then either removes the name at once or leaves it as a
\* pending delete until the last handle closes: `atOnce` is that choice (FS-7).
FsUnlinkChoices == IF Windows THEN {TRUE, FALSE} ELSE {TRUE}
FsUnlink(fs, d, n, atOnce) ==
    LET o == At(fs, d, n) IN
    IF o = NoObj \/ ~DeleteAllowed(fs, o) THEN Fail(fs)
    ELSE IF atOnce \/ HandlesOf(fs, o) = {}
    THEN Ok([fs EXCEPT !.entries[d][ClassOf(n)] = NoObj], o)
    ELSE Ok([fs EXCEPT !.deleted = @ \cup {o}], o)

\* Writing a lock record is two steps, so a reader in between sees Torn (Section 259.6).
FsWriteBegin(fs, o) ==
    IF o = NoObj \/ fs.content[o] = NoContent THEN Fail(fs) ELSE Ok([fs EXCEPT !.content[o] = Torn], o)

FsWriteEnd(fs, o, c) ==
    IF o = NoObj \/ fs.content[o] = NoContent THEN Fail(fs) ELSE Ok([fs EXCEPT !.content[o] = c], o)

\* A data write an operation issues while publishing: it lands at completion, so a stalled owner's
\* call can complete after a takeover (Section 5.2, Section 240.5).
FsIssue(fs, p, o, c) ==
    IF o = NoObj \/ fs.content[o] = NoContent THEN Fail(fs)
    ELSE Ok([fs EXCEPT !.inflight = @ \cup {[proc |-> p, obj |-> o, content |-> c]}], o)

FsLand(fs, call) ==
    IF call \notin fs.inflight THEN Fail(fs)
    ELSE Ok([ fs EXCEPT
                !.content[call.obj] = call.content,
                !.inflight = @ \ {call} ], call.obj)

FsDrop(fs, call) ==
    IF call \notin fs.inflight THEN Fail(fs) ELSE Ok([fs EXCEPT !.inflight = @ \ {call}], call.obj)

FsFlushFile(fs, o) ==
    IF o = NoObj \/ fs.content[o] = NoContent THEN Fail(fs) ELSE Ok([fs EXCEPT !.durable[o] = fs.content[o]], o)

FsFlushDir(fs, d) == Ok([fs EXCEPT !.dentries[d] = fs.entries[d]], d)

\* Looking a name up reports whether it has an entry, without opening a handle.
FsLookup(fs, d, n) == Exists(fs, d, n)

\* The identity a name reports. Under strong identity it is the object the name maps to; under weak
\* identity it may be any id the name has held (Section 5.1, Section 99.1), so a caller cannot tell
\* a replaced object from the original.
FsIdentityChoices(fs, d, n) ==
    LET o == At(fs, d, n) IN
    IF o = NoObj THEN {NoObj}
    ELSE IF IdentityStrength = "strong" THEN {o}
    ELSE {o} \cup fs.past[d][ClassOf(n)]
\* A directory listing is not atomic (Section 5.1): the caller takes the names in any order and
\* reads each at the moment it gets there, so an entry that exists throughout is always returned and
\* one created or removed during the listing may or may not be. The protocol models list with a
\* PlusCal loop over Names; this operator is the per-name read.
FsListStep(fs, d, n) == Exists(fs, d, n)

\* ------------------------------------------------------------------------------------------
\* Crashes (design Section 5.2)

\* Closing every handle a process holds: the handles, their sharing restrictions and its OS-native
\* locks go, and on Windows a pending-delete object whose last handle this was loses its name. A
\* process that stops after a failed Section 99 check does this, and so does a process crash.
FsCloseAll(fs, p) ==
    LET mine == {h \in fs.handles : h.proc = p}
        gone == {h.obj : h \in mine}
        last(o) == {h \in fs.handles \ mine : h.obj = o} = {}
        names == {<<d, c>> \in Dirs \X Classes :
                    /\ fs.entries[d][c] \in (fs.deleted \cap gone)
                    /\ last(fs.entries[d][c])}
    IN [ fs EXCEPT
           !.handles = @ \ mine,
           !.oslock = [o \in Objs |-> IF fs.oslock[o] = p THEN NoProc ELSE fs.oslock[o]],
           !.entries = [d \in Dirs |-> [c \in Classes |->
                          IF <<d, c>> \in names THEN NoObj ELSE fs.entries[d][c]]],
           !.deleted = @ \ {o \in fs.deleted : o \in gone /\ last(o)} ]

\* A process crash closes everything the process holds; content stays as it is, so an interrupted
\* record write stays Torn. The protocol resolves its in-flight calls in the same step (design
\* Section 5.2), with `FsLand` and `FsDrop`.
FsProcCrash(fs, p) == FsCloseAll(fs, p)

\* A host crash. Every object written since its last flush takes one of: its old durable content,
\* its latest content, or Torn, chosen per object (`pick`). Entry operations since the last
\* directory flush are kept as a prefix, in order, and the rest are lost; `keep` says how many of
\* the journalled operations survive, and the model represents the prefix by choosing, per
\* directory, either the current entries or the durable ones, which is the one-operation case, or
\* an intermediate state the protocol reached. `HostCrashPicks` and `HostCrashDirs` are the choice
\* sets a caller iterates.
\* Only an object WRITTEN since its last flush (design Section 5.2). A file created and never written
\* still holds EmptyFile, which only creation sets, and a host crash cannot tear what was never written.
Unflushed(fs) == {o \in Objs : fs.content[o] \notin {NoContent, EmptyFile} /\ fs.durable[o] # fs.content[o]}
HostCrashPicks(fs) == [Unflushed(fs) -> {"old", "new", "torn"}]
HostCrashDirs == [Dirs -> {"kept", "lost"}]

FsHostCrash(fs, pick, dirs) ==
    LET newContent(o) ==
            IF fs.content[o] = NoContent THEN NoContent
            ELSE IF o \notin Unflushed(fs) THEN fs.content[o]
            ELSE CASE pick[o] = "old" -> IF fs.durable[o] = NoContent THEN EmptyFile ELSE fs.durable[o]
                   [] pick[o] = "new" -> fs.content[o]
                   [] OTHER -> Torn
        ents(d) == IF dirs[d] = "kept" THEN fs.entries[d] ELSE fs.dentries[d]
    IN [ fs EXCEPT
           !.content = [o \in Objs |-> newContent(o)],
           !.durable = [o \in Objs |-> newContent(o)],
           !.entries = [d \in Dirs |-> ents(d)],
           !.dentries = [d \in Dirs |-> ents(d)],
           !.handles = {},
           !.oslock = [o \in Objs |-> NoProc],
           !.inflight = {},
           !.deleted = {} ]

\* ------------------------------------------------------------------------------------------
\* What the model assumes about itself; the protocol models check these as invariants, so a
\* simplification made here cannot pass unnoticed.

\* One handle per process per object (see FsOpen).
NoDoubleOpen(fs) ==
    \A p \in Procs, o \in Objs :
        Cardinality({h \in fs.handles : h.proc = p /\ h.obj = o}) <= 1

\* An OS-native lock is only ever held by a process that has the object open (probe FS-9, FS-11).
LockImpliesHandle(fs) ==
    \A o \in Objs : fs.oslock[o] # NoProc => OpenBy(fs, fs.oslock[o], o)

\* Ids are never reused: a name's past ids are allocated, and an allocated id keeps its content
\* slot for the whole run.
IdsNotReused(fs) ==
    /\ \A d \in Dirs, c \in Classes : fs.past[d][c] \subseteq 1..fs.next
    /\ \A d \in Dirs, c \in Classes : fs.entries[d][c] \in (1..fs.next) \cup {NoObj}

FsInvariants(fs) == NoDoubleOpen(fs) /\ LockImpliesHandle(fs) /\ IdsNotReused(fs)
====
