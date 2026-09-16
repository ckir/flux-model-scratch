# flux-model-scratch

Throwaway repository. It exists to run one TLA+ experiment quickly on GitHub Actions, because the real
repository's model workflow is a gate and cannot be dispatched from a branch. Nothing here is a product,
and nothing here is the specification.

The real work lives in [ckir/flux](https://github.com/ckir/flux): `models/lockproto/`, the design note at
`docs/superpowers/specs/2026-09-11-lock-protocol-model-check-design.md`, and the spec itself.

## What is being measured

`Fenced.tla` is a **variant** of the lock protocol, built to test one claim: that the protocol's guarantees
should rest on the last atomic operation rather than on a check made earlier. It differs from the modelled
protocol in three ways:

- **Ownership is the open file.** "Still owned" means the lock path still names the very file this process
  holds open, tested by identity. No record comparison, and no OS-native lock: a record is descriptive, and
  a lease can lapse without the holder being told.
- **A takeover creates a new file** and renames it over the lock, instead of overwriting the lock in place.
- **Publication is one rename.** The output is written to a private file, renamed over the destination in a
  single step, and the operation re-checks its ownership before reporting success.

It also models two filesystem behaviours the main model does not:

- a lock lost to an expired lease is not reclaimed on Linux NFSv4, and writes through that descriptor then
  fail with `EIO` until it is closed;
- an NFS `REMOVE` carries a name, resolved when the server runs the call, so a stale unlink removes whatever
  holds the name at that moment.

## The properties

The destination is modelled here, which the main model does not do, so the properties can say what the
protocol is for rather than using a proxy:

- `TargetComplete` — the destination always holds one operation's complete output: never a mixture, never a
  file caught between the halves of a write.
- `PublishedIsOwn` — an operation that re-checked its ownership after publishing, and still owned the lock,
  was not overwritten.
- `SingleWriter` — the main model's proxy property, measured here as a witness that is **expected to fail**.
  The claim under test is that two operations can be inside a publishing step while the destination stays
  correct.

## Running it

```bash
python models/lockproto/run.py --expected models/lockproto/expected-fenced.toml --scenario fenced --platform posix
```

`run.py` downloads a pinned `tla2tools.jar` and checks its hash. Every push runs the same command in CI.
