---- MODULE LockProtocol ----
\* The V16 lock protocol: acquisition (96.1), classification and recovery (240.1 to 240.3), a takeover
\* (240.5), a plain rerun's and a restart's decisions (21.1), cleanup (251.1), and commit-time revalidation (99), on the abstract
\* filesystem of FsModel.tla. Design: docs/superpowers/specs/2026-09-11-lock-protocol-model-check-design.md,
\* Sections 6.1, 7 and 12. Each label is named after the spec step it implements, and each performs
\* at most one filesystem operation, so other actors run in between (design Section 5.2).
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Owners,        \* operations that acquire the lock and publish
    Recoverers,    \* new invocations that recover a dead owner's lock (240.3)
    PlainRuns,     \* new invocations with no flags (21.1)
    Cleanups,      \* flux cleanup DEST (251.1)
    Breakers,      \* flux copy --restart --break-lock (240.5, 21.1)
    NoProc,        \* model value: nobody
    P,             \* the target's parent directory
    LockName,      \* P/<name>.flux-lock (96.1)
    DirLockName,   \* P/.flux-dir.lock, the long-name fallback (96.1); never created here
    MaxObjs,       \* how many objects this scenario's actors can create (bounds the state space)
    MaxCrashes,    \* how many crashes a run may have, both kinds together (design Section 5.2)
    HostCrashes,   \* whether a host crash is one of the crashes this run explores
    MaxLeaseExpiries, \* how many remote lock leases may lapse under a live holder (design Section 5.1)
    Platform, IdentityStrength, LockCapability,
    SEED_RECOVER_FOREIGN,    \* seeded defects (design Section 8); FALSE outside their seeded runs
    SEED_RECOVER_UNCERTAIN,
    SEED_DEAD_AS_BUSY,
    SEED_RECOVER_UNCERTAIN_CLEANUP_LOCK,
    SEED_ACQUIRER_UNLINKS_BY_NAME,
    SEED_RESTART_RELEASES,
    SEED_MOVE_ASIDE_FOR_UNCERTAIN,
    SEED_RENAME_OVER_TAKEOVER,
    SEED_NO_CAPABILITY_GATE,
    SEED_TORN_AS_FOREIGN,
    LEASE_FENCES_WRITES,  \* does a lost lease fence writes through that descriptor? Linux NFSv4: yes (EIO).
                          \* SMB3 with a still-valid handle, or Linux with recover_lost_locks=1: no.
    FIX_REMOTE_LEASE_SPEC  \* fix flag of the open finding on SingleWriter: the remote-lease spec amendments (design Section 11)

Procs == Owners \cup Recoverers \cup PlainRuns \cup Cleanups \cup Breakers
\* <lock-name>.broken.<operation-id> beside the lock (240.3 step 2). Only an actor that can move a
\* lock aside needs such a name, and every name is an entry class in every state, so the Owners do
\* not get one. The target's own name is not here either: publishing sets a ghost in this scenario
\* (the `nested` scenario, which is about what gets written where, creates the object).
Movers == Recoverers \cup PlainRuns \cup Cleanups \cup Breakers
BrokenOf(p) == <<"broken", p>>
\* The private name SEED_RENAME_OVER_TAKEOVER's takeover builds its record under, before renaming it
\* over the lock (design Section 8); only Breakers have one.
TakeoverName(p) == <<"takeover", p>>
Names == {LockName, DirLockName} \cup {BrokenOf(p) : p \in Movers} \cup {TakeoverName(p) : p \in Breakers}
Dirs == {P}
Fold == [n \in Names |-> n]          \* the recovery scenario needs no name folding

INSTANCE FsModel WITH Dirs <- Dirs, Names <- Names, Procs <- Procs, NoProc <- NoProc,
                      MaxObjs <- MaxObjs, Fold <- Fold, Platform <- Platform,
                      IdentityStrength <- IdentityStrength, LockCapability <- LockCapability

\* How a classifier judged the lock path (design Section 6.1).
RecovererPerms == Permutations(Recoverers)
BreakerPerms == Permutations(Breakers)
Judgements == {"none", "empty", "foreign", "uncertain", "cleanuplock", "live", "dead"}

(* --algorithm LockProtocol {
     \* Fairness (design Section 7): every actor is a weakly fair process, so an actor that can keep taking a
     \* step eventually takes it, however busy the others are; the environment is not fair, so whether and
     \* when it crashes something stays a free choice. Weak fairness of the whole system alone let one actor
     \* spin in a retry loop while another that could step never did (plan 3, breaklock liveness).
     \* Each label performs at most ONE filesystem operation (design Section 5.2). A purely local
     \* decision that follows a call - a judgement over what was just read, a branch on whether the
     \* call succeeded - belongs to the same label: no other actor can observe the state between
     \* them, so giving it a label of its own would only add interleavings (Lipton reduction).
     \*
     \* Every label of every actor begins by checking whether this process has crashed. A crash is
     \* performed by the `env` process below, which releases the handles and OS-native locks of the
     \* process it kills (Section 5.2); the process itself then performs nothing further and ends at
     \* Done, which is what keeps TLC's deadlock check meaningful.
     variables
       \* The filesystem (FsModel.tla). A run starts from an empty lock path, or from one holding an object
       \* that is not a Flux lock record, which no actor ever writes (design Section 7, ForeignUntouched).
       fs \in {FsInit, FsWith(P, LockName, Foreign)},
       foreignObj = At(fs, P, LockName),         \* ghost: that Foreign object, or NoObj
       classified = [p \in Procs |-> "none"],     \* ghost: each process's last judgement
       ownerLive = [p \in Procs |-> "none"],      \* what it decided about the record's owner
       sawLive = [p \in Procs |-> FALSE],         \* its classification found a live owner
       seenRec = [p \in Procs |-> EmptyFile],     \* ghost: what this process last read at the lock path
       crashed = [p \in Procs |-> FALSE],         \* ghost: this process died
       live = [p \in Procs |-> FALSE],            \* it has started and has neither finished nor died
       holding = [p \in Procs |-> FALSE],         \* this process owns the target lock now
       checked = [p \in Procs |-> FALSE],         \* its last Section 99 check passed
       writing = [p \in Procs |-> FALSE],         \* its publishing write is issued and has not landed (Section 5.2)
       pendingUnlink = [p \in Procs |-> NoObj],   \* the lock file its issued release unlink resolved, not yet landed
       checkStale = [p \in Procs |-> TRUE],       \* a lock tenure began after its last passing Section 99 check
       writeStale = [p \in Procs |-> TRUE],       \* a lock tenure began after it issued its publishing write
       lostLock = [p \in Procs |-> FALSE],        \* ghost: another process's write, unlink, rename or a lease lapse hit its lock file
       landedAfterTakeover = FALSE,               \* witness: a write issued in an earlier generation landed
       recoveredAfterCrash = FALSE,               \* witness: a lock left by a crash was replaced
       tornRead = FALSE,                          \* witness: a process read a torn record
       hostCrashChangedLock = FALSE,              \* witness: a host crash changed what is at the lock path
       touchedUncertain = FALSE,                  \* a lock judged uncertain was mutated
       refusedOk = [p \in Procs |-> FALSE],       \* the refusal below was justified
       refused = [p \in Procs |-> "none"];        \* what a refusing actor reported

     define {
       LockObj == At(fs, P, LockName)
       \* `f` after process q's issued release unlink lands (Section 5.2). NFS REMOVE carries the directory handle
       \* and the NAME, and the server resolves that name when it EXECUTES the call (RFC 7530, design Section 5.3),
       \* so a stale unlink removes whatever holds the lock name then - including a lock another operation created
       \* meanwhile. The model read this the optimistic way until 2026-09-16, and the three accepted remote windows
       \* were measured under that reading. q = NoProc lands nothing.
       LandUnlink(f, q, c) == IF q # NoProc /\ pendingUnlink[q] # NoObj /\ At(f, P, LockName) # NoObj
                              THEN FsUnlink(f, P, LockName, c).fs ELSE f
       OwnRecord(p) == Rec(p, IF p \in Cleanups THEN "cleanup" ELSE "operation")
       \* A write through a descriptor whose lock this process no longer holds. On Linux NFSv4 the kernel keeps
       \* NFS_LOCK_LOST and the write fails with EIO until the file is closed and opened again (fcntl_locking(2)).
       WriteFenced(p, o) == LEASE_FENCES_WRITES /\ LockCapability = "remote" /\ o # NoObj /\ fs.oslock[o] # p
       \* The object of the one lock-file handle a process holds, or NoObj. A holder of the target lock
       \* has exactly one open handle at the points that use this (after a takeover or a recovery).
       HandleObj(p) == IF \E h \in fs.handles : h.proc = p
                       THEN (CHOOSE h \in fs.handles : h.proc = p).obj
                       ELSE NoObj
       \* "Still owned" (Section 99): a lock file at the lock path holding this operation's record.
       \* FIX_REMOTE_LEASE_SPEC adds the amendment the open finding calls for: this process must still hold that
       \* file's OS-native lock. It cannot get it back once a lease has lapsed - the descriptor keeps the kernel's
       \* NFS_LOCK_LOST state, I/O through it fails with EIO, re-locking the same descriptor does not clear it, and
       \* the documented recovery is to close the file and open it again (fcntl_locking(2), design Section 5.3).
       \* The model tried a relock that took a lapsed lock back until 2026-09-16; no platform offers that.
       StillOwned(p) == /\ LockObj # NoObj
                        /\ fs.content[LockObj] = OwnRecord(p)
                        /\ (FIX_REMOTE_LEASE_SPEC => HandleObj(p) = LockObj /\ fs.oslock[LockObj] = p)
       \* The lock path holds a record whose owner is alive: what justifies TARGET_LOCK_BUSY
       \* (Section 7, 240.2). A takeover's record is the `breaklock` scenario's business.
       BusyJustified == /\ LockObj # NoObj
                        /\ IsRecord(fs.content[LockObj])
                        /\ ~crashed[fs.content[LockObj].op]
       \* The destination provides OS-native locks (235.1): every lock attempt is conditional on it, as
       \* 96.1 and 240.3 step 4 put it. Under `weak` 235.1 refuses first, so only SEED_NO_CAPABILITY_GATE
       \* ever runs a protocol step without them.
       LocksAvailable == LockCapability # "weak"
       \* The evidence a TARGET_LOCK_BUSY refusal rests on, recorded by every refusing label through this
       \* one definition, so SEED_DEAD_AS_BUSY guards all of them (design Section 7, RefusalJustified).
       \* 240.2 defines TARGET_LOCK_BUSY as "the lock is held", so another process holding the OS-native lock
       \* on the file at the lock path is evidence too (owner ruling for plan 3: a takeover writing in place
       \* holds it while the record it replaces is torn).
       HeldByOther(p) == LockObj # NoObj /\ fs.oslock[LockObj] \notin {NoProc, p}
       RefusalEvidence(p) == BusyJustified \/ sawLive[p] \/ HeldByOther(p)
       \* Process q holds an open handle on object o.
       Holds(q, o) == o # NoObj /\ \E h \in fs.handles : h.proc = q /\ h.obj = o
       \* The cause ghost after process `me` writes, unlinks, renames or replaces object o: every other process with
       \* a handle on it has had its lock hit. A failed Section 99 check is justified only by that cause (owner ruling
       \* for plan 3, 2026-09-15): a restatement of the check's own predicate could not catch a wrong refusal.
       MarkLost(me, o) == [q \in Procs |-> IF q # me /\ Holds(q, o) THEN TRUE ELSE lostLock[q]]
       \* The actor's judgement was uncertain: a torn or empty record, or an owner the oracle cannot judge.
       JudgedUncertain(p) == classified[p] = "uncertain" \/ ownerLive[p] = "uncertain"
       \* A lock this actor may replace through 240.3: a dead owner's operation lock, or a cleanup
       \* lock whose owner is dead (251.1, 259.6). The seeds re-introduce the defects of design Section 8.
       Replaceable(p) == \/ classified[p] = "dead"
                         \/ (classified[p] = "cleanuplock" /\ ownerLive[p] = "dead")
                         \/ (SEED_RECOVER_UNCERTAIN /\ classified[p] = "uncertain" /\ ownerLive[p] = "none")
                         \/ (SEED_RECOVER_FOREIGN /\ classified[p] = "foreign")
                         \/ (SEED_RECOVER_UNCERTAIN_CLEANUP_LOCK /\ classified[p] = "cleanuplock"
                                                                /\ ownerLive[p] = "uncertain")
       \* The states the liveness properties are about, and the two state witnesses (Section 7).
       DeadOwnerLock == /\ LockObj # NoObj
                        /\ IsRecord(fs.content[LockObj])
                        /\ crashed[fs.content[LockObj].op]
       TornLock == LockObj # NoObj /\ fs.content[LockObj] = Torn
     }

     \* Classify what is at the lock path: open it, try its OS-native lock without waiting, read the
     \* record, then judge (design Section 6.1). `keep` says whether the caller keeps the handle and
     \* the lock it may have taken, as 240.3 does through its move-aside.
     procedure Classify(keep)
       variables obj = 0, got = FALSE;
     {
       S240_1_open:
         if (crashed[self]) { goto classify_crashed; }
         else {
           \* No entry at the lock path: the open fails and the judgement is "empty" (96.1).
           with (r = FsOpen(fs, P, LockName, self, TRUE)) {
             if (r.ok) { fs := r.fs; obj := r.val; }
             else { classified[self] := "empty"; seenRec[self] := EmptyFile; return; };
         };
         };
       S240_1_trylock:
         if (crashed[self]) { goto classify_crashed; }
         else {
           with (r = FsTryLock(fs, self, obj)) {
             got := r.ok;
             if (r.ok) { fs := r.fs; };
         };
         };
       S240_1_read:
         if (crashed[self]) { goto classify_crashed; }
         else {
           \* Read the record, then judge what was read (Section 6.1's table). A torn or unreadable
           \* record cannot show a dead owner: uncertain (96.1, 240.4, 259.6).
           with (seen = fs.content[obj]) {
             seenRec[self] := seen;
             if (seen = Torn) { tornRead := TRUE; };
             if ((seen = Torn /\ ~SEED_TORN_AS_FOREIGN) \/ seen = EmptyFile) {
               classified[self] := "uncertain";
               ownerLive[self] := "none";
               sawLive[self] := FALSE;
             } else if (seen = Foreign \/ (SEED_TORN_AS_FOREIGN /\ seen = Torn)) {
               \* SEED_TORN_AS_FOREIGN (design Section 8) treats a checksum-failing record as a foreign object.
               classified[self] := "foreign";
               ownerLive[self] := "none";
               sawLive[self] := FALSE;
             } else {
               \* The OS-native lock proves the owner is alive (240.2); otherwise the oracle decides
               \* what no filesystem fact can (Section 6.1), consistent with the truth and free to say
               \* "uncertain" either way.
               with (alive \in IF ~got /\ LockCapability \in {"strong", "remote"} THEN {"live"}
                              ELSE IF crashed[seen.op] THEN {"dead", "uncertain"}
                              ELSE {"live", "uncertain"}) {
                 ownerLive[self] := alive;
                 \* A "live" forced by a failed try-lock shows the lock is held, which is what BUSY means
                 \* (240.2); it does not show who holds it.
                 sawLive[self] := alive = "live";
                 \* A cleanup lock is its own case (251.1); an operation's lock takes its judgement
                 \* from its owner (240.1 to 240.4).
                 if (seen.kind = "cleanup") { classified[self] := "cleanuplock"; }
                 else { classified[self] := alive; };
         };
             };
           };
         };
       S240_1_close:
         \* Unless the caller keeps the handle through its next steps, the classifier closes it at
         \* once, which also gives back the OS-native lock (Section 5.1), so a refusal never leaves a
         \* lock held on another process's file (Section 6.1).
         if (crashed[self]) { goto classify_crashed; }
         else {
           if (~keep \/ ~Replaceable(self)) { fs := FsClose(fs, self, obj).fs; };
           return;
         };
       classify_crashed:
         return;
     }

     \* Acquire the target lock (96.1): create it exclusively, check the directory lock is absent,
     \* take its OS-native lock, then write this operation's record.
     procedure Acquire()
       variables obj = 0;
     {
       S96_1_create:
         if (crashed[self]) { goto acquire_crashed; }
         else {
           \* Another operation created the lock first: start the acquisition again (21.1 step 1).
           with (r = FsCreate(fs, P, LockName, self, TRUE)) {
             if (r.ok) { fs := r.fs; obj := r.val; lostLock[self] := FALSE; }
             else { refused[self] := "RESTART"; return; };
         };
         };
       S96_1_dircheck:
         \* The per-name acquirer announces, then checks (96.1). The directory lock never exists in
         \* this scenario, so the conflict below is the `dirlock` scenario's business.
         if (crashed[self]) { goto acquire_crashed; }
         else {
           if (FsLookup(fs, P, DirLockName)) { goto S96_1_backoff; };
         };
       S96_1_ownlock:
         \* A classifier can open the file just created and take its lock before this step does.
         if (crashed[self]) { goto acquire_crashed; }
         else {
           if (LocksAvailable) {
             with (r = FsTryLock(fs, self, obj)) {
               if (r.ok) { fs := r.fs; }
               else { goto S96_1_ownlock_wait; };
             };
         };
         };
       S96_1_ownlock_verify:
         \* Holding the lock, check that the lock path still names the file and that nobody has written it
         \* (a takeover that finished and released while this acquirer waited): otherwise start again.
         if (crashed[self]) { goto acquire_crashed; }
         else {
           with (ident \in FsIdentityChoices(fs, P, LockName)) {
             if (ident # obj \/ fs.content[obj] # EmptyFile) { goto S96_1_ownlock_close; };
         };
         };
       S96_1_record_begin:
         if (crashed[self]) { goto acquire_crashed; }
         else {
           \* The lease lapsed under this write: the descriptor is poisoned and the write fails (EIO).
           if (WriteFenced(self, obj)) {
             refused[self] := "TARGET_LOCK_BUSY";
             refusedOk[self] := lostLock[self];
             holding[self] := FALSE;
             goto S96_1_ownlock_close;
           }
           else {
             fs := FsWriteBegin(fs, obj).fs;
             lostLock := MarkLost(self, obj);
           };
         };
       S96_1_record_end:
         \* A crash between the two halves of the write leaves the record torn (Section 5.2), which
         \* is what the `NeverTornRead` witness run is about.
         if (crashed[self]) { goto acquire_crashed; }
         else {
           \* The lease lapsed under this write: the descriptor is poisoned and the write fails (EIO).
           if (WriteFenced(self, obj)) {
             refused[self] := "TARGET_LOCK_BUSY";
             refusedOk[self] := lostLock[self];
             holding[self] := FALSE;
             goto S96_1_ownlock_close;
           }
           else {
             fs := FsWriteEnd(fs, obj, OwnRecord(self)).fs;
             \* Either half of a write can hit a file another process took meanwhile, so both mark it.
             lostLock := MarkLost(self, obj);
             seenRec[self] := OwnRecord(self);
             holding[self] := TRUE;
             \* A new tenure: every other process's last check and issued write are stale from here (design Section 7).
             checkStale := [q \in Procs |-> IF q = self THEN checkStale[q] ELSE TRUE];
             writeStale := [q \in Procs |-> IF q = self THEN writeStale[q] ELSE TRUE];
             return;
           };
         };
       S96_1_backoff:
         \* On a conflict the acquirer removes what it created and reports TARGET_LOCK_BUSY (96.1).
         if (crashed[self]) { goto acquire_crashed; }
         else {
           refusedOk[self] := RefusalEvidence(self);
           with (c \in FsUnlinkChoices) { fs := FsUnlink(fs, P, LockName, c).fs; };
           lostLock := MarkLost(self, LockObj);
           refused[self] := "TARGET_LOCK_BUSY";
           return;
         };
       S96_1_ownlock_wait:
         \* Without the OS-native lock the record would prove nothing, and 240.2 would read whoever does
         \* hold the lock as the owner (96.1). The holder may be an inspector, which lets go, or a takeover of
         \* this very file (240.5). While the lock path still names the file and it is still empty, try the
         \* lock again or give up; once it has changed, give up. Giving up closes the handle and never removes
         \* the file by name, which could delete a takeover's lock (plan 3's measured finding): the empty lock
         \* it leaves is uncertain, and --break-lock clears it.
         if (crashed[self]) { goto acquire_crashed; }
         else {
           with (ident \in FsIdentityChoices(fs, P, LockName)) {
             if (ident # obj \/ fs.content[obj] # EmptyFile) { goto S96_1_ownlock_close; }
             else {
               either { goto S96_1_ownlock; }
               or { goto S96_1_ownlock_close; };
             };
         };
         };
       S96_1_ownlock_close:
         \* SEED_ACQUIRER_UNLINKS_BY_NAME puts back the old wording, which removed the file by name first.
         if (crashed[self]) { goto acquire_crashed; }
         else {
           with (c \in FsUnlinkChoices) {
             fs := FsClose(IF SEED_ACQUIRER_UNLINKS_BY_NAME THEN FsUnlink(fs, P, LockName, c).fs ELSE fs, self, obj).fs;
           };
           lostLock := IF SEED_ACQUIRER_UNLINKS_BY_NAME THEN MarkLost(self, LockObj) ELSE lostLock;
           refused[self] := "RESTART";
           return;
         };
       acquire_crashed:
         return;
     }

     \* Replace a dead owner's lock by moving it aside (240.3 steps 1 to 5). The caller has
     \* classified the lock as replaceable and still holds its handle and its OS-native lock.
     procedure Recover()
       variables robj = 0, victim = NoProc, nobj = 0;
     {
       S240_3_s1:
         \* Re-read the lock: proceed only if it still names the same dead owner.
         if (crashed[self]) { goto recover_crashed; }
         else {
           robj := LockObj;
           if (IsRecord(seenRec[self])) { victim := seenRec[self].op; };
           if (LockObj = NoObj \/ fs.content[LockObj] # seenRec[self]) { goto S240_3_restart; };
         };
       S240_3_s2:
         \* Only one of several concurrent recoverers can move it; the others find the lock gone and
         \* start the acquisition again (240.3 step 2).
         if (crashed[self]) { goto recover_crashed; }
         else {
           if (JudgedUncertain(self)) { touchedUncertain := TRUE; };
           with (r = FsRenameNoReplace(fs, P, LockName, BrokenOf(self))) {
             if (r.ok) { fs := r.fs; lostLock := MarkLost(self, LockObj); } else { goto S240_3_restart; };
         };
         };
       S240_3_s3:
         \* Check the moved file is the one step 1 re-read, by identity AND by its record: a takeover
         \* rewrites the record in the same file, so identity alone is not enough (240.3 step 3).
         if (crashed[self]) { goto recover_crashed; }
         else {
           with (ident \in FsIdentityChoices(fs, P, BrokenOf(self))) {
             if (ident # robj \/ fs.content[robj] # seenRec[self]) { goto S240_3_putback; };
         };
         };
       S240_3_s4:
         \* Create its own lock exclusively (step 4). If that fails, another operation owns the
         \* target: delete the moved file, whose owner is dead, and start again.
         if (crashed[self]) { goto recover_crashed; }
         else {
           with (r = FsCreate(fs, P, LockName, self, TRUE)) {
             if (r.ok) { fs := r.fs; nobj := r.val; lostLock[self] := FALSE; } else { goto S240_3_s4_drop; };
         };
         };
       S240_3_s4_lock:
         \* The lock, and the record write below, go through the handle the create returned, as the
         \* acquirer's do (a reading, recorded in trace.toml): never through a second lookup of the path.
         if (crashed[self]) { goto recover_crashed; }
         else {
           if (LocksAvailable) {
             with (r = FsTryLock(fs, self, nobj)) {
               if (r.ok) { fs := r.fs; }
               else { goto S240_3_s4_lock_wait; };
             };
         };
         };
       S240_3_s4_lock_verify:
         \* As 96.1's acquirer: holding the lock, the path must still name the new file and it must still
         \* be empty, or the recoverer closes it and drops the moved file.
         if (crashed[self]) { goto recover_crashed; }
         else {
           with (ident \in FsIdentityChoices(fs, P, LockName)) {
             if (ident # nobj \/ fs.content[nobj] # EmptyFile) { goto S240_3_s4_lock_close; };
         };
         };
       S240_3_s4_record_begin:
         if (crashed[self]) { goto recover_crashed; }
         else {
           \* The lease lapsed under this write: the descriptor is poisoned and the write fails (EIO).
           if (WriteFenced(self, nobj)) {
             refused[self] := "TARGET_LOCK_BUSY";
             refusedOk[self] := lostLock[self];
             holding[self] := FALSE;
             goto S240_3_s4_lock_close;
           }
           else {
             fs := FsWriteBegin(fs, nobj).fs;
             lostLock := MarkLost(self, nobj);
           };
         };
       S240_3_s4_record_end:
         if (crashed[self]) { goto recover_crashed; }
         else {
           \* The lease lapsed under this write: the descriptor is poisoned and the write fails (EIO).
           if (WriteFenced(self, nobj)) {
             refused[self] := "TARGET_LOCK_BUSY";
             refusedOk[self] := lostLock[self];
             holding[self] := FALSE;
             goto S240_3_s4_lock_close;
           }
           else {
             fs := FsWriteEnd(fs, nobj, OwnRecord(self)).fs;
             lostLock := MarkLost(self, nobj);
             seenRec[self] := OwnRecord(self);
             holding[self] := TRUE;
             \* A new tenure: every other process's last check and issued write are stale from here (design Section 7).
             checkStale := [q \in Procs |-> IF q = self THEN checkStale[q] ELSE TRUE];
             writeStale := [q \in Procs |-> IF q = self THEN writeStale[q] ELSE TRUE];
           };
         };
       S240_3_s5:
         \* Delete the moved file (step 5).
         if (crashed[self]) { goto recover_crashed; }
         else {
           with (c \in FsUnlinkChoices) { fs := FsUnlink(fs, P, BrokenOf(self), c).fs; };
           if (victim \in Procs) { if (crashed[victim]) { recoveredAfterCrash := TRUE; }; };
           goto S240_3_release;
         };
       S240_3_s4_drop:
         if (crashed[self]) { goto recover_crashed; }
         else {
           with (c \in FsUnlinkChoices) { fs := FsUnlink(fs, P, BrokenOf(self), c).fs; };
           refused[self] := "RESTART";
           goto S240_3_release;
         };
       S240_3_s4_lock_wait:
         \* The same rule at 240.3 step 4 (96.1): while the path still names the new file and it is still
         \* empty, try the lock again or give up; giving up closes without removing the file by name, then
         \* drops the moved file as a failed create does, and starts again.
         if (crashed[self]) { goto recover_crashed; }
         else {
           with (ident \in FsIdentityChoices(fs, P, LockName)) {
             if (ident # nobj \/ fs.content[nobj] # EmptyFile) { goto S240_3_s4_lock_close; }
             else {
               either { goto S240_3_s4_lock; }
               or { goto S240_3_s4_lock_close; };
             };
         };
         };
       S240_3_s4_lock_close:
         \* SEED_ACQUIRER_UNLINKS_BY_NAME puts back the old wording, which removed the file by name first.
         if (crashed[self]) { goto recover_crashed; }
         else {
           with (c \in FsUnlinkChoices) {
             fs := FsClose(IF SEED_ACQUIRER_UNLINKS_BY_NAME THEN FsUnlink(fs, P, LockName, c).fs ELSE fs, self, nobj).fs;
           };
           lostLock := IF SEED_ACQUIRER_UNLINKS_BY_NAME THEN MarkLost(self, LockObj) ELSE lostLock;
           goto S240_3_s4_drop;
         };
       S240_3_putback:
         \* Rename the file back without replacing, then start the acquisition again (step 3).
         if (crashed[self]) { goto recover_crashed; }
         else {
           with (r = FsRenameNoReplace(fs, P, BrokenOf(self), LockName)) {
             if (r.ok) { fs := r.fs; };
           };
           refused[self] := "RESTART";
           goto S240_3_release;
         };
       S240_3_restart:
         \* Start the acquisition again (21.1 step 1). This model stops here instead of looping: one
         \* pass reaches every state a further one would, and the bound is in the README.
         refused[self] := "RESTART";
       S240_3_release:
         if (crashed[self]) { goto recover_crashed; }
         else {
           if (robj # NoObj /\ OpenBy(fs, self, robj)) { fs := FsClose(fs, self, robj).fs; };
           return;
         };
       recover_crashed:
         return;
     }

     \* Take an uncertain lock over in place (240.5 steps 1 to 6), so the lock path is never empty. The
     \* caller classified the lock as uncertain and closed that handle; `seenRec` holds the record it
     \* reported as the holder. A takeover that succeeds returns holding the lock file's handle and its
     \* OS-native lock; every other outcome returns holding nothing.
     procedure TakeOver()
       variables tobj = 0;
     {
       S240_5_s1:
         \* Strong file identity and OS-native locks, decided from the capability, never by a trial lock.
         if (crashed[self]) { goto takeover_crashed; }
         else {
           if (IdentityStrength # "strong" \/ (LockCapability \notin {"strong", "remote"} /\ ~SEED_NO_CAPABILITY_GATE)) {
             refused[self] := "TARGET_LOCK_UNCERTAIN";
             return;
           };
         };
       S240_5_s2:
         \* Open the existing lock file for writing, without creating it; if it is gone, start again.
         if (crashed[self]) { goto takeover_crashed; }
         else {
           with (r = FsOpen(fs, P, LockName, self, TRUE)) {
             if (r.ok) { fs := r.fs; tobj := r.val; lostLock[self] := FALSE; }
             else { refused[self] := "RESTART"; return; };
         };
         };
       S240_5_s3:
         \* Its OS-native lock without waiting. A failure means another process holds it (the owner, or
         \* another takeover), and that failure is the refusal's evidence (240.2).
         if (crashed[self]) { goto takeover_crashed; }
         else {
           if (LocksAvailable) {
             with (r = FsTryLock(fs, self, tobj)) {
               if (r.ok) { fs := r.fs; }
               else {
                 refusedOk[self] := fs.oslock[tobj] # NoProc \/ RefusalEvidence(self);
                 refused[self] := "TARGET_LOCK_BUSY";
                 goto S240_5_close;
               };
             };
         };
         };
       S240_5_s4:
         \* The open file must still be the one at the lock path.
         if (crashed[self]) { goto takeover_crashed; }
         else {
           with (ident \in FsIdentityChoices(fs, P, LockName)) {
             if (ident # tobj) { refused[self] := "RESTART"; goto S240_5_close; };
         };
         };
       S240_5_s5:
         \* Read the record. A live owner refuses; another operation than the reported holder starts
         \* again; the reported holder, or an unreadable record, continues. Whether a named owner is
         \* alive is the oracle's judgement, as in classification (design Section 6.1).
         if (crashed[self]) { goto takeover_crashed; }
         else {
           with (seen = fs.content[tobj]) {
             if (IsRecord(seen) /\ seen # seenRec[self]) { refused[self] := "RESTART"; goto S240_5_close; }
             else if (IsRecord(seen)) {
               with (alive \in IF crashed[seen.op] THEN {"dead", "uncertain"} ELSE {"live", "uncertain"}) {
                 if (alive = "live") {
                   sawLive[self] := TRUE;
                   \* A define-block operator reads the variables as they were before this step, so RefusalEvidence
                   \* would not see the sawLive set just above; the judgement is passed in directly. Measured under
                   \* remote (2026-09-15): the prior owner's release unlink empties the path during the takeover, so
                   \* BusyJustified is false and only this judgement is behind the refusal.
                   refusedOk[self] := alive = "live" \/ RefusalEvidence(self);
                   refused[self] := "TARGET_LOCK_BUSY";
                   goto S240_5_close;
                 };
             };
             };
         };
         };
       S240_5_s6_seed:
         \* SEED_RENAME_OVER_TAKEOVER (design Section 8): instead of overwriting in place, build this
         \* operation's record under a private name and rename it over the lock.
         if (crashed[self]) { goto takeover_crashed; }
         else {
           if (SEED_RENAME_OVER_TAKEOVER) {
             with (r = FsCreate(fs, P, TakeoverName(self), self, TRUE)) {
               if (r.ok) { fs := r.fs; goto S240_5_seed_write_begin; }
               else { refused[self] := "RESTART"; goto S240_5_close; };
             };
           };
         };
       S240_5_s6_write_begin:
         \* Overwrite the record in place with this operation's record, in one write (259.6).
         if (crashed[self]) { goto takeover_crashed; }
         else {
           \* The lease lapsed under this write: the descriptor is poisoned and the write fails (EIO).
           if (WriteFenced(self, tobj)) {
             refused[self] := "TARGET_LOCK_BUSY";
             refusedOk[self] := lostLock[self];
             holding[self] := FALSE;
             goto S240_5_close;
           }
           else {
             fs := FsWriteBegin(fs, tobj).fs;
             lostLock := MarkLost(self, tobj);
           };
         };
       S240_5_s6_write_end:
         if (crashed[self]) { goto takeover_crashed; }
         else {
           \* The lease lapsed under this write: the descriptor is poisoned and the write fails (EIO).
           if (WriteFenced(self, tobj)) {
             refused[self] := "TARGET_LOCK_BUSY";
             refusedOk[self] := lostLock[self];
             holding[self] := FALSE;
             goto S240_5_close;
           }
           else {
             fs := FsWriteEnd(fs, tobj, OwnRecord(self)).fs;
             lostLock := MarkLost(self, tobj);
             seenRec[self] := OwnRecord(self);
           };
         };
       S240_5_s6_flush:
         if (crashed[self]) { goto takeover_crashed; }
         else {
           fs := FsFlushFile(fs, tobj).fs;
         };
       S240_5_s6:
         \* Check the file identity against the lock path again. Empty: the prior owner removed its lock
         \* meanwhile, so start again. Another file: whoever created it owns the target. The same file: the
         \* takeover stands, and this operation proceeds as if the prior owner were dead.
         if (crashed[self]) { goto takeover_crashed; }
         else {
           with (ident \in FsIdentityChoices(fs, P, LockName)) {
             if (ident = NoObj) { refused[self] := "RESTART"; goto S240_5_close; }
             else if (ident # tobj) {
               refusedOk[self] := LockObj # NoObj /\ LockObj # tobj;
               refused[self] := "TARGET_LOCK_BUSY";
               goto S240_5_close;
             }
             else {
               \* The takeover stands: it ends the prior owner's tenure (design Section 7).
               holding[self] := TRUE;
               checkStale := [q \in Procs |-> IF q = self THEN checkStale[q] ELSE TRUE];
               writeStale := [q \in Procs |-> IF q = self THEN writeStale[q] ELSE TRUE];
               return;
             };
         };
         };
       S240_5_seed_write_begin:
         if (crashed[self]) { goto takeover_crashed; }
         else {
           fs := FsWriteBegin(fs, At(fs, P, TakeoverName(self))).fs;
           lostLock := MarkLost(self, At(fs, P, TakeoverName(self)));
         };
       S240_5_seed_write_end:
         if (crashed[self]) { goto takeover_crashed; }
         else {
           fs := FsWriteEnd(fs, At(fs, P, TakeoverName(self)), OwnRecord(self)).fs;
           lostLock := MarkLost(self, At(fs, P, TakeoverName(self)));
           seenRec[self] := OwnRecord(self);
         };
       S240_5_seed_rename:
         \* The rename replaces the lock; the old file keeps its handles and its OS-native lock.
         if (crashed[self]) { goto takeover_crashed; }
         else {
           with (r = FsRenameReplace(fs, P, TakeoverName(self), LockName)) {
             if (r.ok) {
               fs := FsClose(r.fs, self, tobj).fs;
               lostLock := MarkLost(self, LockObj);
               holding[self] := TRUE;
               checkStale := [q \in Procs |-> IF q = self THEN checkStale[q] ELSE TRUE];
               writeStale := [q \in Procs |-> IF q = self THEN writeStale[q] ELSE TRUE];
               return;
             }
             else { refused[self] := "RESTART"; goto S240_5_close; };
           };
         };
       S240_5_close:
         if (crashed[self]) { goto takeover_crashed; }
         else {
           if (tobj # NoObj /\ OpenBy(fs, self, tobj)) { fs := FsClose(fs, self, tobj).fs; };
           return;
         };
       takeover_crashed:
         return;
     }

     \* Publish under the lock, revalidating before the write (Section 99), then release it.
     procedure Publish()
     {
       S99_check:
         \* "Still owned" is a read of the lock path; the decision that follows is local.
         if (crashed[self]) { goto publish_crashed; }
         else {
           if (StillOwned(self)) { checked[self] := TRUE; checkStale[self] := FALSE; }
           else {
             checked[self] := FALSE;
             refusedOk[self] := lostLock[self];
             refused[self] := "TARGET_LOCK_BUSY";
             holding[self] := FALSE;
             goto S99_refuse_close;
         };
         };
       S99_write:
         \* The write itself: a separate label, because the spec's check must come immediately before
         \* it and another actor can act in between (design Section 11's check-to-call window). What
         \* it writes is not part of the lock protocol here, so no object is created: the `nested`
         \* scenario, which is about what gets written where, creates it.
         if (crashed[self]) { goto publish_crashed; }
         else {
           writing[self] := TRUE;
           writeStale[self] := FALSE;
         };
       S240_5_inflight_lands:
         \* The issued write completes (Section 5.2). A takeover can land in between, and "a filesystem call it had
         \* already started can still complete" (240.5).
         if (crashed[self]) { goto publish_crashed; }
         else {
           if (writeStale[self]) { landedAfterTakeover := TRUE; };
           writing[self] := FALSE;
           \* Neither flag is read again until the next check or write sets it, so both go back to their initial
           \* value: a state that differs only in them is the same state.
           writeStale[self] := TRUE;
         };
       S99_release_check:
         \* Section 99 lists unlink among the calls it guards, so the release is revalidated too (a reading
         \* of the spec, recorded in trace.toml): a lock that is no longer this operation's is not removed.
         if (crashed[self]) { goto publish_crashed; }
         else {
           checked[self] := FALSE;
           checkStale[self] := TRUE;
           if (~StillOwned(self)) {
             refusedOk[self] := lostLock[self];
             refused[self] := "TARGET_LOCK_BUSY";
             holding[self] := FALSE;
             goto S99_refuse_close;
           };
         };
       S99_release:
         \* The release unlink is issued: it resolves the lock path to a file now and removes that file's name when
         \* it lands, as a system call resolves its path when it starts.
         if (crashed[self]) { goto publish_crashed; }
         else {
           holding[self] := FALSE;
           pendingUnlink[self] := LockObj;
         };
       S99_release_lands:
         if (crashed[self]) { goto publish_crashed; }
         else {
           with (c \in FsUnlinkChoices) {
             fs := LandUnlink(fs, self, c);
           };
           lostLock := IF pendingUnlink[self] # NoObj /\ LockObj # NoObj THEN MarkLost(self, LockObj) ELSE lostLock;
           pendingUnlink[self] := NoObj;
         };
       S99_close:
         if (crashed[self]) { goto publish_crashed; }
         else {
           \* Close the lock file's handle, which may no longer be at the lock path once the release unlink landed.
           fs := FsCloseAll(fs, self);
           return;
         };
       S99_refuse_close:
         \* A failed check stops the operation, which gives up its handles and so its OS-native lock (design
         \* Section 6.1): close every handle this process holds.
         if (crashed[self]) { goto publish_crashed; }
         else {
           fs := FsCloseAll(fs, self);
           return;
         };
       publish_crashed:
         checked[self] := FALSE;
         checkStale[self] := TRUE;
         return;
     }

     \* A normal operation: acquire the lock, publish, release.
     fair process (own \in Owners)
     {
       own_start:
         if (LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE) {
           \* 235.1: without verified OS-native locks, an operation needing target exclusivity refuses.
           refused[self] := "REMOTE_LOCK_UNSAFE";
           goto own_end;
         }
         else {
           live[self] := TRUE;
           call Acquire();
         };
       own_publish:
         if (~crashed[self] /\ holding[self]) { call Publish(); };
       own_end:
         live[self] := FALSE;
         lostLock[self] := FALSE;
     }

     \* A new invocation with no flags (21.1): classify what it finds, then act or refuse.
     fair process (plain \in PlainRuns)
     {
       plain_start:
         if (LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE) {
           \* 235.1: without verified OS-native locks, an operation needing target exclusivity refuses.
           refused[self] := "REMOTE_LOCK_UNSAFE";
           goto plain_end;
         }
         else {
           live[self] := TRUE;
           call Classify(FALSE);
         };
       S21_1_decide:
         if (crashed[self]) { goto plain_end; }
         else {
           refusedOk[self] := RefusalEvidence(self);
           if (classified[self] = "empty") { goto plain_acquire; }
           else if (Replaceable(self) /\ classified[self] = "cleanuplock") {
             \* A cleanup lock names no resumable operation (259.6), so a dead one is removed as 240.3
             \* describes and this invocation proceeds (21.1).
             goto plain_recover;
           }
           else if (classified[self] = "live" \/ (SEED_DEAD_AS_BUSY /\ classified[self] = "dead")) {
             refused[self] := "TARGET_LOCK_BUSY";
           }
         else if (classified[self] = "uncertain" \/ ownerLive[self] = "uncertain") {
           refused[self] := "TARGET_LOCK_UNCERTAIN";
         }
         else if (classified[self] = "foreign") { refused[self] := "CONTROL_PLANE_NAMESPACE_CONFLICT"; }
         else if (classified[self] = "cleanuplock") { refused[self] := "TARGET_LOCK_BUSY"; }
         else {
           \* A resumable prior operation, with neither --resume nor --restart: refuse without
           \* mutating anything (21.1).
             refused[self] := "RESUMABLE_OPERATION_EXISTS";
           };
         };
       S21_1_refused:
         goto plain_end;
       plain_recover:
         call Recover();
       plain_recovered:
         if (~crashed[self] /\ holding[self]) { call Publish(); };
       plain_recovered_done:
         goto plain_end;
       plain_acquire:
         call Acquire();
       plain_publish:
         if (~crashed[self] /\ holding[self]) { call Publish(); };
       plain_end:
         live[self] := FALSE;
         lostLock[self] := FALSE;
     }

     \* A new invocation that finds a dead owner's lock, recovers it (240.3), then continues as an
     \* owner: the recovery path of 21.1 step 1.
     fair process (rec \in Recoverers)
     {
       rec_start:
         if (LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE) {
           \* 235.1: without verified OS-native locks, an operation needing target exclusivity refuses.
           refused[self] := "REMOTE_LOCK_UNSAFE";
           goto rec_end;
         }
         else {
           live[self] := TRUE;
           call Classify(TRUE);
         };
       rec_decide:
         if (crashed[self]) { goto rec_end; }
         else {
           refusedOk[self] := RefusalEvidence(self);
           if (Replaceable(self)) { goto rec_recover; }
           else if (classified[self] = "empty") { goto rec_acquire; }
           else if (classified[self] = "uncertain" \/ ownerLive[self] = "uncertain") {
             refused[self] := "TARGET_LOCK_UNCERTAIN";
           }
           else if (classified[self] = "foreign") { refused[self] := "CONTROL_PLANE_NAMESPACE_CONFLICT"; }
           else { refused[self] := "TARGET_LOCK_BUSY"; };
         };
       rec_refused:
         goto rec_end;
       rec_recover:
         call Recover();
       rec_publish:
         if (~crashed[self] /\ holding[self]) { call Publish(); };
       rec_publish_done:
         goto rec_end;
       rec_acquire:
         call Acquire();
       rec_acquired:
         if (~crashed[self] /\ holding[self]) { call Publish(); };
       rec_end:
         live[self] := FALSE;
         lostLock[self] := FALSE;
     }

     \* flux cleanup DEST: classify the lock, remove a dead owner's or a dead cleanup lock through
     \* 240.3 under its own cleanup lock, then delete that lock last (251.1, 259.6).
     fair process (clean \in Cleanups)
     {
       clean_start:
         if (LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE) {
           \* 235.1: without verified OS-native locks, an operation needing target exclusivity refuses.
           refused[self] := "REMOTE_LOCK_UNSAFE";
           goto clean_end;
         }
         else {
           live[self] := TRUE;
           call Classify(TRUE);
         };
       S251_1_classify:
         if (crashed[self]) { goto clean_end; }
         else {
           refusedOk[self] := RefusalEvidence(self);
           if (Replaceable(self)) { goto clean_recover; }
           else if (classified[self] = "empty") { refused[self] := "NOTHING_TO_CLEAN"; }
           else if (classified[self] = "foreign") { refused[self] := "CONTROL_PLANE_NAMESPACE_CONFLICT"; }
           else if (classified[self] = "uncertain" \/ ownerLive[self] = "uncertain") {
             \* Artifacts of uncertain ownership need `flux cleanup --target PATH --break-lock` (251.2).
             refused[self] := "TARGET_LOCK_UNCERTAIN";
           }
           else { refused[self] := "TARGET_LOCK_BUSY"; };
         };
       clean_refused:
         goto clean_end;
       clean_recover:
         call Recover();
       S251_1_delete:
         \* Its own cleanup lock goes last, while it still holds the OS-native lock (240.5, 251.1).
         if (crashed[self]) { goto clean_end; }
         else {
           if (holding[self]) {
             holding[self] := FALSE;
             with (c \in FsUnlinkChoices) { fs := FsUnlink(fs, P, LockName, c).fs; };
             lostLock := MarkLost(self, LockObj);
         };
         };
       S251_1_close:
         if (crashed[self]) { goto clean_end; }
         else {
           if (LockObj # NoObj /\ OpenBy(fs, self, LockObj)) { fs := FsClose(fs, self, LockObj).fs; };
         };
       clean_end:
         live[self] := FALSE;
         lostLock[self] := FALSE;
     }

     \* flux copy --restart --break-lock (21.1, 240.5). It classifies the lock first (the reported holder
     \* 240.5 reads before acting). A dead owner's lock is replaced through 240.3, as 21.1 step 1 says; an
     \* uncertain one is taken over in place; anything else is handled as a plain rerun would. Holding
     \* the lock, it then revalidates (21.1 step 3) and rewrites the record for the new operation (step 5),
     \* and continues as an Owner. 21.1 steps 2 and 4 change only the prior operation's state, which is
     \* not modelled.
     fair process (brk \in Breakers)
     {
       brk_start:
         if (LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE) {
           \* 235.1: without verified OS-native locks, an operation needing target exclusivity refuses.
           refused[self] := "REMOTE_LOCK_UNSAFE";
           goto brk_end;
         }
         else {
           live[self] := TRUE;
           call Classify(TRUE);
         };
       S21_1_restart_decide:
         if (crashed[self]) { goto brk_end; }
         else {
           refusedOk[self] := RefusalEvidence(self);
           if (Replaceable(self)) { goto brk_recover; }
           else if (classified[self] = "empty") { goto brk_acquire; }
           else if (classified[self] = "uncertain") {
             \* SEED_MOVE_ASIDE_FOR_UNCERTAIN (design Section 8) moves the uncertain lock aside instead.
             if (SEED_MOVE_ASIDE_FOR_UNCERTAIN) { goto brk_recover; } else { goto brk_takeover; };
           }
           else if (ownerLive[self] = "uncertain") { refused[self] := "TARGET_LOCK_UNCERTAIN"; }
           else if (classified[self] = "foreign") { refused[self] := "CONTROL_PLANE_NAMESPACE_CONFLICT"; }
           else { refused[self] := "TARGET_LOCK_BUSY"; };
         };
       brk_refused:
         goto brk_end;
       brk_takeover:
         call TakeOver();
       brk_took_over:
         goto S21_1_s3;
       brk_recover:
         call Recover();
       S21_1_s3:
         \* Revalidate the lock it now holds (Section 99).
         if (crashed[self] \/ ~holding[self]) { goto brk_end; }
         else {
           if (~StillOwned(self)) {
             refusedOk[self] := lostLock[self];
             refused[self] := "TARGET_LOCK_BUSY";
             holding[self] := FALSE;
             goto S21_1_s3_refuse_close;
           };
         };
       S21_1_s5_write_begin:
         \* The lock record is rewritten for the new operation, under the lock already held: through the
         \* handle that holds it, not through a second lookup of the path (a reading, recorded in trace.toml).
         if (crashed[self]) { goto brk_end; }
         else {
           \* SEED_RESTART_RELEASES (design Section 8) releases the OS-native lock here first.
           \* The lease lapsed under this write: the descriptor is poisoned and the write fails (EIO).
           if (WriteFenced(self, HandleObj(self))) {
             refused[self] := "TARGET_LOCK_BUSY";
             refusedOk[self] := lostLock[self];
             holding[self] := FALSE;
             goto S21_1_s3_refuse_close;
           }
           else {
             fs := FsWriteBegin(IF SEED_RESTART_RELEASES THEN FsUnlock(fs, self, HandleObj(self)).fs ELSE fs,
                                HandleObj(self)).fs;
             lostLock := MarkLost(self, HandleObj(self));
           };
         };
       S21_1_s5_write_end:
         if (crashed[self]) { goto brk_end; }
         else {
           \* The lease lapsed under this write: the descriptor is poisoned and the write fails (EIO).
           if (WriteFenced(self, HandleObj(self))) {
             refused[self] := "TARGET_LOCK_BUSY";
             refusedOk[self] := lostLock[self];
             holding[self] := FALSE;
             goto S21_1_s3_refuse_close;
           }
           else {
             fs := FsWriteEnd(fs, HandleObj(self), OwnRecord(self)).fs;
             lostLock := MarkLost(self, HandleObj(self));
           };
         };
       brk_publish:
         if (~crashed[self] /\ holding[self]) { call Publish(); };
       brk_publish_done:
         goto brk_end;
       brk_acquire:
         call Acquire();
       brk_acquired:
         if (~crashed[self] /\ holding[self]) { call Publish(); };
       brk_acquired_done:
         goto brk_end;
       S21_1_s3_refuse_close:
         if (crashed[self]) { goto brk_end; }
         else {
           fs := FsCloseAll(fs, self);
         };
       brk_end:
         live[self] := FALSE;
         lostLock[self] := FALSE;
     }

     \* The environment: the crashes of Section 5.2. A process crash releases the handles, their
     \* sharing restrictions and the OS-native locks of the process it kills, and leaves everything it
     \* wrote as it is, so a record write caught between its two halves stays torn. A host crash is a
     \* process crash of every process that has started, and then resolves every unflushed object and
     \* every unflushed entry operation. At most `MaxCrashes` crashes happen in a run, counted across
     \* both kinds, and a host crash counts as one however many processes it stops.
     \* Under `LockCapability = remote` it may also let a lock lease lapse under a live holder, at most
     \* `MaxLeaseExpiries` times, counted apart from crashes (design Section 5.1).
     process (env = "env")
       variables crashes = 0, leases = 0;
     {
       env_loop:
         while (crashes < MaxCrashes \/ leases < MaxLeaseExpiries) {
           either {
             \* Crash one running process.
             await crashes < MaxCrashes;
             with (p \in {q \in Procs : live[q] /\ ~crashed[q]}, land \in BOOLEAN, c \in FsUnlinkChoices) {
               \* Its in-flight calls land or are dropped at the crash itself (design Section 5.2).
               fs := FsProcCrash(LandUnlink(fs, IF land THEN p ELSE NoProc, c), p);
               \* Its own ghost goes back to FALSE: a crashed process never refuses again, so any other value is
               \* dead state that splits states which are otherwise the same.
               lostLock := [ (IF land /\ pendingUnlink[p] # NoObj /\ LockObj # NoObj
                              THEN MarkLost(p, LockObj) ELSE lostLock) EXCEPT ![p] = FALSE ];
               landedAfterTakeover := landedAfterTakeover \/ (land /\ writing[p] /\ writeStale[p]);
               writing[p] := FALSE;
               pendingUnlink[p] := NoObj;
               crashed[p] := TRUE;
               \* It loses its in-memory state (Section 5.2): it is no longer inside a publishing
               \* step and no longer owns anything, whatever its lock file still says.
               checked[p] := FALSE;
               checkStale[p] := TRUE;
               writeStale[p] := TRUE;
               holding[p] := FALSE;
               crashes := crashes + 1;
             };
           }
           or {
             \* The whole host goes down.
             await HostCrashes /\ crashes < MaxCrashes;
             \* Each in-flight call lands or is dropped at the crash (Section 5.2): at most one issued release unlink
             \* can still name the lock file, so choosing one lander, or none, covers every outcome. What landed is
             \* unflushed, so the host crash can undo it.
             with (lander \in {NoProc} \cup {q \in Procs : live[q]}, c \in FsUnlinkChoices) {
               with (pick \in HostCrashPicks(LandUnlink(fs, lander, c)), dirs \in HostCrashDirs) {
                 \* An unflushed create, move-aside or removal at the lock path undone (Section 11).
                 \* One line: a disjunct continued on the next line would split the translated action (TLC error 2109).
                 hostCrashChangedLock := (hostCrashChangedLock \/ At(FsHostCrash(LandUnlink(fs, lander, c), pick, dirs), P, LockName) # At(LandUnlink(fs, lander, c), P, LockName));
                 fs := FsHostCrash(LandUnlink(fs, lander, c), pick, dirs);
               };
             };
             crashed := [q \in Procs |-> IF live[q] THEN TRUE ELSE crashed[q]];
             \* The in-flight calls are resolved above; an in-flight data write's effect is not modelled (Section 5.2).
             writing := [q \in Procs |-> IF live[q] THEN FALSE ELSE writing[q]];
             pendingUnlink := [q \in Procs |-> IF live[q] THEN NoObj ELSE pendingUnlink[q]];
             checked := [q \in Procs |-> IF live[q] THEN FALSE ELSE checked[q]];
             checkStale := [q \in Procs |-> IF live[q] THEN TRUE ELSE checkStale[q]];
             lostLock := [q \in Procs |-> IF live[q] THEN FALSE ELSE lostLock[q]];
             writeStale := [q \in Procs |-> IF live[q] THEN TRUE ELSE writeStale[q]];
             holding := [q \in Procs |-> IF live[q] THEN FALSE ELSE holding[q]];
             crashes := crashes + 1;
           }
           or {
             \* A remote lock's lease lapses under a live holder, which is not told.
             await LockCapability = "remote" /\ leases < MaxLeaseExpiries;
             with (o \in {x \in Objs : fs.oslock[x] # NoProc /\ live[fs.oslock[x]] /\ ~crashed[fs.oslock[x]]}) {
               \* Before fs: PlusCal reads fs as already assigned once it has been, so the holder must be read first.
               lostLock[fs.oslock[o]] := TRUE;
               fs := FsLeaseExpiry(fs, o).fs;
               leases := leases + 1;
             };
           }
           or {
             \* Nothing crashes after all: the environment may simply stop.
             goto env_done;
           };
         };
       env_done:
         skip;
     }
   } *)
\* BEGIN TRANSLATION (chksum(pcal) = "feb9f774" /\ chksum(tla) = "9b1b507b")
\* Procedure variable obj of procedure Classify at line 171 col 18 changed to obj_
CONSTANT defaultInitValue
VARIABLES fs, foreignObj, classified, ownerLive, sawLive, seenRec, crashed, 
          live, holding, checked, writing, pendingUnlink, checkStale, 
          writeStale, lostLock, landedAfterTakeover, recoveredAfterCrash, 
          tornRead, hostCrashChangedLock, touchedUncertain, refusedOk, 
          refused, pc, stack

(* define statement *)
LockObj == At(fs, P, LockName)





LandUnlink(f, q, c) == IF q # NoProc /\ pendingUnlink[q] # NoObj /\ At(f, P, LockName) # NoObj
                       THEN FsUnlink(f, P, LockName, c).fs ELSE f
OwnRecord(p) == Rec(p, IF p \in Cleanups THEN "cleanup" ELSE "operation")


WriteFenced(p, o) == LEASE_FENCES_WRITES /\ LockCapability = "remote" /\ o # NoObj /\ fs.oslock[o] # p


HandleObj(p) == IF \E h \in fs.handles : h.proc = p
                THEN (CHOOSE h \in fs.handles : h.proc = p).obj
                ELSE NoObj






StillOwned(p) == /\ LockObj # NoObj
                 /\ fs.content[LockObj] = OwnRecord(p)
                 /\ (FIX_REMOTE_LEASE_SPEC => HandleObj(p) = LockObj /\ fs.oslock[LockObj] = p)


BusyJustified == /\ LockObj # NoObj
                 /\ IsRecord(fs.content[LockObj])
                 /\ ~crashed[fs.content[LockObj].op]



LocksAvailable == LockCapability # "weak"





HeldByOther(p) == LockObj # NoObj /\ fs.oslock[LockObj] \notin {NoProc, p}
RefusalEvidence(p) == BusyJustified \/ sawLive[p] \/ HeldByOther(p)

Holds(q, o) == o # NoObj /\ \E h \in fs.handles : h.proc = q /\ h.obj = o



MarkLost(me, o) == [q \in Procs |-> IF q # me /\ Holds(q, o) THEN TRUE ELSE lostLock[q]]

JudgedUncertain(p) == classified[p] = "uncertain" \/ ownerLive[p] = "uncertain"


Replaceable(p) == \/ classified[p] = "dead"
                  \/ (classified[p] = "cleanuplock" /\ ownerLive[p] = "dead")
                  \/ (SEED_RECOVER_UNCERTAIN /\ classified[p] = "uncertain" /\ ownerLive[p] = "none")
                  \/ (SEED_RECOVER_FOREIGN /\ classified[p] = "foreign")
                  \/ (SEED_RECOVER_UNCERTAIN_CLEANUP_LOCK /\ classified[p] = "cleanuplock"
                                                         /\ ownerLive[p] = "uncertain")

DeadOwnerLock == /\ LockObj # NoObj
                 /\ IsRecord(fs.content[LockObj])
                 /\ crashed[fs.content[LockObj].op]
TornLock == LockObj # NoObj /\ fs.content[LockObj] = Torn

VARIABLES keep, obj_, got, obj, robj, victim, nobj, tobj, crashes, leases

vars == << fs, foreignObj, classified, ownerLive, sawLive, seenRec, crashed, 
           live, holding, checked, writing, pendingUnlink, checkStale, 
           writeStale, lostLock, landedAfterTakeover, recoveredAfterCrash, 
           tornRead, hostCrashChangedLock, touchedUncertain, refusedOk, 
           refused, pc, stack, keep, obj_, got, obj, robj, victim, nobj, tobj, 
           crashes, leases >>

ProcSet == (Owners) \cup (PlainRuns) \cup (Recoverers) \cup (Cleanups) \cup (Breakers) \cup {"env"}

Init == (* Global variables *)
        /\ fs \in {FsInit, FsWith(P, LockName, Foreign)}
        /\ foreignObj = At(fs, P, LockName)
        /\ classified = [p \in Procs |-> "none"]
        /\ ownerLive = [p \in Procs |-> "none"]
        /\ sawLive = [p \in Procs |-> FALSE]
        /\ seenRec = [p \in Procs |-> EmptyFile]
        /\ crashed = [p \in Procs |-> FALSE]
        /\ live = [p \in Procs |-> FALSE]
        /\ holding = [p \in Procs |-> FALSE]
        /\ checked = [p \in Procs |-> FALSE]
        /\ writing = [p \in Procs |-> FALSE]
        /\ pendingUnlink = [p \in Procs |-> NoObj]
        /\ checkStale = [p \in Procs |-> TRUE]
        /\ writeStale = [p \in Procs |-> TRUE]
        /\ lostLock = [p \in Procs |-> FALSE]
        /\ landedAfterTakeover = FALSE
        /\ recoveredAfterCrash = FALSE
        /\ tornRead = FALSE
        /\ hostCrashChangedLock = FALSE
        /\ touchedUncertain = FALSE
        /\ refusedOk = [p \in Procs |-> FALSE]
        /\ refused = [p \in Procs |-> "none"]
        (* Procedure Classify *)
        /\ keep = [ self \in ProcSet |-> defaultInitValue]
        /\ obj_ = [ self \in ProcSet |-> 0]
        /\ got = [ self \in ProcSet |-> FALSE]
        (* Procedure Acquire *)
        /\ obj = [ self \in ProcSet |-> 0]
        (* Procedure Recover *)
        /\ robj = [ self \in ProcSet |-> 0]
        /\ victim = [ self \in ProcSet |-> NoProc]
        /\ nobj = [ self \in ProcSet |-> 0]
        (* Procedure TakeOver *)
        /\ tobj = [ self \in ProcSet |-> 0]
        (* Process env *)
        /\ crashes = 0
        /\ leases = 0
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Owners -> "own_start"
                                        [] self \in PlainRuns -> "plain_start"
                                        [] self \in Recoverers -> "rec_start"
                                        [] self \in Cleanups -> "clean_start"
                                        [] self \in Breakers -> "brk_start"
                                        [] self = "env" -> "env_loop"]

S240_1_open(self) == /\ pc[self] = "S240_1_open"
                     /\ IF crashed[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = "classify_crashed"]
                                /\ UNCHANGED << fs, classified, seenRec, stack, 
                                                keep, obj_, got >>
                           ELSE /\ LET r == FsOpen(fs, P, LockName, self, TRUE) IN
                                     IF r.ok
                                        THEN /\ fs' = r.fs
                                             /\ obj_' = [obj_ EXCEPT ![self] = r.val]
                                             /\ pc' = [pc EXCEPT ![self] = "S240_1_trylock"]
                                             /\ UNCHANGED << classified, 
                                                             seenRec, stack, 
                                                             keep, got >>
                                        ELSE /\ classified' = [classified EXCEPT ![self] = "empty"]
                                             /\ seenRec' = [seenRec EXCEPT ![self] = EmptyFile]
                                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                             /\ obj_' = [obj_ EXCEPT ![self] = Head(stack[self]).obj_]
                                             /\ got' = [got EXCEPT ![self] = Head(stack[self]).got]
                                             /\ keep' = [keep EXCEPT ![self] = Head(stack[self]).keep]
                                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                             /\ fs' = fs
                     /\ UNCHANGED << foreignObj, ownerLive, sawLive, crashed, 
                                     live, holding, checked, writing, 
                                     pendingUnlink, checkStale, writeStale, 
                                     lostLock, landedAfterTakeover, 
                                     recoveredAfterCrash, tornRead, 
                                     hostCrashChangedLock, touchedUncertain, 
                                     refusedOk, refused, obj, robj, victim, 
                                     nobj, tobj, crashes, leases >>

S240_1_trylock(self) == /\ pc[self] = "S240_1_trylock"
                        /\ IF crashed[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "classify_crashed"]
                                   /\ UNCHANGED << fs, got >>
                              ELSE /\ LET r == FsTryLock(fs, self, obj_[self]) IN
                                        /\ got' = [got EXCEPT ![self] = r.ok]
                                        /\ IF r.ok
                                              THEN /\ fs' = r.fs
                                              ELSE /\ TRUE
                                                   /\ fs' = fs
                                   /\ pc' = [pc EXCEPT ![self] = "S240_1_read"]
                        /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                        sawLive, seenRec, crashed, live, 
                                        holding, checked, writing, 
                                        pendingUnlink, checkStale, writeStale, 
                                        lostLock, landedAfterTakeover, 
                                        recoveredAfterCrash, tornRead, 
                                        hostCrashChangedLock, touchedUncertain, 
                                        refusedOk, refused, stack, keep, obj_, 
                                        obj, robj, victim, nobj, tobj, crashes, 
                                        leases >>

S240_1_read(self) == /\ pc[self] = "S240_1_read"
                     /\ IF crashed[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = "classify_crashed"]
                                /\ UNCHANGED << classified, ownerLive, sawLive, 
                                                seenRec, tornRead >>
                           ELSE /\ LET seen == fs.content[obj_[self]] IN
                                     /\ seenRec' = [seenRec EXCEPT ![self] = seen]
                                     /\ IF seen = Torn
                                           THEN /\ tornRead' = TRUE
                                           ELSE /\ TRUE
                                                /\ UNCHANGED tornRead
                                     /\ IF (seen = Torn /\ ~SEED_TORN_AS_FOREIGN) \/ seen = EmptyFile
                                           THEN /\ classified' = [classified EXCEPT ![self] = "uncertain"]
                                                /\ ownerLive' = [ownerLive EXCEPT ![self] = "none"]
                                                /\ sawLive' = [sawLive EXCEPT ![self] = FALSE]
                                           ELSE /\ IF seen = Foreign \/ (SEED_TORN_AS_FOREIGN /\ seen = Torn)
                                                      THEN /\ classified' = [classified EXCEPT ![self] = "foreign"]
                                                           /\ ownerLive' = [ownerLive EXCEPT ![self] = "none"]
                                                           /\ sawLive' = [sawLive EXCEPT ![self] = FALSE]
                                                      ELSE /\ \E alive \in  IF ~got[self] /\ LockCapability \in {"strong", "remote"} THEN {"live"}
                                                                           ELSE IF crashed[seen.op] THEN {"dead", "uncertain"}
                                                                           ELSE {"live", "uncertain"}:
                                                                /\ ownerLive' = [ownerLive EXCEPT ![self] = alive]
                                                                /\ sawLive' = [sawLive EXCEPT ![self] = alive = "live"]
                                                                /\ IF seen.kind = "cleanup"
                                                                      THEN /\ classified' = [classified EXCEPT ![self] = "cleanuplock"]
                                                                      ELSE /\ classified' = [classified EXCEPT ![self] = alive]
                                /\ pc' = [pc EXCEPT ![self] = "S240_1_close"]
                     /\ UNCHANGED << fs, foreignObj, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     hostCrashChangedLock, touchedUncertain, 
                                     refusedOk, refused, stack, keep, obj_, 
                                     got, obj, robj, victim, nobj, tobj, 
                                     crashes, leases >>

S240_1_close(self) == /\ pc[self] = "S240_1_close"
                      /\ IF crashed[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = "classify_crashed"]
                                 /\ UNCHANGED << fs, stack, keep, obj_, got >>
                            ELSE /\ IF ~keep[self] \/ ~Replaceable(self)
                                       THEN /\ fs' = FsClose(fs, self, obj_[self]).fs
                                       ELSE /\ TRUE
                                            /\ fs' = fs
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ obj_' = [obj_ EXCEPT ![self] = Head(stack[self]).obj_]
                                 /\ got' = [got EXCEPT ![self] = Head(stack[self]).got]
                                 /\ keep' = [keep EXCEPT ![self] = Head(stack[self]).keep]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                      sawLive, seenRec, crashed, live, holding, 
                                      checked, writing, pendingUnlink, 
                                      checkStale, writeStale, lostLock, 
                                      landedAfterTakeover, recoveredAfterCrash, 
                                      tornRead, hostCrashChangedLock, 
                                      touchedUncertain, refusedOk, refused, 
                                      obj, robj, victim, nobj, tobj, crashes, 
                                      leases >>

classify_crashed(self) == /\ pc[self] = "classify_crashed"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ obj_' = [obj_ EXCEPT ![self] = Head(stack[self]).obj_]
                          /\ got' = [got EXCEPT ![self] = Head(stack[self]).got]
                          /\ keep' = [keep EXCEPT ![self] = Head(stack[self]).keep]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << fs, foreignObj, classified, 
                                          ownerLive, sawLive, seenRec, crashed, 
                                          live, holding, checked, writing, 
                                          pendingUnlink, checkStale, 
                                          writeStale, lostLock, 
                                          landedAfterTakeover, 
                                          recoveredAfterCrash, tornRead, 
                                          hostCrashChangedLock, 
                                          touchedUncertain, refusedOk, refused, 
                                          obj, robj, victim, nobj, tobj, 
                                          crashes, leases >>

Classify(self) == S240_1_open(self) \/ S240_1_trylock(self)
                     \/ S240_1_read(self) \/ S240_1_close(self)
                     \/ classify_crashed(self)

S96_1_create(self) == /\ pc[self] = "S96_1_create"
                      /\ IF crashed[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                                 /\ UNCHANGED << fs, lostLock, refused, stack, 
                                                 obj >>
                            ELSE /\ LET r == FsCreate(fs, P, LockName, self, TRUE) IN
                                      IF r.ok
                                         THEN /\ fs' = r.fs
                                              /\ obj' = [obj EXCEPT ![self] = r.val]
                                              /\ lostLock' = [lostLock EXCEPT ![self] = FALSE]
                                              /\ pc' = [pc EXCEPT ![self] = "S96_1_dircheck"]
                                              /\ UNCHANGED << refused, stack >>
                                         ELSE /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                              /\ obj' = [obj EXCEPT ![self] = Head(stack[self]).obj]
                                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                              /\ UNCHANGED << fs, lostLock >>
                      /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                      sawLive, seenRec, crashed, live, holding, 
                                      checked, writing, pendingUnlink, 
                                      checkStale, writeStale, 
                                      landedAfterTakeover, recoveredAfterCrash, 
                                      tornRead, hostCrashChangedLock, 
                                      touchedUncertain, refusedOk, keep, obj_, 
                                      got, robj, victim, nobj, tobj, crashes, 
                                      leases >>

S96_1_dircheck(self) == /\ pc[self] = "S96_1_dircheck"
                        /\ IF crashed[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                              ELSE /\ IF FsLookup(fs, P, DirLockName)
                                         THEN /\ pc' = [pc EXCEPT ![self] = "S96_1_backoff"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock"]
                        /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                        sawLive, seenRec, crashed, live, 
                                        holding, checked, writing, 
                                        pendingUnlink, checkStale, writeStale, 
                                        lostLock, landedAfterTakeover, 
                                        recoveredAfterCrash, tornRead, 
                                        hostCrashChangedLock, touchedUncertain, 
                                        refusedOk, refused, stack, keep, obj_, 
                                        got, obj, robj, victim, nobj, tobj, 
                                        crashes, leases >>

S96_1_ownlock(self) == /\ pc[self] = "S96_1_ownlock"
                       /\ IF crashed[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                                  /\ fs' = fs
                             ELSE /\ IF LocksAvailable
                                        THEN /\ LET r == FsTryLock(fs, self, obj[self]) IN
                                                  IF r.ok
                                                     THEN /\ fs' = r.fs
                                                          /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock_verify"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock_wait"]
                                                          /\ fs' = fs
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock_verify"]
                                             /\ fs' = fs
                       /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, stack, keep, obj_, 
                                       got, obj, robj, victim, nobj, tobj, 
                                       crashes, leases >>

S96_1_ownlock_verify(self) == /\ pc[self] = "S96_1_ownlock_verify"
                              /\ IF crashed[self]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                                    ELSE /\ \E ident \in FsIdentityChoices(fs, P, LockName):
                                              IF ident # obj[self] \/ fs.content[obj[self]] # EmptyFile
                                                 THEN /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock_close"]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "S96_1_record_begin"]
                              /\ UNCHANGED << fs, foreignObj, classified, 
                                              ownerLive, sawLive, seenRec, 
                                              crashed, live, holding, checked, 
                                              writing, pendingUnlink, 
                                              checkStale, writeStale, lostLock, 
                                              landedAfterTakeover, 
                                              recoveredAfterCrash, tornRead, 
                                              hostCrashChangedLock, 
                                              touchedUncertain, refusedOk, 
                                              refused, stack, keep, obj_, got, 
                                              obj, robj, victim, nobj, tobj, 
                                              crashes, leases >>

S96_1_record_begin(self) == /\ pc[self] = "S96_1_record_begin"
                            /\ IF crashed[self]
                                  THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                                       /\ UNCHANGED << fs, holding, lostLock, 
                                                       refusedOk, refused >>
                                  ELSE /\ IF WriteFenced(self, obj[self])
                                             THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                  /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                  /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                  /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock_close"]
                                                  /\ UNCHANGED << fs, lostLock >>
                                             ELSE /\ fs' = FsWriteBegin(fs, obj[self]).fs
                                                  /\ lostLock' = MarkLost(self, obj[self])
                                                  /\ pc' = [pc EXCEPT ![self] = "S96_1_record_end"]
                                                  /\ UNCHANGED << holding, 
                                                                  refusedOk, 
                                                                  refused >>
                            /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                            sawLive, seenRec, crashed, live, 
                                            checked, writing, pendingUnlink, 
                                            checkStale, writeStale, 
                                            landedAfterTakeover, 
                                            recoveredAfterCrash, tornRead, 
                                            hostCrashChangedLock, 
                                            touchedUncertain, stack, keep, 
                                            obj_, got, obj, robj, victim, nobj, 
                                            tobj, crashes, leases >>

S96_1_record_end(self) == /\ pc[self] = "S96_1_record_end"
                          /\ IF crashed[self]
                                THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                                     /\ UNCHANGED << fs, seenRec, holding, 
                                                     checkStale, writeStale, 
                                                     lostLock, refusedOk, 
                                                     refused, stack, obj >>
                                ELSE /\ IF WriteFenced(self, obj[self])
                                           THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock_close"]
                                                /\ UNCHANGED << fs, seenRec, 
                                                                checkStale, 
                                                                writeStale, 
                                                                lostLock, 
                                                                stack, obj >>
                                           ELSE /\ fs' = FsWriteEnd(fs, obj[self], OwnRecord(self)).fs
                                                /\ lostLock' = MarkLost(self, obj[self])
                                                /\ seenRec' = [seenRec EXCEPT ![self] = OwnRecord(self)]
                                                /\ holding' = [holding EXCEPT ![self] = TRUE]
                                                /\ checkStale' = [q \in Procs |-> IF q = self THEN checkStale[q] ELSE TRUE]
                                                /\ writeStale' = [q \in Procs |-> IF q = self THEN writeStale[q] ELSE TRUE]
                                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                /\ obj' = [obj EXCEPT ![self] = Head(stack[self]).obj]
                                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                /\ UNCHANGED << refusedOk, 
                                                                refused >>
                          /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                          sawLive, crashed, live, checked, 
                                          writing, pendingUnlink, 
                                          landedAfterTakeover, 
                                          recoveredAfterCrash, tornRead, 
                                          hostCrashChangedLock, 
                                          touchedUncertain, keep, obj_, got, 
                                          robj, victim, nobj, tobj, crashes, 
                                          leases >>

S96_1_backoff(self) == /\ pc[self] = "S96_1_backoff"
                       /\ IF crashed[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                                  /\ UNCHANGED << fs, lostLock, refusedOk, 
                                                  refused, stack, obj >>
                             ELSE /\ refusedOk' = [refusedOk EXCEPT ![self] = RefusalEvidence(self)]
                                  /\ \E c \in FsUnlinkChoices:
                                       fs' = FsUnlink(fs, P, LockName, c).fs
                                  /\ lostLock' = MarkLost(self, LockObj)
                                  /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ obj' = [obj EXCEPT ![self] = Head(stack[self]).obj]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       keep, obj_, got, robj, victim, nobj, 
                                       tobj, crashes, leases >>

S96_1_ownlock_wait(self) == /\ pc[self] = "S96_1_ownlock_wait"
                            /\ IF crashed[self]
                                  THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                                  ELSE /\ \E ident \in FsIdentityChoices(fs, P, LockName):
                                            IF ident # obj[self] \/ fs.content[obj[self]] # EmptyFile
                                               THEN /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock_close"]
                                               ELSE /\ \/ /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock"]
                                                       \/ /\ pc' = [pc EXCEPT ![self] = "S96_1_ownlock_close"]
                            /\ UNCHANGED << fs, foreignObj, classified, 
                                            ownerLive, sawLive, seenRec, 
                                            crashed, live, holding, checked, 
                                            writing, pendingUnlink, checkStale, 
                                            writeStale, lostLock, 
                                            landedAfterTakeover, 
                                            recoveredAfterCrash, tornRead, 
                                            hostCrashChangedLock, 
                                            touchedUncertain, refusedOk, 
                                            refused, stack, keep, obj_, got, 
                                            obj, robj, victim, nobj, tobj, 
                                            crashes, leases >>

S96_1_ownlock_close(self) == /\ pc[self] = "S96_1_ownlock_close"
                             /\ IF crashed[self]
                                   THEN /\ pc' = [pc EXCEPT ![self] = "acquire_crashed"]
                                        /\ UNCHANGED << fs, lostLock, refused, 
                                                        stack, obj >>
                                   ELSE /\ \E c \in FsUnlinkChoices:
                                             fs' = FsClose(IF SEED_ACQUIRER_UNLINKS_BY_NAME THEN FsUnlink(fs, P, LockName, c).fs ELSE fs, self, obj[self]).fs
                                        /\ lostLock' = IF SEED_ACQUIRER_UNLINKS_BY_NAME THEN MarkLost(self, LockObj) ELSE lostLock
                                        /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                        /\ obj' = [obj EXCEPT ![self] = Head(stack[self]).obj]
                                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                             sawLive, seenRec, crashed, live, 
                                             holding, checked, writing, 
                                             pendingUnlink, checkStale, 
                                             writeStale, landedAfterTakeover, 
                                             recoveredAfterCrash, tornRead, 
                                             hostCrashChangedLock, 
                                             touchedUncertain, refusedOk, keep, 
                                             obj_, got, robj, victim, nobj, 
                                             tobj, crashes, leases >>

acquire_crashed(self) == /\ pc[self] = "acquire_crashed"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ obj' = [obj EXCEPT ![self] = Head(stack[self]).obj]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                         sawLive, seenRec, crashed, live, 
                                         holding, checked, writing, 
                                         pendingUnlink, checkStale, writeStale, 
                                         lostLock, landedAfterTakeover, 
                                         recoveredAfterCrash, tornRead, 
                                         hostCrashChangedLock, 
                                         touchedUncertain, refusedOk, refused, 
                                         keep, obj_, got, robj, victim, nobj, 
                                         tobj, crashes, leases >>

Acquire(self) == S96_1_create(self) \/ S96_1_dircheck(self)
                    \/ S96_1_ownlock(self) \/ S96_1_ownlock_verify(self)
                    \/ S96_1_record_begin(self) \/ S96_1_record_end(self)
                    \/ S96_1_backoff(self) \/ S96_1_ownlock_wait(self)
                    \/ S96_1_ownlock_close(self) \/ acquire_crashed(self)

S240_3_s1(self) == /\ pc[self] = "S240_3_s1"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                              /\ UNCHANGED << robj, victim >>
                         ELSE /\ robj' = [robj EXCEPT ![self] = LockObj]
                              /\ IF IsRecord(seenRec[self])
                                    THEN /\ victim' = [victim EXCEPT ![self] = seenRec[self].op]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED victim
                              /\ IF LockObj = NoObj \/ fs.content[LockObj] # seenRec[self]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "S240_3_restart"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "S240_3_s2"]
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, live, holding, 
                                   checked, writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, refused, stack, keep, obj_, got, 
                                   obj, nobj, tobj, crashes, leases >>

S240_3_s2(self) == /\ pc[self] = "S240_3_s2"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                              /\ UNCHANGED << fs, lostLock, touchedUncertain >>
                         ELSE /\ IF JudgedUncertain(self)
                                    THEN /\ touchedUncertain' = TRUE
                                    ELSE /\ TRUE
                                         /\ UNCHANGED touchedUncertain
                              /\ LET r == FsRenameNoReplace(fs, P, LockName, BrokenOf(self)) IN
                                   IF r.ok
                                      THEN /\ fs' = r.fs
                                           /\ lostLock' = MarkLost(self, LockObj)
                                           /\ pc' = [pc EXCEPT ![self] = "S240_3_s3"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "S240_3_restart"]
                                           /\ UNCHANGED << fs, lostLock >>
                   /\ UNCHANGED << foreignObj, classified, ownerLive, sawLive, 
                                   seenRec, crashed, live, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, refusedOk, refused, 
                                   stack, keep, obj_, got, obj, robj, victim, 
                                   nobj, tobj, crashes, leases >>

S240_3_s3(self) == /\ pc[self] = "S240_3_s3"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                         ELSE /\ \E ident \in FsIdentityChoices(fs, P, BrokenOf(self)):
                                   IF ident # robj[self] \/ fs.content[robj[self]] # seenRec[self]
                                      THEN /\ pc' = [pc EXCEPT ![self] = "S240_3_putback"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "S240_3_s4"]
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, live, holding, 
                                   checked, writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, refused, stack, keep, obj_, got, 
                                   obj, robj, victim, nobj, tobj, crashes, 
                                   leases >>

S240_3_s4(self) == /\ pc[self] = "S240_3_s4"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                              /\ UNCHANGED << fs, lostLock, nobj >>
                         ELSE /\ LET r == FsCreate(fs, P, LockName, self, TRUE) IN
                                   IF r.ok
                                      THEN /\ fs' = r.fs
                                           /\ nobj' = [nobj EXCEPT ![self] = r.val]
                                           /\ lostLock' = [lostLock EXCEPT ![self] = FALSE]
                                           /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_drop"]
                                           /\ UNCHANGED << fs, lostLock, nobj >>
                   /\ UNCHANGED << foreignObj, classified, ownerLive, sawLive, 
                                   seenRec, crashed, live, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, refused, stack, keep, obj_, got, 
                                   obj, robj, victim, tobj, crashes, leases >>

S240_3_s4_lock(self) == /\ pc[self] = "S240_3_s4_lock"
                        /\ IF crashed[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                   /\ fs' = fs
                              ELSE /\ IF LocksAvailable
                                         THEN /\ LET r == FsTryLock(fs, self, nobj[self]) IN
                                                   IF r.ok
                                                      THEN /\ fs' = r.fs
                                                           /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock_verify"]
                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock_wait"]
                                                           /\ fs' = fs
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock_verify"]
                                              /\ fs' = fs
                        /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                        sawLive, seenRec, crashed, live, 
                                        holding, checked, writing, 
                                        pendingUnlink, checkStale, writeStale, 
                                        lostLock, landedAfterTakeover, 
                                        recoveredAfterCrash, tornRead, 
                                        hostCrashChangedLock, touchedUncertain, 
                                        refusedOk, refused, stack, keep, obj_, 
                                        got, obj, robj, victim, nobj, tobj, 
                                        crashes, leases >>

S240_3_s4_lock_verify(self) == /\ pc[self] = "S240_3_s4_lock_verify"
                               /\ IF crashed[self]
                                     THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                     ELSE /\ \E ident \in FsIdentityChoices(fs, P, LockName):
                                               IF ident # nobj[self] \/ fs.content[nobj[self]] # EmptyFile
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock_close"]
                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_record_begin"]
                               /\ UNCHANGED << fs, foreignObj, classified, 
                                               ownerLive, sawLive, seenRec, 
                                               crashed, live, holding, checked, 
                                               writing, pendingUnlink, 
                                               checkStale, writeStale, 
                                               lostLock, landedAfterTakeover, 
                                               recoveredAfterCrash, tornRead, 
                                               hostCrashChangedLock, 
                                               touchedUncertain, refusedOk, 
                                               refused, stack, keep, obj_, got, 
                                               obj, robj, victim, nobj, tobj, 
                                               crashes, leases >>

S240_3_s4_record_begin(self) == /\ pc[self] = "S240_3_s4_record_begin"
                                /\ IF crashed[self]
                                      THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                           /\ UNCHANGED << fs, holding, 
                                                           lostLock, refusedOk, 
                                                           refused >>
                                      ELSE /\ IF WriteFenced(self, nobj[self])
                                                 THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                      /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                      /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                      /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock_close"]
                                                      /\ UNCHANGED << fs, 
                                                                      lostLock >>
                                                 ELSE /\ fs' = FsWriteBegin(fs, nobj[self]).fs
                                                      /\ lostLock' = MarkLost(self, nobj[self])
                                                      /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_record_end"]
                                                      /\ UNCHANGED << holding, 
                                                                      refusedOk, 
                                                                      refused >>
                                /\ UNCHANGED << foreignObj, classified, 
                                                ownerLive, sawLive, seenRec, 
                                                crashed, live, checked, 
                                                writing, pendingUnlink, 
                                                checkStale, writeStale, 
                                                landedAfterTakeover, 
                                                recoveredAfterCrash, tornRead, 
                                                hostCrashChangedLock, 
                                                touchedUncertain, stack, keep, 
                                                obj_, got, obj, robj, victim, 
                                                nobj, tobj, crashes, leases >>

S240_3_s4_record_end(self) == /\ pc[self] = "S240_3_s4_record_end"
                              /\ IF crashed[self]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                         /\ UNCHANGED << fs, seenRec, holding, 
                                                         checkStale, 
                                                         writeStale, lostLock, 
                                                         refusedOk, refused >>
                                    ELSE /\ IF WriteFenced(self, nobj[self])
                                               THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                    /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                    /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                    /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock_close"]
                                                    /\ UNCHANGED << fs, 
                                                                    seenRec, 
                                                                    checkStale, 
                                                                    writeStale, 
                                                                    lostLock >>
                                               ELSE /\ fs' = FsWriteEnd(fs, nobj[self], OwnRecord(self)).fs
                                                    /\ lostLock' = MarkLost(self, nobj[self])
                                                    /\ seenRec' = [seenRec EXCEPT ![self] = OwnRecord(self)]
                                                    /\ holding' = [holding EXCEPT ![self] = TRUE]
                                                    /\ checkStale' = [q \in Procs |-> IF q = self THEN checkStale[q] ELSE TRUE]
                                                    /\ writeStale' = [q \in Procs |-> IF q = self THEN writeStale[q] ELSE TRUE]
                                                    /\ pc' = [pc EXCEPT ![self] = "S240_3_s5"]
                                                    /\ UNCHANGED << refusedOk, 
                                                                    refused >>
                              /\ UNCHANGED << foreignObj, classified, 
                                              ownerLive, sawLive, crashed, 
                                              live, checked, writing, 
                                              pendingUnlink, 
                                              landedAfterTakeover, 
                                              recoveredAfterCrash, tornRead, 
                                              hostCrashChangedLock, 
                                              touchedUncertain, stack, keep, 
                                              obj_, got, obj, robj, victim, 
                                              nobj, tobj, crashes, leases >>

S240_3_s5(self) == /\ pc[self] = "S240_3_s5"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                              /\ UNCHANGED << fs, recoveredAfterCrash >>
                         ELSE /\ \E c \in FsUnlinkChoices:
                                   fs' = FsUnlink(fs, P, BrokenOf(self), c).fs
                              /\ IF victim[self] \in Procs
                                    THEN /\ IF crashed[victim[self]]
                                               THEN /\ recoveredAfterCrash' = TRUE
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED recoveredAfterCrash
                                    ELSE /\ TRUE
                                         /\ UNCHANGED recoveredAfterCrash
                              /\ pc' = [pc EXCEPT ![self] = "S240_3_release"]
                   /\ UNCHANGED << foreignObj, classified, ownerLive, sawLive, 
                                   seenRec, crashed, live, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   tornRead, hostCrashChangedLock, 
                                   touchedUncertain, refusedOk, refused, stack, 
                                   keep, obj_, got, obj, robj, victim, nobj, 
                                   tobj, crashes, leases >>

S240_3_s4_drop(self) == /\ pc[self] = "S240_3_s4_drop"
                        /\ IF crashed[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                   /\ UNCHANGED << fs, refused >>
                              ELSE /\ \E c \in FsUnlinkChoices:
                                        fs' = FsUnlink(fs, P, BrokenOf(self), c).fs
                                   /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                   /\ pc' = [pc EXCEPT ![self] = "S240_3_release"]
                        /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                        sawLive, seenRec, crashed, live, 
                                        holding, checked, writing, 
                                        pendingUnlink, checkStale, writeStale, 
                                        lostLock, landedAfterTakeover, 
                                        recoveredAfterCrash, tornRead, 
                                        hostCrashChangedLock, touchedUncertain, 
                                        refusedOk, stack, keep, obj_, got, obj, 
                                        robj, victim, nobj, tobj, crashes, 
                                        leases >>

S240_3_s4_lock_wait(self) == /\ pc[self] = "S240_3_s4_lock_wait"
                             /\ IF crashed[self]
                                   THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                   ELSE /\ \E ident \in FsIdentityChoices(fs, P, LockName):
                                             IF ident # nobj[self] \/ fs.content[nobj[self]] # EmptyFile
                                                THEN /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock_close"]
                                                ELSE /\ \/ /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock"]
                                                        \/ /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_lock_close"]
                             /\ UNCHANGED << fs, foreignObj, classified, 
                                             ownerLive, sawLive, seenRec, 
                                             crashed, live, holding, checked, 
                                             writing, pendingUnlink, 
                                             checkStale, writeStale, lostLock, 
                                             landedAfterTakeover, 
                                             recoveredAfterCrash, tornRead, 
                                             hostCrashChangedLock, 
                                             touchedUncertain, refusedOk, 
                                             refused, stack, keep, obj_, got, 
                                             obj, robj, victim, nobj, tobj, 
                                             crashes, leases >>

S240_3_s4_lock_close(self) == /\ pc[self] = "S240_3_s4_lock_close"
                              /\ IF crashed[self]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                         /\ UNCHANGED << fs, lostLock >>
                                    ELSE /\ \E c \in FsUnlinkChoices:
                                              fs' = FsClose(IF SEED_ACQUIRER_UNLINKS_BY_NAME THEN FsUnlink(fs, P, LockName, c).fs ELSE fs, self, nobj[self]).fs
                                         /\ lostLock' = IF SEED_ACQUIRER_UNLINKS_BY_NAME THEN MarkLost(self, LockObj) ELSE lostLock
                                         /\ pc' = [pc EXCEPT ![self] = "S240_3_s4_drop"]
                              /\ UNCHANGED << foreignObj, classified, 
                                              ownerLive, sawLive, seenRec, 
                                              crashed, live, holding, checked, 
                                              writing, pendingUnlink, 
                                              checkStale, writeStale, 
                                              landedAfterTakeover, 
                                              recoveredAfterCrash, tornRead, 
                                              hostCrashChangedLock, 
                                              touchedUncertain, refusedOk, 
                                              refused, stack, keep, obj_, got, 
                                              obj, robj, victim, nobj, tobj, 
                                              crashes, leases >>

S240_3_putback(self) == /\ pc[self] = "S240_3_putback"
                        /\ IF crashed[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                   /\ UNCHANGED << fs, refused >>
                              ELSE /\ LET r == FsRenameNoReplace(fs, P, BrokenOf(self), LockName) IN
                                        IF r.ok
                                           THEN /\ fs' = r.fs
                                           ELSE /\ TRUE
                                                /\ fs' = fs
                                   /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                   /\ pc' = [pc EXCEPT ![self] = "S240_3_release"]
                        /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                        sawLive, seenRec, crashed, live, 
                                        holding, checked, writing, 
                                        pendingUnlink, checkStale, writeStale, 
                                        lostLock, landedAfterTakeover, 
                                        recoveredAfterCrash, tornRead, 
                                        hostCrashChangedLock, touchedUncertain, 
                                        refusedOk, stack, keep, obj_, got, obj, 
                                        robj, victim, nobj, tobj, crashes, 
                                        leases >>

S240_3_restart(self) == /\ pc[self] = "S240_3_restart"
                        /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                        /\ pc' = [pc EXCEPT ![self] = "S240_3_release"]
                        /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                        sawLive, seenRec, crashed, live, 
                                        holding, checked, writing, 
                                        pendingUnlink, checkStale, writeStale, 
                                        lostLock, landedAfterTakeover, 
                                        recoveredAfterCrash, tornRead, 
                                        hostCrashChangedLock, touchedUncertain, 
                                        refusedOk, stack, keep, obj_, got, obj, 
                                        robj, victim, nobj, tobj, crashes, 
                                        leases >>

S240_3_release(self) == /\ pc[self] = "S240_3_release"
                        /\ IF crashed[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "recover_crashed"]
                                   /\ UNCHANGED << fs, stack, robj, victim, 
                                                   nobj >>
                              ELSE /\ IF robj[self] # NoObj /\ OpenBy(fs, self, robj[self])
                                         THEN /\ fs' = FsClose(fs, self, robj[self]).fs
                                         ELSE /\ TRUE
                                              /\ fs' = fs
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ robj' = [robj EXCEPT ![self] = Head(stack[self]).robj]
                                   /\ victim' = [victim EXCEPT ![self] = Head(stack[self]).victim]
                                   /\ nobj' = [nobj EXCEPT ![self] = Head(stack[self]).nobj]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                        sawLive, seenRec, crashed, live, 
                                        holding, checked, writing, 
                                        pendingUnlink, checkStale, writeStale, 
                                        lostLock, landedAfterTakeover, 
                                        recoveredAfterCrash, tornRead, 
                                        hostCrashChangedLock, touchedUncertain, 
                                        refusedOk, refused, keep, obj_, got, 
                                        obj, tobj, crashes, leases >>

recover_crashed(self) == /\ pc[self] = "recover_crashed"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ robj' = [robj EXCEPT ![self] = Head(stack[self]).robj]
                         /\ victim' = [victim EXCEPT ![self] = Head(stack[self]).victim]
                         /\ nobj' = [nobj EXCEPT ![self] = Head(stack[self]).nobj]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                         sawLive, seenRec, crashed, live, 
                                         holding, checked, writing, 
                                         pendingUnlink, checkStale, writeStale, 
                                         lostLock, landedAfterTakeover, 
                                         recoveredAfterCrash, tornRead, 
                                         hostCrashChangedLock, 
                                         touchedUncertain, refusedOk, refused, 
                                         keep, obj_, got, obj, tobj, crashes, 
                                         leases >>

Recover(self) == S240_3_s1(self) \/ S240_3_s2(self) \/ S240_3_s3(self)
                    \/ S240_3_s4(self) \/ S240_3_s4_lock(self)
                    \/ S240_3_s4_lock_verify(self)
                    \/ S240_3_s4_record_begin(self)
                    \/ S240_3_s4_record_end(self) \/ S240_3_s5(self)
                    \/ S240_3_s4_drop(self) \/ S240_3_s4_lock_wait(self)
                    \/ S240_3_s4_lock_close(self) \/ S240_3_putback(self)
                    \/ S240_3_restart(self) \/ S240_3_release(self)
                    \/ recover_crashed(self)

S240_5_s1(self) == /\ pc[self] = "S240_5_s1"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                              /\ UNCHANGED << refused, stack, tobj >>
                         ELSE /\ IF IdentityStrength # "strong" \/ (LockCapability \notin {"strong", "remote"} /\ ~SEED_NO_CAPABILITY_GATE)
                                    THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_UNCERTAIN"]
                                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                         /\ tobj' = [tobj EXCEPT ![self] = Head(stack[self]).tobj]
                                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "S240_5_s2"]
                                         /\ UNCHANGED << refused, stack, tobj >>
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, live, holding, 
                                   checked, writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, keep, obj_, got, obj, robj, 
                                   victim, nobj, crashes, leases >>

S240_5_s2(self) == /\ pc[self] = "S240_5_s2"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                              /\ UNCHANGED << fs, lostLock, refused, stack, 
                                              tobj >>
                         ELSE /\ LET r == FsOpen(fs, P, LockName, self, TRUE) IN
                                   IF r.ok
                                      THEN /\ fs' = r.fs
                                           /\ tobj' = [tobj EXCEPT ![self] = r.val]
                                           /\ lostLock' = [lostLock EXCEPT ![self] = FALSE]
                                           /\ pc' = [pc EXCEPT ![self] = "S240_5_s3"]
                                           /\ UNCHANGED << refused, stack >>
                                      ELSE /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                           /\ tobj' = [tobj EXCEPT ![self] = Head(stack[self]).tobj]
                                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                           /\ UNCHANGED << fs, lostLock >>
                   /\ UNCHANGED << foreignObj, classified, ownerLive, sawLive, 
                                   seenRec, crashed, live, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, keep, obj_, got, obj, robj, 
                                   victim, nobj, crashes, leases >>

S240_5_s3(self) == /\ pc[self] = "S240_5_s3"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                              /\ UNCHANGED << fs, refusedOk, refused >>
                         ELSE /\ IF LocksAvailable
                                    THEN /\ LET r == FsTryLock(fs, self, tobj[self]) IN
                                              IF r.ok
                                                 THEN /\ fs' = r.fs
                                                      /\ pc' = [pc EXCEPT ![self] = "S240_5_s4"]
                                                      /\ UNCHANGED << refusedOk, 
                                                                      refused >>
                                                 ELSE /\ refusedOk' = [refusedOk EXCEPT ![self] = fs.oslock[tobj[self]] # NoProc \/ RefusalEvidence(self)]
                                                      /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                      /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                                      /\ fs' = fs
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "S240_5_s4"]
                                         /\ UNCHANGED << fs, refusedOk, 
                                                         refused >>
                   /\ UNCHANGED << foreignObj, classified, ownerLive, sawLive, 
                                   seenRec, crashed, live, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   stack, keep, obj_, got, obj, robj, victim, 
                                   nobj, tobj, crashes, leases >>

S240_5_s4(self) == /\ pc[self] = "S240_5_s4"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                              /\ UNCHANGED refused
                         ELSE /\ \E ident \in FsIdentityChoices(fs, P, LockName):
                                   IF ident # tobj[self]
                                      THEN /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                           /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "S240_5_s5"]
                                           /\ UNCHANGED refused
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, live, holding, 
                                   checked, writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, stack, keep, obj_, got, obj, 
                                   robj, victim, nobj, tobj, crashes, leases >>

S240_5_s5(self) == /\ pc[self] = "S240_5_s5"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                              /\ UNCHANGED << sawLive, refusedOk, refused >>
                         ELSE /\ LET seen == fs.content[tobj[self]] IN
                                   IF IsRecord(seen) /\ seen # seenRec[self]
                                      THEN /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                           /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                           /\ UNCHANGED << sawLive, refusedOk >>
                                      ELSE /\ IF IsRecord(seen)
                                                 THEN /\ \E alive \in IF crashed[seen.op] THEN {"dead", "uncertain"} ELSE {"live", "uncertain"}:
                                                           IF alive = "live"
                                                              THEN /\ sawLive' = [sawLive EXCEPT ![self] = TRUE]
                                                                   /\ refusedOk' = [refusedOk EXCEPT ![self] = alive = "live" \/ RefusalEvidence(self)]
                                                                   /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                                   /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "S240_5_s6_seed"]
                                                                   /\ UNCHANGED << sawLive, 
                                                                                   refusedOk, 
                                                                                   refused >>
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "S240_5_s6_seed"]
                                                      /\ UNCHANGED << sawLive, 
                                                                      refusedOk, 
                                                                      refused >>
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   seenRec, crashed, live, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   stack, keep, obj_, got, obj, robj, victim, 
                                   nobj, tobj, crashes, leases >>

S240_5_s6_seed(self) == /\ pc[self] = "S240_5_s6_seed"
                        /\ IF crashed[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                                   /\ UNCHANGED << fs, refused >>
                              ELSE /\ IF SEED_RENAME_OVER_TAKEOVER
                                         THEN /\ LET r == FsCreate(fs, P, TakeoverName(self), self, TRUE) IN
                                                   IF r.ok
                                                      THEN /\ fs' = r.fs
                                                           /\ pc' = [pc EXCEPT ![self] = "S240_5_seed_write_begin"]
                                                           /\ UNCHANGED refused
                                                      ELSE /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                                           /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                                           /\ fs' = fs
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "S240_5_s6_write_begin"]
                                              /\ UNCHANGED << fs, refused >>
                        /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                        sawLive, seenRec, crashed, live, 
                                        holding, checked, writing, 
                                        pendingUnlink, checkStale, writeStale, 
                                        lostLock, landedAfterTakeover, 
                                        recoveredAfterCrash, tornRead, 
                                        hostCrashChangedLock, touchedUncertain, 
                                        refusedOk, stack, keep, obj_, got, obj, 
                                        robj, victim, nobj, tobj, crashes, 
                                        leases >>

S240_5_s6_write_begin(self) == /\ pc[self] = "S240_5_s6_write_begin"
                               /\ IF crashed[self]
                                     THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                                          /\ UNCHANGED << fs, holding, 
                                                          lostLock, refusedOk, 
                                                          refused >>
                                     ELSE /\ IF WriteFenced(self, tobj[self])
                                                THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                     /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                     /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                     /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                                     /\ UNCHANGED << fs, 
                                                                     lostLock >>
                                                ELSE /\ fs' = FsWriteBegin(fs, tobj[self]).fs
                                                     /\ lostLock' = MarkLost(self, tobj[self])
                                                     /\ pc' = [pc EXCEPT ![self] = "S240_5_s6_write_end"]
                                                     /\ UNCHANGED << holding, 
                                                                     refusedOk, 
                                                                     refused >>
                               /\ UNCHANGED << foreignObj, classified, 
                                               ownerLive, sawLive, seenRec, 
                                               crashed, live, checked, writing, 
                                               pendingUnlink, checkStale, 
                                               writeStale, landedAfterTakeover, 
                                               recoveredAfterCrash, tornRead, 
                                               hostCrashChangedLock, 
                                               touchedUncertain, stack, keep, 
                                               obj_, got, obj, robj, victim, 
                                               nobj, tobj, crashes, leases >>

S240_5_s6_write_end(self) == /\ pc[self] = "S240_5_s6_write_end"
                             /\ IF crashed[self]
                                   THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                                        /\ UNCHANGED << fs, seenRec, holding, 
                                                        lostLock, refusedOk, 
                                                        refused >>
                                   ELSE /\ IF WriteFenced(self, tobj[self])
                                              THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                   /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                   /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                   /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                                   /\ UNCHANGED << fs, seenRec, 
                                                                   lostLock >>
                                              ELSE /\ fs' = FsWriteEnd(fs, tobj[self], OwnRecord(self)).fs
                                                   /\ lostLock' = MarkLost(self, tobj[self])
                                                   /\ seenRec' = [seenRec EXCEPT ![self] = OwnRecord(self)]
                                                   /\ pc' = [pc EXCEPT ![self] = "S240_5_s6_flush"]
                                                   /\ UNCHANGED << holding, 
                                                                   refusedOk, 
                                                                   refused >>
                             /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                             sawLive, crashed, live, checked, 
                                             writing, pendingUnlink, 
                                             checkStale, writeStale, 
                                             landedAfterTakeover, 
                                             recoveredAfterCrash, tornRead, 
                                             hostCrashChangedLock, 
                                             touchedUncertain, stack, keep, 
                                             obj_, got, obj, robj, victim, 
                                             nobj, tobj, crashes, leases >>

S240_5_s6_flush(self) == /\ pc[self] = "S240_5_s6_flush"
                         /\ IF crashed[self]
                               THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                                    /\ fs' = fs
                               ELSE /\ fs' = FsFlushFile(fs, tobj[self]).fs
                                    /\ pc' = [pc EXCEPT ![self] = "S240_5_s6"]
                         /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                         sawLive, seenRec, crashed, live, 
                                         holding, checked, writing, 
                                         pendingUnlink, checkStale, writeStale, 
                                         lostLock, landedAfterTakeover, 
                                         recoveredAfterCrash, tornRead, 
                                         hostCrashChangedLock, 
                                         touchedUncertain, refusedOk, refused, 
                                         stack, keep, obj_, got, obj, robj, 
                                         victim, nobj, tobj, crashes, leases >>

S240_5_s6(self) == /\ pc[self] = "S240_5_s6"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                              /\ UNCHANGED << holding, checkStale, writeStale, 
                                              refusedOk, refused, stack, tobj >>
                         ELSE /\ \E ident \in FsIdentityChoices(fs, P, LockName):
                                   IF ident = NoObj
                                      THEN /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                           /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                           /\ UNCHANGED << holding, checkStale, 
                                                           writeStale, 
                                                           refusedOk, stack, 
                                                           tobj >>
                                      ELSE /\ IF ident # tobj[self]
                                                 THEN /\ refusedOk' = [refusedOk EXCEPT ![self] = LockObj # NoObj /\ LockObj # tobj[self]]
                                                      /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                      /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                                      /\ UNCHANGED << holding, 
                                                                      checkStale, 
                                                                      writeStale, 
                                                                      stack, 
                                                                      tobj >>
                                                 ELSE /\ holding' = [holding EXCEPT ![self] = TRUE]
                                                      /\ checkStale' = [q \in Procs |-> IF q = self THEN checkStale[q] ELSE TRUE]
                                                      /\ writeStale' = [q \in Procs |-> IF q = self THEN writeStale[q] ELSE TRUE]
                                                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                      /\ tobj' = [tobj EXCEPT ![self] = Head(stack[self]).tobj]
                                                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                      /\ UNCHANGED << refusedOk, 
                                                                      refused >>
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, live, checked, 
                                   writing, pendingUnlink, lostLock, 
                                   landedAfterTakeover, recoveredAfterCrash, 
                                   tornRead, hostCrashChangedLock, 
                                   touchedUncertain, keep, obj_, got, obj, 
                                   robj, victim, nobj, crashes, leases >>

S240_5_seed_write_begin(self) == /\ pc[self] = "S240_5_seed_write_begin"
                                 /\ IF crashed[self]
                                       THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                                            /\ UNCHANGED << fs, lostLock >>
                                       ELSE /\ fs' = FsWriteBegin(fs, At(fs, P, TakeoverName(self))).fs
                                            /\ lostLock' = MarkLost(self, At(fs', P, TakeoverName(self)))
                                            /\ pc' = [pc EXCEPT ![self] = "S240_5_seed_write_end"]
                                 /\ UNCHANGED << foreignObj, classified, 
                                                 ownerLive, sawLive, seenRec, 
                                                 crashed, live, holding, 
                                                 checked, writing, 
                                                 pendingUnlink, checkStale, 
                                                 writeStale, 
                                                 landedAfterTakeover, 
                                                 recoveredAfterCrash, tornRead, 
                                                 hostCrashChangedLock, 
                                                 touchedUncertain, refusedOk, 
                                                 refused, stack, keep, obj_, 
                                                 got, obj, robj, victim, nobj, 
                                                 tobj, crashes, leases >>

S240_5_seed_write_end(self) == /\ pc[self] = "S240_5_seed_write_end"
                               /\ IF crashed[self]
                                     THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                                          /\ UNCHANGED << fs, seenRec, 
                                                          lostLock >>
                                     ELSE /\ fs' = FsWriteEnd(fs, At(fs, P, TakeoverName(self)), OwnRecord(self)).fs
                                          /\ lostLock' = MarkLost(self, At(fs', P, TakeoverName(self)))
                                          /\ seenRec' = [seenRec EXCEPT ![self] = OwnRecord(self)]
                                          /\ pc' = [pc EXCEPT ![self] = "S240_5_seed_rename"]
                               /\ UNCHANGED << foreignObj, classified, 
                                               ownerLive, sawLive, crashed, 
                                               live, holding, checked, writing, 
                                               pendingUnlink, checkStale, 
                                               writeStale, landedAfterTakeover, 
                                               recoveredAfterCrash, tornRead, 
                                               hostCrashChangedLock, 
                                               touchedUncertain, refusedOk, 
                                               refused, stack, keep, obj_, got, 
                                               obj, robj, victim, nobj, tobj, 
                                               crashes, leases >>

S240_5_seed_rename(self) == /\ pc[self] = "S240_5_seed_rename"
                            /\ IF crashed[self]
                                  THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                                       /\ UNCHANGED << fs, holding, checkStale, 
                                                       writeStale, lostLock, 
                                                       refused, stack, tobj >>
                                  ELSE /\ LET r == FsRenameReplace(fs, P, TakeoverName(self), LockName) IN
                                            IF r.ok
                                               THEN /\ fs' = FsClose(r.fs, self, tobj[self]).fs
                                                    /\ lostLock' = MarkLost(self, LockObj)
                                                    /\ holding' = [holding EXCEPT ![self] = TRUE]
                                                    /\ checkStale' = [q \in Procs |-> IF q = self THEN checkStale[q] ELSE TRUE]
                                                    /\ writeStale' = [q \in Procs |-> IF q = self THEN writeStale[q] ELSE TRUE]
                                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                    /\ tobj' = [tobj EXCEPT ![self] = Head(stack[self]).tobj]
                                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                    /\ UNCHANGED refused
                                               ELSE /\ refused' = [refused EXCEPT ![self] = "RESTART"]
                                                    /\ pc' = [pc EXCEPT ![self] = "S240_5_close"]
                                                    /\ UNCHANGED << fs, 
                                                                    holding, 
                                                                    checkStale, 
                                                                    writeStale, 
                                                                    lostLock, 
                                                                    stack, 
                                                                    tobj >>
                            /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                            sawLive, seenRec, crashed, live, 
                                            checked, writing, pendingUnlink, 
                                            landedAfterTakeover, 
                                            recoveredAfterCrash, tornRead, 
                                            hostCrashChangedLock, 
                                            touchedUncertain, refusedOk, keep, 
                                            obj_, got, obj, robj, victim, nobj, 
                                            crashes, leases >>

S240_5_close(self) == /\ pc[self] = "S240_5_close"
                      /\ IF crashed[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = "takeover_crashed"]
                                 /\ UNCHANGED << fs, stack, tobj >>
                            ELSE /\ IF tobj[self] # NoObj /\ OpenBy(fs, self, tobj[self])
                                       THEN /\ fs' = FsClose(fs, self, tobj[self]).fs
                                       ELSE /\ TRUE
                                            /\ fs' = fs
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ tobj' = [tobj EXCEPT ![self] = Head(stack[self]).tobj]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                      sawLive, seenRec, crashed, live, holding, 
                                      checked, writing, pendingUnlink, 
                                      checkStale, writeStale, lostLock, 
                                      landedAfterTakeover, recoveredAfterCrash, 
                                      tornRead, hostCrashChangedLock, 
                                      touchedUncertain, refusedOk, refused, 
                                      keep, obj_, got, obj, robj, victim, nobj, 
                                      crashes, leases >>

takeover_crashed(self) == /\ pc[self] = "takeover_crashed"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ tobj' = [tobj EXCEPT ![self] = Head(stack[self]).tobj]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << fs, foreignObj, classified, 
                                          ownerLive, sawLive, seenRec, crashed, 
                                          live, holding, checked, writing, 
                                          pendingUnlink, checkStale, 
                                          writeStale, lostLock, 
                                          landedAfterTakeover, 
                                          recoveredAfterCrash, tornRead, 
                                          hostCrashChangedLock, 
                                          touchedUncertain, refusedOk, refused, 
                                          keep, obj_, got, obj, robj, victim, 
                                          nobj, crashes, leases >>

TakeOver(self) == S240_5_s1(self) \/ S240_5_s2(self) \/ S240_5_s3(self)
                     \/ S240_5_s4(self) \/ S240_5_s5(self)
                     \/ S240_5_s6_seed(self) \/ S240_5_s6_write_begin(self)
                     \/ S240_5_s6_write_end(self) \/ S240_5_s6_flush(self)
                     \/ S240_5_s6(self) \/ S240_5_seed_write_begin(self)
                     \/ S240_5_seed_write_end(self)
                     \/ S240_5_seed_rename(self) \/ S240_5_close(self)
                     \/ takeover_crashed(self)

S99_check(self) == /\ pc[self] = "S99_check"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "publish_crashed"]
                              /\ UNCHANGED << holding, checked, checkStale, 
                                              refusedOk, refused >>
                         ELSE /\ IF StillOwned(self)
                                    THEN /\ checked' = [checked EXCEPT ![self] = TRUE]
                                         /\ checkStale' = [checkStale EXCEPT ![self] = FALSE]
                                         /\ pc' = [pc EXCEPT ![self] = "S99_write"]
                                         /\ UNCHANGED << holding, refusedOk, 
                                                         refused >>
                                    ELSE /\ checked' = [checked EXCEPT ![self] = FALSE]
                                         /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                         /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                         /\ holding' = [holding EXCEPT ![self] = FALSE]
                                         /\ pc' = [pc EXCEPT ![self] = "S99_refuse_close"]
                                         /\ UNCHANGED checkStale
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, live, writing, 
                                   pendingUnlink, writeStale, lostLock, 
                                   landedAfterTakeover, recoveredAfterCrash, 
                                   tornRead, hostCrashChangedLock, 
                                   touchedUncertain, stack, keep, obj_, got, 
                                   obj, robj, victim, nobj, tobj, crashes, 
                                   leases >>

S99_write(self) == /\ pc[self] = "S99_write"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "publish_crashed"]
                              /\ UNCHANGED << writing, writeStale >>
                         ELSE /\ writing' = [writing EXCEPT ![self] = TRUE]
                              /\ writeStale' = [writeStale EXCEPT ![self] = FALSE]
                              /\ pc' = [pc EXCEPT ![self] = "S240_5_inflight_lands"]
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, live, holding, 
                                   checked, pendingUnlink, checkStale, 
                                   lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, refused, stack, keep, obj_, got, 
                                   obj, robj, victim, nobj, tobj, crashes, 
                                   leases >>

S240_5_inflight_lands(self) == /\ pc[self] = "S240_5_inflight_lands"
                               /\ IF crashed[self]
                                     THEN /\ pc' = [pc EXCEPT ![self] = "publish_crashed"]
                                          /\ UNCHANGED << writing, writeStale, 
                                                          landedAfterTakeover >>
                                     ELSE /\ IF writeStale[self]
                                                THEN /\ landedAfterTakeover' = TRUE
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED landedAfterTakeover
                                          /\ writing' = [writing EXCEPT ![self] = FALSE]
                                          /\ writeStale' = [writeStale EXCEPT ![self] = TRUE]
                                          /\ pc' = [pc EXCEPT ![self] = "S99_release_check"]
                               /\ UNCHANGED << fs, foreignObj, classified, 
                                               ownerLive, sawLive, seenRec, 
                                               crashed, live, holding, checked, 
                                               pendingUnlink, checkStale, 
                                               lostLock, recoveredAfterCrash, 
                                               tornRead, hostCrashChangedLock, 
                                               touchedUncertain, refusedOk, 
                                               refused, stack, keep, obj_, got, 
                                               obj, robj, victim, nobj, tobj, 
                                               crashes, leases >>

S99_release_check(self) == /\ pc[self] = "S99_release_check"
                           /\ IF crashed[self]
                                 THEN /\ pc' = [pc EXCEPT ![self] = "publish_crashed"]
                                      /\ UNCHANGED << holding, checked, 
                                                      checkStale, refusedOk, 
                                                      refused >>
                                 ELSE /\ checked' = [checked EXCEPT ![self] = FALSE]
                                      /\ checkStale' = [checkStale EXCEPT ![self] = TRUE]
                                      /\ IF ~StillOwned(self)
                                            THEN /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                 /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                 /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                 /\ pc' = [pc EXCEPT ![self] = "S99_refuse_close"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "S99_release"]
                                                 /\ UNCHANGED << holding, 
                                                                 refusedOk, 
                                                                 refused >>
                           /\ UNCHANGED << fs, foreignObj, classified, 
                                           ownerLive, sawLive, seenRec, 
                                           crashed, live, writing, 
                                           pendingUnlink, writeStale, lostLock, 
                                           landedAfterTakeover, 
                                           recoveredAfterCrash, tornRead, 
                                           hostCrashChangedLock, 
                                           touchedUncertain, stack, keep, obj_, 
                                           got, obj, robj, victim, nobj, tobj, 
                                           crashes, leases >>

S99_release(self) == /\ pc[self] = "S99_release"
                     /\ IF crashed[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = "publish_crashed"]
                                /\ UNCHANGED << holding, pendingUnlink >>
                           ELSE /\ holding' = [holding EXCEPT ![self] = FALSE]
                                /\ pendingUnlink' = [pendingUnlink EXCEPT ![self] = LockObj]
                                /\ pc' = [pc EXCEPT ![self] = "S99_release_lands"]
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, checked, 
                                     writing, checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     stack, keep, obj_, got, obj, robj, victim, 
                                     nobj, tobj, crashes, leases >>

S99_release_lands(self) == /\ pc[self] = "S99_release_lands"
                           /\ IF crashed[self]
                                 THEN /\ pc' = [pc EXCEPT ![self] = "publish_crashed"]
                                      /\ UNCHANGED << fs, pendingUnlink, 
                                                      lostLock >>
                                 ELSE /\ \E c \in FsUnlinkChoices:
                                           fs' = LandUnlink(fs, self, c)
                                      /\ lostLock' = (IF pendingUnlink[self] # NoObj /\ LockObj # NoObj THEN MarkLost(self, LockObj) ELSE lostLock)
                                      /\ pendingUnlink' = [pendingUnlink EXCEPT ![self] = NoObj]
                                      /\ pc' = [pc EXCEPT ![self] = "S99_close"]
                           /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                           sawLive, seenRec, crashed, live, 
                                           holding, checked, writing, 
                                           checkStale, writeStale, 
                                           landedAfterTakeover, 
                                           recoveredAfterCrash, tornRead, 
                                           hostCrashChangedLock, 
                                           touchedUncertain, refusedOk, 
                                           refused, stack, keep, obj_, got, 
                                           obj, robj, victim, nobj, tobj, 
                                           crashes, leases >>

S99_close(self) == /\ pc[self] = "S99_close"
                   /\ IF crashed[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "publish_crashed"]
                              /\ UNCHANGED << fs, stack >>
                         ELSE /\ fs' = FsCloseAll(fs, self)
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << foreignObj, classified, ownerLive, sawLive, 
                                   seenRec, crashed, live, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, refused, keep, obj_, got, obj, 
                                   robj, victim, nobj, tobj, crashes, leases >>

S99_refuse_close(self) == /\ pc[self] = "S99_refuse_close"
                          /\ IF crashed[self]
                                THEN /\ pc' = [pc EXCEPT ![self] = "publish_crashed"]
                                     /\ UNCHANGED << fs, stack >>
                                ELSE /\ fs' = FsCloseAll(fs, self)
                                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                          sawLive, seenRec, crashed, live, 
                                          holding, checked, writing, 
                                          pendingUnlink, checkStale, 
                                          writeStale, lostLock, 
                                          landedAfterTakeover, 
                                          recoveredAfterCrash, tornRead, 
                                          hostCrashChangedLock, 
                                          touchedUncertain, refusedOk, refused, 
                                          keep, obj_, got, obj, robj, victim, 
                                          nobj, tobj, crashes, leases >>

publish_crashed(self) == /\ pc[self] = "publish_crashed"
                         /\ checked' = [checked EXCEPT ![self] = FALSE]
                         /\ checkStale' = [checkStale EXCEPT ![self] = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                         sawLive, seenRec, crashed, live, 
                                         holding, writing, pendingUnlink, 
                                         writeStale, lostLock, 
                                         landedAfterTakeover, 
                                         recoveredAfterCrash, tornRead, 
                                         hostCrashChangedLock, 
                                         touchedUncertain, refusedOk, refused, 
                                         keep, obj_, got, obj, robj, victim, 
                                         nobj, tobj, crashes, leases >>

Publish(self) == S99_check(self) \/ S99_write(self)
                    \/ S240_5_inflight_lands(self)
                    \/ S99_release_check(self) \/ S99_release(self)
                    \/ S99_release_lands(self) \/ S99_close(self)
                    \/ S99_refuse_close(self) \/ publish_crashed(self)

own_start(self) == /\ pc[self] = "own_start"
                   /\ IF LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE
                         THEN /\ refused' = [refused EXCEPT ![self] = "REMOTE_LOCK_UNSAFE"]
                              /\ pc' = [pc EXCEPT ![self] = "own_end"]
                              /\ UNCHANGED << live, stack, obj >>
                         ELSE /\ live' = [live EXCEPT ![self] = TRUE]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Acquire",
                                                                       pc        |->  "own_publish",
                                                                       obj       |->  obj[self] ] >>
                                                                   \o stack[self]]
                              /\ obj' = [obj EXCEPT ![self] = 0]
                              /\ pc' = [pc EXCEPT ![self] = "S96_1_create"]
                              /\ UNCHANGED refused
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, keep, obj_, got, robj, victim, 
                                   nobj, tobj, crashes, leases >>

own_publish(self) == /\ pc[self] = "own_publish"
                     /\ IF ~crashed[self] /\ holding[self]
                           THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Publish",
                                                                         pc        |->  "own_end" ] >>
                                                                     \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "S99_check"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "own_end"]
                                /\ stack' = stack
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     keep, obj_, got, obj, robj, victim, nobj, 
                                     tobj, crashes, leases >>

own_end(self) == /\ pc[self] = "own_end"
                 /\ live' = [live EXCEPT ![self] = FALSE]
                 /\ lostLock' = [lostLock EXCEPT ![self] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                 sawLive, seenRec, crashed, holding, checked, 
                                 writing, pendingUnlink, checkStale, 
                                 writeStale, landedAfterTakeover, 
                                 recoveredAfterCrash, tornRead, 
                                 hostCrashChangedLock, touchedUncertain, 
                                 refusedOk, refused, stack, keep, obj_, got, 
                                 obj, robj, victim, nobj, tobj, crashes, 
                                 leases >>

own(self) == own_start(self) \/ own_publish(self) \/ own_end(self)

plain_start(self) == /\ pc[self] = "plain_start"
                     /\ IF LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE
                           THEN /\ refused' = [refused EXCEPT ![self] = "REMOTE_LOCK_UNSAFE"]
                                /\ pc' = [pc EXCEPT ![self] = "plain_end"]
                                /\ UNCHANGED << live, stack, keep, obj_, got >>
                           ELSE /\ live' = [live EXCEPT ![self] = TRUE]
                                /\ /\ keep' = [keep EXCEPT ![self] = FALSE]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Classify",
                                                                            pc        |->  "S21_1_decide",
                                                                            obj_      |->  obj_[self],
                                                                            got       |->  got[self],
                                                                            keep      |->  keep[self] ] >>
                                                                        \o stack[self]]
                                /\ obj_' = [obj_ EXCEPT ![self] = 0]
                                /\ got' = [got EXCEPT ![self] = FALSE]
                                /\ pc' = [pc EXCEPT ![self] = "S240_1_open"]
                                /\ UNCHANGED refused
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, obj, robj, 
                                     victim, nobj, tobj, crashes, leases >>

S21_1_decide(self) == /\ pc[self] = "S21_1_decide"
                      /\ IF crashed[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = "plain_end"]
                                 /\ UNCHANGED << refusedOk, refused >>
                            ELSE /\ refusedOk' = [refusedOk EXCEPT ![self] = RefusalEvidence(self)]
                                 /\ IF classified[self] = "empty"
                                       THEN /\ pc' = [pc EXCEPT ![self] = "plain_acquire"]
                                            /\ UNCHANGED refused
                                       ELSE /\ IF Replaceable(self) /\ classified[self] = "cleanuplock"
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "plain_recover"]
                                                       /\ UNCHANGED refused
                                                  ELSE /\ IF classified[self] = "live" \/ (SEED_DEAD_AS_BUSY /\ classified[self] = "dead")
                                                             THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                             ELSE /\ IF classified[self] = "uncertain" \/ ownerLive[self] = "uncertain"
                                                                        THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_UNCERTAIN"]
                                                                        ELSE /\ IF classified[self] = "foreign"
                                                                                   THEN /\ refused' = [refused EXCEPT ![self] = "CONTROL_PLANE_NAMESPACE_CONFLICT"]
                                                                                   ELSE /\ IF classified[self] = "cleanuplock"
                                                                                              THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                                                              ELSE /\ refused' = [refused EXCEPT ![self] = "RESUMABLE_OPERATION_EXISTS"]
                                                       /\ pc' = [pc EXCEPT ![self] = "S21_1_refused"]
                      /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                      sawLive, seenRec, crashed, live, holding, 
                                      checked, writing, pendingUnlink, 
                                      checkStale, writeStale, lostLock, 
                                      landedAfterTakeover, recoveredAfterCrash, 
                                      tornRead, hostCrashChangedLock, 
                                      touchedUncertain, stack, keep, obj_, got, 
                                      obj, robj, victim, nobj, tobj, crashes, 
                                      leases >>

S21_1_refused(self) == /\ pc[self] = "S21_1_refused"
                       /\ pc' = [pc EXCEPT ![self] = "plain_end"]
                       /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, stack, keep, obj_, 
                                       got, obj, robj, victim, nobj, tobj, 
                                       crashes, leases >>

plain_recover(self) == /\ pc[self] = "plain_recover"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Recover",
                                                                pc        |->  "plain_recovered",
                                                                robj      |->  robj[self],
                                                                victim    |->  victim[self],
                                                                nobj      |->  nobj[self] ] >>
                                                            \o stack[self]]
                       /\ robj' = [robj EXCEPT ![self] = 0]
                       /\ victim' = [victim EXCEPT ![self] = NoProc]
                       /\ nobj' = [nobj EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "S240_3_s1"]
                       /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, keep, obj_, got, 
                                       obj, tobj, crashes, leases >>

plain_recovered(self) == /\ pc[self] = "plain_recovered"
                         /\ IF ~crashed[self] /\ holding[self]
                               THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Publish",
                                                                             pc        |->  "plain_recovered_done" ] >>
                                                                         \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "S99_check"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "plain_recovered_done"]
                                    /\ stack' = stack
                         /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                         sawLive, seenRec, crashed, live, 
                                         holding, checked, writing, 
                                         pendingUnlink, checkStale, writeStale, 
                                         lostLock, landedAfterTakeover, 
                                         recoveredAfterCrash, tornRead, 
                                         hostCrashChangedLock, 
                                         touchedUncertain, refusedOk, refused, 
                                         keep, obj_, got, obj, robj, victim, 
                                         nobj, tobj, crashes, leases >>

plain_recovered_done(self) == /\ pc[self] = "plain_recovered_done"
                              /\ pc' = [pc EXCEPT ![self] = "plain_end"]
                              /\ UNCHANGED << fs, foreignObj, classified, 
                                              ownerLive, sawLive, seenRec, 
                                              crashed, live, holding, checked, 
                                              writing, pendingUnlink, 
                                              checkStale, writeStale, lostLock, 
                                              landedAfterTakeover, 
                                              recoveredAfterCrash, tornRead, 
                                              hostCrashChangedLock, 
                                              touchedUncertain, refusedOk, 
                                              refused, stack, keep, obj_, got, 
                                              obj, robj, victim, nobj, tobj, 
                                              crashes, leases >>

plain_acquire(self) == /\ pc[self] = "plain_acquire"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Acquire",
                                                                pc        |->  "plain_publish",
                                                                obj       |->  obj[self] ] >>
                                                            \o stack[self]]
                       /\ obj' = [obj EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "S96_1_create"]
                       /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, keep, obj_, got, 
                                       robj, victim, nobj, tobj, crashes, 
                                       leases >>

plain_publish(self) == /\ pc[self] = "plain_publish"
                       /\ IF ~crashed[self] /\ holding[self]
                             THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Publish",
                                                                           pc        |->  "plain_end" ] >>
                                                                       \o stack[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "S99_check"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "plain_end"]
                                  /\ stack' = stack
                       /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, keep, obj_, got, 
                                       obj, robj, victim, nobj, tobj, crashes, 
                                       leases >>

plain_end(self) == /\ pc[self] = "plain_end"
                   /\ live' = [live EXCEPT ![self] = FALSE]
                   /\ lostLock' = [lostLock EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, refused, stack, keep, obj_, got, 
                                   obj, robj, victim, nobj, tobj, crashes, 
                                   leases >>

plain(self) == plain_start(self) \/ S21_1_decide(self)
                  \/ S21_1_refused(self) \/ plain_recover(self)
                  \/ plain_recovered(self) \/ plain_recovered_done(self)
                  \/ plain_acquire(self) \/ plain_publish(self)
                  \/ plain_end(self)

rec_start(self) == /\ pc[self] = "rec_start"
                   /\ IF LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE
                         THEN /\ refused' = [refused EXCEPT ![self] = "REMOTE_LOCK_UNSAFE"]
                              /\ pc' = [pc EXCEPT ![self] = "rec_end"]
                              /\ UNCHANGED << live, stack, keep, obj_, got >>
                         ELSE /\ live' = [live EXCEPT ![self] = TRUE]
                              /\ /\ keep' = [keep EXCEPT ![self] = TRUE]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Classify",
                                                                          pc        |->  "rec_decide",
                                                                          obj_      |->  obj_[self],
                                                                          got       |->  got[self],
                                                                          keep      |->  keep[self] ] >>
                                                                      \o stack[self]]
                              /\ obj_' = [obj_ EXCEPT ![self] = 0]
                              /\ got' = [got EXCEPT ![self] = FALSE]
                              /\ pc' = [pc EXCEPT ![self] = "S240_1_open"]
                              /\ UNCHANGED refused
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, obj, robj, victim, nobj, tobj, 
                                   crashes, leases >>

rec_decide(self) == /\ pc[self] = "rec_decide"
                    /\ IF crashed[self]
                          THEN /\ pc' = [pc EXCEPT ![self] = "rec_end"]
                               /\ UNCHANGED << refusedOk, refused >>
                          ELSE /\ refusedOk' = [refusedOk EXCEPT ![self] = RefusalEvidence(self)]
                               /\ IF Replaceable(self)
                                     THEN /\ pc' = [pc EXCEPT ![self] = "rec_recover"]
                                          /\ UNCHANGED refused
                                     ELSE /\ IF classified[self] = "empty"
                                                THEN /\ pc' = [pc EXCEPT ![self] = "rec_acquire"]
                                                     /\ UNCHANGED refused
                                                ELSE /\ IF classified[self] = "uncertain" \/ ownerLive[self] = "uncertain"
                                                           THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_UNCERTAIN"]
                                                           ELSE /\ IF classified[self] = "foreign"
                                                                      THEN /\ refused' = [refused EXCEPT ![self] = "CONTROL_PLANE_NAMESPACE_CONFLICT"]
                                                                      ELSE /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                     /\ pc' = [pc EXCEPT ![self] = "rec_refused"]
                    /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                    sawLive, seenRec, crashed, live, holding, 
                                    checked, writing, pendingUnlink, 
                                    checkStale, writeStale, lostLock, 
                                    landedAfterTakeover, recoveredAfterCrash, 
                                    tornRead, hostCrashChangedLock, 
                                    touchedUncertain, stack, keep, obj_, got, 
                                    obj, robj, victim, nobj, tobj, crashes, 
                                    leases >>

rec_refused(self) == /\ pc[self] = "rec_refused"
                     /\ pc' = [pc EXCEPT ![self] = "rec_end"]
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     stack, keep, obj_, got, obj, robj, victim, 
                                     nobj, tobj, crashes, leases >>

rec_recover(self) == /\ pc[self] = "rec_recover"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Recover",
                                                              pc        |->  "rec_publish",
                                                              robj      |->  robj[self],
                                                              victim    |->  victim[self],
                                                              nobj      |->  nobj[self] ] >>
                                                          \o stack[self]]
                     /\ robj' = [robj EXCEPT ![self] = 0]
                     /\ victim' = [victim EXCEPT ![self] = NoProc]
                     /\ nobj' = [nobj EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "S240_3_s1"]
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     keep, obj_, got, obj, tobj, crashes, 
                                     leases >>

rec_publish(self) == /\ pc[self] = "rec_publish"
                     /\ IF ~crashed[self] /\ holding[self]
                           THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Publish",
                                                                         pc        |->  "rec_publish_done" ] >>
                                                                     \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "S99_check"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "rec_publish_done"]
                                /\ stack' = stack
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     keep, obj_, got, obj, robj, victim, nobj, 
                                     tobj, crashes, leases >>

rec_publish_done(self) == /\ pc[self] = "rec_publish_done"
                          /\ pc' = [pc EXCEPT ![self] = "rec_end"]
                          /\ UNCHANGED << fs, foreignObj, classified, 
                                          ownerLive, sawLive, seenRec, crashed, 
                                          live, holding, checked, writing, 
                                          pendingUnlink, checkStale, 
                                          writeStale, lostLock, 
                                          landedAfterTakeover, 
                                          recoveredAfterCrash, tornRead, 
                                          hostCrashChangedLock, 
                                          touchedUncertain, refusedOk, refused, 
                                          stack, keep, obj_, got, obj, robj, 
                                          victim, nobj, tobj, crashes, leases >>

rec_acquire(self) == /\ pc[self] = "rec_acquire"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Acquire",
                                                              pc        |->  "rec_acquired",
                                                              obj       |->  obj[self] ] >>
                                                          \o stack[self]]
                     /\ obj' = [obj EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "S96_1_create"]
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     keep, obj_, got, robj, victim, nobj, tobj, 
                                     crashes, leases >>

rec_acquired(self) == /\ pc[self] = "rec_acquired"
                      /\ IF ~crashed[self] /\ holding[self]
                            THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Publish",
                                                                          pc        |->  "rec_end" ] >>
                                                                      \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "S99_check"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "rec_end"]
                                 /\ stack' = stack
                      /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                      sawLive, seenRec, crashed, live, holding, 
                                      checked, writing, pendingUnlink, 
                                      checkStale, writeStale, lostLock, 
                                      landedAfterTakeover, recoveredAfterCrash, 
                                      tornRead, hostCrashChangedLock, 
                                      touchedUncertain, refusedOk, refused, 
                                      keep, obj_, got, obj, robj, victim, nobj, 
                                      tobj, crashes, leases >>

rec_end(self) == /\ pc[self] = "rec_end"
                 /\ live' = [live EXCEPT ![self] = FALSE]
                 /\ lostLock' = [lostLock EXCEPT ![self] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                 sawLive, seenRec, crashed, holding, checked, 
                                 writing, pendingUnlink, checkStale, 
                                 writeStale, landedAfterTakeover, 
                                 recoveredAfterCrash, tornRead, 
                                 hostCrashChangedLock, touchedUncertain, 
                                 refusedOk, refused, stack, keep, obj_, got, 
                                 obj, robj, victim, nobj, tobj, crashes, 
                                 leases >>

rec(self) == rec_start(self) \/ rec_decide(self) \/ rec_refused(self)
                \/ rec_recover(self) \/ rec_publish(self)
                \/ rec_publish_done(self) \/ rec_acquire(self)
                \/ rec_acquired(self) \/ rec_end(self)

clean_start(self) == /\ pc[self] = "clean_start"
                     /\ IF LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE
                           THEN /\ refused' = [refused EXCEPT ![self] = "REMOTE_LOCK_UNSAFE"]
                                /\ pc' = [pc EXCEPT ![self] = "clean_end"]
                                /\ UNCHANGED << live, stack, keep, obj_, got >>
                           ELSE /\ live' = [live EXCEPT ![self] = TRUE]
                                /\ /\ keep' = [keep EXCEPT ![self] = TRUE]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Classify",
                                                                            pc        |->  "S251_1_classify",
                                                                            obj_      |->  obj_[self],
                                                                            got       |->  got[self],
                                                                            keep      |->  keep[self] ] >>
                                                                        \o stack[self]]
                                /\ obj_' = [obj_ EXCEPT ![self] = 0]
                                /\ got' = [got EXCEPT ![self] = FALSE]
                                /\ pc' = [pc EXCEPT ![self] = "S240_1_open"]
                                /\ UNCHANGED refused
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, obj, robj, 
                                     victim, nobj, tobj, crashes, leases >>

S251_1_classify(self) == /\ pc[self] = "S251_1_classify"
                         /\ IF crashed[self]
                               THEN /\ pc' = [pc EXCEPT ![self] = "clean_end"]
                                    /\ UNCHANGED << refusedOk, refused >>
                               ELSE /\ refusedOk' = [refusedOk EXCEPT ![self] = RefusalEvidence(self)]
                                    /\ IF Replaceable(self)
                                          THEN /\ pc' = [pc EXCEPT ![self] = "clean_recover"]
                                               /\ UNCHANGED refused
                                          ELSE /\ IF classified[self] = "empty"
                                                     THEN /\ refused' = [refused EXCEPT ![self] = "NOTHING_TO_CLEAN"]
                                                     ELSE /\ IF classified[self] = "foreign"
                                                                THEN /\ refused' = [refused EXCEPT ![self] = "CONTROL_PLANE_NAMESPACE_CONFLICT"]
                                                                ELSE /\ IF classified[self] = "uncertain" \/ ownerLive[self] = "uncertain"
                                                                           THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_UNCERTAIN"]
                                                                           ELSE /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                               /\ pc' = [pc EXCEPT ![self] = "clean_refused"]
                         /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                         sawLive, seenRec, crashed, live, 
                                         holding, checked, writing, 
                                         pendingUnlink, checkStale, writeStale, 
                                         lostLock, landedAfterTakeover, 
                                         recoveredAfterCrash, tornRead, 
                                         hostCrashChangedLock, 
                                         touchedUncertain, stack, keep, obj_, 
                                         got, obj, robj, victim, nobj, tobj, 
                                         crashes, leases >>

clean_refused(self) == /\ pc[self] = "clean_refused"
                       /\ pc' = [pc EXCEPT ![self] = "clean_end"]
                       /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, stack, keep, obj_, 
                                       got, obj, robj, victim, nobj, tobj, 
                                       crashes, leases >>

clean_recover(self) == /\ pc[self] = "clean_recover"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Recover",
                                                                pc        |->  "S251_1_delete",
                                                                robj      |->  robj[self],
                                                                victim    |->  victim[self],
                                                                nobj      |->  nobj[self] ] >>
                                                            \o stack[self]]
                       /\ robj' = [robj EXCEPT ![self] = 0]
                       /\ victim' = [victim EXCEPT ![self] = NoProc]
                       /\ nobj' = [nobj EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "S240_3_s1"]
                       /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, keep, obj_, got, 
                                       obj, tobj, crashes, leases >>

S251_1_delete(self) == /\ pc[self] = "S251_1_delete"
                       /\ IF crashed[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "clean_end"]
                                  /\ UNCHANGED << fs, holding, lostLock >>
                             ELSE /\ IF holding[self]
                                        THEN /\ holding' = [holding EXCEPT ![self] = FALSE]
                                             /\ \E c \in FsUnlinkChoices:
                                                  fs' = FsUnlink(fs, P, LockName, c).fs
                                             /\ lostLock' = MarkLost(self, LockObj)
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << fs, holding, 
                                                             lostLock >>
                                  /\ pc' = [pc EXCEPT ![self] = "S251_1_close"]
                       /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       checked, writing, pendingUnlink, 
                                       checkStale, writeStale, 
                                       landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, stack, keep, obj_, 
                                       got, obj, robj, victim, nobj, tobj, 
                                       crashes, leases >>

S251_1_close(self) == /\ pc[self] = "S251_1_close"
                      /\ IF crashed[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = "clean_end"]
                                 /\ fs' = fs
                            ELSE /\ IF LockObj # NoObj /\ OpenBy(fs, self, LockObj)
                                       THEN /\ fs' = FsClose(fs, self, LockObj).fs
                                       ELSE /\ TRUE
                                            /\ fs' = fs
                                 /\ pc' = [pc EXCEPT ![self] = "clean_end"]
                      /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                      sawLive, seenRec, crashed, live, holding, 
                                      checked, writing, pendingUnlink, 
                                      checkStale, writeStale, lostLock, 
                                      landedAfterTakeover, recoveredAfterCrash, 
                                      tornRead, hostCrashChangedLock, 
                                      touchedUncertain, refusedOk, refused, 
                                      stack, keep, obj_, got, obj, robj, 
                                      victim, nobj, tobj, crashes, leases >>

clean_end(self) == /\ pc[self] = "clean_end"
                   /\ live' = [live EXCEPT ![self] = FALSE]
                   /\ lostLock' = [lostLock EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, refused, stack, keep, obj_, got, 
                                   obj, robj, victim, nobj, tobj, crashes, 
                                   leases >>

clean(self) == clean_start(self) \/ S251_1_classify(self)
                  \/ clean_refused(self) \/ clean_recover(self)
                  \/ S251_1_delete(self) \/ S251_1_close(self)
                  \/ clean_end(self)

brk_start(self) == /\ pc[self] = "brk_start"
                   /\ IF LockCapability = "weak" /\ ~SEED_NO_CAPABILITY_GATE
                         THEN /\ refused' = [refused EXCEPT ![self] = "REMOTE_LOCK_UNSAFE"]
                              /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                              /\ UNCHANGED << live, stack, keep, obj_, got >>
                         ELSE /\ live' = [live EXCEPT ![self] = TRUE]
                              /\ /\ keep' = [keep EXCEPT ![self] = TRUE]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Classify",
                                                                          pc        |->  "S21_1_restart_decide",
                                                                          obj_      |->  obj_[self],
                                                                          got       |->  got[self],
                                                                          keep      |->  keep[self] ] >>
                                                                      \o stack[self]]
                              /\ obj_' = [obj_ EXCEPT ![self] = 0]
                              /\ got' = [got EXCEPT ![self] = FALSE]
                              /\ pc' = [pc EXCEPT ![self] = "S240_1_open"]
                              /\ UNCHANGED refused
                   /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                   sawLive, seenRec, crashed, holding, checked, 
                                   writing, pendingUnlink, checkStale, 
                                   writeStale, lostLock, landedAfterTakeover, 
                                   recoveredAfterCrash, tornRead, 
                                   hostCrashChangedLock, touchedUncertain, 
                                   refusedOk, obj, robj, victim, nobj, tobj, 
                                   crashes, leases >>

S21_1_restart_decide(self) == /\ pc[self] = "S21_1_restart_decide"
                              /\ IF crashed[self]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                                         /\ UNCHANGED << refusedOk, refused >>
                                    ELSE /\ refusedOk' = [refusedOk EXCEPT ![self] = RefusalEvidence(self)]
                                         /\ IF Replaceable(self)
                                               THEN /\ pc' = [pc EXCEPT ![self] = "brk_recover"]
                                                    /\ UNCHANGED refused
                                               ELSE /\ IF classified[self] = "empty"
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "brk_acquire"]
                                                               /\ UNCHANGED refused
                                                          ELSE /\ IF classified[self] = "uncertain"
                                                                     THEN /\ IF SEED_MOVE_ASIDE_FOR_UNCERTAIN
                                                                                THEN /\ pc' = [pc EXCEPT ![self] = "brk_recover"]
                                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "brk_takeover"]
                                                                          /\ UNCHANGED refused
                                                                     ELSE /\ IF ownerLive[self] = "uncertain"
                                                                                THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_UNCERTAIN"]
                                                                                ELSE /\ IF classified[self] = "foreign"
                                                                                           THEN /\ refused' = [refused EXCEPT ![self] = "CONTROL_PLANE_NAMESPACE_CONFLICT"]
                                                                                           ELSE /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                                          /\ pc' = [pc EXCEPT ![self] = "brk_refused"]
                              /\ UNCHANGED << fs, foreignObj, classified, 
                                              ownerLive, sawLive, seenRec, 
                                              crashed, live, holding, checked, 
                                              writing, pendingUnlink, 
                                              checkStale, writeStale, lostLock, 
                                              landedAfterTakeover, 
                                              recoveredAfterCrash, tornRead, 
                                              hostCrashChangedLock, 
                                              touchedUncertain, stack, keep, 
                                              obj_, got, obj, robj, victim, 
                                              nobj, tobj, crashes, leases >>

brk_refused(self) == /\ pc[self] = "brk_refused"
                     /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     stack, keep, obj_, got, obj, robj, victim, 
                                     nobj, tobj, crashes, leases >>

brk_takeover(self) == /\ pc[self] = "brk_takeover"
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "TakeOver",
                                                               pc        |->  "brk_took_over",
                                                               tobj      |->  tobj[self] ] >>
                                                           \o stack[self]]
                      /\ tobj' = [tobj EXCEPT ![self] = 0]
                      /\ pc' = [pc EXCEPT ![self] = "S240_5_s1"]
                      /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                      sawLive, seenRec, crashed, live, holding, 
                                      checked, writing, pendingUnlink, 
                                      checkStale, writeStale, lostLock, 
                                      landedAfterTakeover, recoveredAfterCrash, 
                                      tornRead, hostCrashChangedLock, 
                                      touchedUncertain, refusedOk, refused, 
                                      keep, obj_, got, obj, robj, victim, nobj, 
                                      crashes, leases >>

brk_took_over(self) == /\ pc[self] = "brk_took_over"
                       /\ pc' = [pc EXCEPT ![self] = "S21_1_s3"]
                       /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                       sawLive, seenRec, crashed, live, 
                                       holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       recoveredAfterCrash, tornRead, 
                                       hostCrashChangedLock, touchedUncertain, 
                                       refusedOk, refused, stack, keep, obj_, 
                                       got, obj, robj, victim, nobj, tobj, 
                                       crashes, leases >>

brk_recover(self) == /\ pc[self] = "brk_recover"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Recover",
                                                              pc        |->  "S21_1_s3",
                                                              robj      |->  robj[self],
                                                              victim    |->  victim[self],
                                                              nobj      |->  nobj[self] ] >>
                                                          \o stack[self]]
                     /\ robj' = [robj EXCEPT ![self] = 0]
                     /\ victim' = [victim EXCEPT ![self] = NoProc]
                     /\ nobj' = [nobj EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "S240_3_s1"]
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     keep, obj_, got, obj, tobj, crashes, 
                                     leases >>

S21_1_s3(self) == /\ pc[self] = "S21_1_s3"
                  /\ IF crashed[self] \/ ~holding[self]
                        THEN /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                             /\ UNCHANGED << holding, refusedOk, refused >>
                        ELSE /\ IF ~StillOwned(self)
                                   THEN /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                        /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                        /\ holding' = [holding EXCEPT ![self] = FALSE]
                                        /\ pc' = [pc EXCEPT ![self] = "S21_1_s3_refuse_close"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "S21_1_s5_write_begin"]
                                        /\ UNCHANGED << holding, refusedOk, 
                                                        refused >>
                  /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                  sawLive, seenRec, crashed, live, checked, 
                                  writing, pendingUnlink, checkStale, 
                                  writeStale, lostLock, landedAfterTakeover, 
                                  recoveredAfterCrash, tornRead, 
                                  hostCrashChangedLock, touchedUncertain, 
                                  stack, keep, obj_, got, obj, robj, victim, 
                                  nobj, tobj, crashes, leases >>

S21_1_s5_write_begin(self) == /\ pc[self] = "S21_1_s5_write_begin"
                              /\ IF crashed[self]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                                         /\ UNCHANGED << fs, holding, lostLock, 
                                                         refusedOk, refused >>
                                    ELSE /\ IF WriteFenced(self, HandleObj(self))
                                               THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                    /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                    /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                    /\ pc' = [pc EXCEPT ![self] = "S21_1_s3_refuse_close"]
                                                    /\ UNCHANGED << fs, 
                                                                    lostLock >>
                                               ELSE /\ fs' = FsWriteBegin(IF SEED_RESTART_RELEASES THEN FsUnlock(fs, self, HandleObj(self)).fs ELSE fs,
                                                                          HandleObj(self)).fs
                                                    /\ lostLock' = MarkLost(self, HandleObj(self))
                                                    /\ pc' = [pc EXCEPT ![self] = "S21_1_s5_write_end"]
                                                    /\ UNCHANGED << holding, 
                                                                    refusedOk, 
                                                                    refused >>
                              /\ UNCHANGED << foreignObj, classified, 
                                              ownerLive, sawLive, seenRec, 
                                              crashed, live, checked, writing, 
                                              pendingUnlink, checkStale, 
                                              writeStale, landedAfterTakeover, 
                                              recoveredAfterCrash, tornRead, 
                                              hostCrashChangedLock, 
                                              touchedUncertain, stack, keep, 
                                              obj_, got, obj, robj, victim, 
                                              nobj, tobj, crashes, leases >>

S21_1_s5_write_end(self) == /\ pc[self] = "S21_1_s5_write_end"
                            /\ IF crashed[self]
                                  THEN /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                                       /\ UNCHANGED << fs, holding, lostLock, 
                                                       refusedOk, refused >>
                                  ELSE /\ IF WriteFenced(self, HandleObj(self))
                                             THEN /\ refused' = [refused EXCEPT ![self] = "TARGET_LOCK_BUSY"]
                                                  /\ refusedOk' = [refusedOk EXCEPT ![self] = lostLock[self]]
                                                  /\ holding' = [holding EXCEPT ![self] = FALSE]
                                                  /\ pc' = [pc EXCEPT ![self] = "S21_1_s3_refuse_close"]
                                                  /\ UNCHANGED << fs, lostLock >>
                                             ELSE /\ fs' = FsWriteEnd(fs, HandleObj(self), OwnRecord(self)).fs
                                                  /\ lostLock' = MarkLost(self, HandleObj(self))
                                                  /\ pc' = [pc EXCEPT ![self] = "brk_publish"]
                                                  /\ UNCHANGED << holding, 
                                                                  refusedOk, 
                                                                  refused >>
                            /\ UNCHANGED << foreignObj, classified, ownerLive, 
                                            sawLive, seenRec, crashed, live, 
                                            checked, writing, pendingUnlink, 
                                            checkStale, writeStale, 
                                            landedAfterTakeover, 
                                            recoveredAfterCrash, tornRead, 
                                            hostCrashChangedLock, 
                                            touchedUncertain, stack, keep, 
                                            obj_, got, obj, robj, victim, nobj, 
                                            tobj, crashes, leases >>

brk_publish(self) == /\ pc[self] = "brk_publish"
                     /\ IF ~crashed[self] /\ holding[self]
                           THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Publish",
                                                                         pc        |->  "brk_publish_done" ] >>
                                                                     \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "S99_check"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "brk_publish_done"]
                                /\ stack' = stack
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     keep, obj_, got, obj, robj, victim, nobj, 
                                     tobj, crashes, leases >>

brk_publish_done(self) == /\ pc[self] = "brk_publish_done"
                          /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                          /\ UNCHANGED << fs, foreignObj, classified, 
                                          ownerLive, sawLive, seenRec, crashed, 
                                          live, holding, checked, writing, 
                                          pendingUnlink, checkStale, 
                                          writeStale, lostLock, 
                                          landedAfterTakeover, 
                                          recoveredAfterCrash, tornRead, 
                                          hostCrashChangedLock, 
                                          touchedUncertain, refusedOk, refused, 
                                          stack, keep, obj_, got, obj, robj, 
                                          victim, nobj, tobj, crashes, leases >>

brk_acquire(self) == /\ pc[self] = "brk_acquire"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Acquire",
                                                              pc        |->  "brk_acquired",
                                                              obj       |->  obj[self] ] >>
                                                          \o stack[self]]
                     /\ obj' = [obj EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "S96_1_create"]
                     /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                     sawLive, seenRec, crashed, live, holding, 
                                     checked, writing, pendingUnlink, 
                                     checkStale, writeStale, lostLock, 
                                     landedAfterTakeover, recoveredAfterCrash, 
                                     tornRead, hostCrashChangedLock, 
                                     touchedUncertain, refusedOk, refused, 
                                     keep, obj_, got, robj, victim, nobj, tobj, 
                                     crashes, leases >>

brk_acquired(self) == /\ pc[self] = "brk_acquired"
                      /\ IF ~crashed[self] /\ holding[self]
                            THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Publish",
                                                                          pc        |->  "brk_acquired_done" ] >>
                                                                      \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "S99_check"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "brk_acquired_done"]
                                 /\ stack' = stack
                      /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                      sawLive, seenRec, crashed, live, holding, 
                                      checked, writing, pendingUnlink, 
                                      checkStale, writeStale, lostLock, 
                                      landedAfterTakeover, recoveredAfterCrash, 
                                      tornRead, hostCrashChangedLock, 
                                      touchedUncertain, refusedOk, refused, 
                                      keep, obj_, got, obj, robj, victim, nobj, 
                                      tobj, crashes, leases >>

brk_acquired_done(self) == /\ pc[self] = "brk_acquired_done"
                           /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                           /\ UNCHANGED << fs, foreignObj, classified, 
                                           ownerLive, sawLive, seenRec, 
                                           crashed, live, holding, checked, 
                                           writing, pendingUnlink, checkStale, 
                                           writeStale, lostLock, 
                                           landedAfterTakeover, 
                                           recoveredAfterCrash, tornRead, 
                                           hostCrashChangedLock, 
                                           touchedUncertain, refusedOk, 
                                           refused, stack, keep, obj_, got, 
                                           obj, robj, victim, nobj, tobj, 
                                           crashes, leases >>

S21_1_s3_refuse_close(self) == /\ pc[self] = "S21_1_s3_refuse_close"
                               /\ IF crashed[self]
                                     THEN /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                                          /\ fs' = fs
                                     ELSE /\ fs' = FsCloseAll(fs, self)
                                          /\ pc' = [pc EXCEPT ![self] = "brk_end"]
                               /\ UNCHANGED << foreignObj, classified, 
                                               ownerLive, sawLive, seenRec, 
                                               crashed, live, holding, checked, 
                                               writing, pendingUnlink, 
                                               checkStale, writeStale, 
                                               lostLock, landedAfterTakeover, 
                                               recoveredAfterCrash, tornRead, 
                                               hostCrashChangedLock, 
                                               touchedUncertain, refusedOk, 
                                               refused, stack, keep, obj_, got, 
                                               obj, robj, victim, nobj, tobj, 
                                               crashes, leases >>

brk_end(self) == /\ pc[self] = "brk_end"
                 /\ live' = [live EXCEPT ![self] = FALSE]
                 /\ lostLock' = [lostLock EXCEPT ![self] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << fs, foreignObj, classified, ownerLive, 
                                 sawLive, seenRec, crashed, holding, checked, 
                                 writing, pendingUnlink, checkStale, 
                                 writeStale, landedAfterTakeover, 
                                 recoveredAfterCrash, tornRead, 
                                 hostCrashChangedLock, touchedUncertain, 
                                 refusedOk, refused, stack, keep, obj_, got, 
                                 obj, robj, victim, nobj, tobj, crashes, 
                                 leases >>

brk(self) == brk_start(self) \/ S21_1_restart_decide(self)
                \/ brk_refused(self) \/ brk_takeover(self)
                \/ brk_took_over(self) \/ brk_recover(self)
                \/ S21_1_s3(self) \/ S21_1_s5_write_begin(self)
                \/ S21_1_s5_write_end(self) \/ brk_publish(self)
                \/ brk_publish_done(self) \/ brk_acquire(self)
                \/ brk_acquired(self) \/ brk_acquired_done(self)
                \/ S21_1_s3_refuse_close(self) \/ brk_end(self)

env_loop == /\ pc["env"] = "env_loop"
            /\ IF crashes < MaxCrashes \/ leases < MaxLeaseExpiries
                  THEN /\ \/ /\ crashes < MaxCrashes
                             /\ \E p \in {q \in Procs : live[q] /\ ~crashed[q]}:
                                  \E land \in BOOLEAN:
                                    \E c \in FsUnlinkChoices:
                                      /\ fs' = FsProcCrash(LandUnlink(fs, IF land THEN p ELSE NoProc, c), p)
                                      /\ lostLock' = [ (IF land /\ pendingUnlink[p] # NoObj /\ LockObj # NoObj
                                                        THEN MarkLost(p, LockObj) ELSE lostLock) EXCEPT ![p] = FALSE ]
                                      /\ landedAfterTakeover' = (landedAfterTakeover \/ (land /\ writing[p] /\ writeStale[p]))
                                      /\ writing' = [writing EXCEPT ![p] = FALSE]
                                      /\ pendingUnlink' = [pendingUnlink EXCEPT ![p] = NoObj]
                                      /\ crashed' = [crashed EXCEPT ![p] = TRUE]
                                      /\ checked' = [checked EXCEPT ![p] = FALSE]
                                      /\ checkStale' = [checkStale EXCEPT ![p] = TRUE]
                                      /\ writeStale' = [writeStale EXCEPT ![p] = TRUE]
                                      /\ holding' = [holding EXCEPT ![p] = FALSE]
                                      /\ crashes' = crashes + 1
                             /\ pc' = [pc EXCEPT !["env"] = "env_loop"]
                             /\ UNCHANGED <<hostCrashChangedLock, leases>>
                          \/ /\ HostCrashes /\ crashes < MaxCrashes
                             /\ \E lander \in {NoProc} \cup {q \in Procs : live[q]}:
                                  \E c \in FsUnlinkChoices:
                                    \E pick \in HostCrashPicks(LandUnlink(fs, lander, c)):
                                      \E dirs \in HostCrashDirs:
                                        /\ hostCrashChangedLock' = (hostCrashChangedLock \/ At(FsHostCrash(LandUnlink(fs, lander, c), pick, dirs), P, LockName) # At(LandUnlink(fs, lander, c), P, LockName))
                                        /\ fs' = FsHostCrash(LandUnlink(fs, lander, c), pick, dirs)
                             /\ crashed' = [q \in Procs |-> IF live[q] THEN TRUE ELSE crashed[q]]
                             /\ writing' = [q \in Procs |-> IF live[q] THEN FALSE ELSE writing[q]]
                             /\ pendingUnlink' = [q \in Procs |-> IF live[q] THEN NoObj ELSE pendingUnlink[q]]
                             /\ checked' = [q \in Procs |-> IF live[q] THEN FALSE ELSE checked[q]]
                             /\ checkStale' = [q \in Procs |-> IF live[q] THEN TRUE ELSE checkStale[q]]
                             /\ lostLock' = [q \in Procs |-> IF live[q] THEN FALSE ELSE lostLock[q]]
                             /\ writeStale' = [q \in Procs |-> IF live[q] THEN TRUE ELSE writeStale[q]]
                             /\ holding' = [q \in Procs |-> IF live[q] THEN FALSE ELSE holding[q]]
                             /\ crashes' = crashes + 1
                             /\ pc' = [pc EXCEPT !["env"] = "env_loop"]
                             /\ UNCHANGED <<landedAfterTakeover, leases>>
                          \/ /\ LockCapability = "remote" /\ leases < MaxLeaseExpiries
                             /\ \E o \in {x \in Objs : fs.oslock[x] # NoProc /\ live[fs.oslock[x]] /\ ~crashed[fs.oslock[x]]}:
                                  /\ lostLock' = [lostLock EXCEPT ![fs.oslock[o]] = TRUE]
                                  /\ fs' = FsLeaseExpiry(fs, o).fs
                                  /\ leases' = leases + 1
                             /\ pc' = [pc EXCEPT !["env"] = "env_loop"]
                             /\ UNCHANGED <<crashed, holding, checked, writing, pendingUnlink, checkStale, writeStale, landedAfterTakeover, hostCrashChangedLock, crashes>>
                          \/ /\ pc' = [pc EXCEPT !["env"] = "env_done"]
                             /\ UNCHANGED <<fs, crashed, holding, checked, writing, pendingUnlink, checkStale, writeStale, lostLock, landedAfterTakeover, hostCrashChangedLock, crashes, leases>>
                  ELSE /\ pc' = [pc EXCEPT !["env"] = "env_done"]
                       /\ UNCHANGED << fs, crashed, holding, checked, writing, 
                                       pendingUnlink, checkStale, writeStale, 
                                       lostLock, landedAfterTakeover, 
                                       hostCrashChangedLock, crashes, leases >>
            /\ UNCHANGED << foreignObj, classified, ownerLive, sawLive, 
                            seenRec, live, recoveredAfterCrash, tornRead, 
                            touchedUncertain, refusedOk, refused, stack, keep, 
                            obj_, got, obj, robj, victim, nobj, tobj >>

env_done == /\ pc["env"] = "env_done"
            /\ TRUE
            /\ pc' = [pc EXCEPT !["env"] = "Done"]
            /\ UNCHANGED << fs, foreignObj, classified, ownerLive, sawLive, 
                            seenRec, crashed, live, holding, checked, writing, 
                            pendingUnlink, checkStale, writeStale, lostLock, 
                            landedAfterTakeover, recoveredAfterCrash, tornRead, 
                            hostCrashChangedLock, touchedUncertain, refusedOk, 
                            refused, stack, keep, obj_, got, obj, robj, victim, 
                            nobj, tobj, crashes, leases >>

env == env_loop \/ env_done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == env
           \/ (\E self \in ProcSet:  \/ Classify(self) \/ Acquire(self)
                                     \/ Recover(self) \/ TakeOver(self)
                                     \/ Publish(self))
           \/ (\E self \in Owners: own(self))
           \/ (\E self \in PlainRuns: plain(self))
           \/ (\E self \in Recoverers: rec(self))
           \/ (\E self \in Cleanups: clean(self))
           \/ (\E self \in Breakers: brk(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Owners : WF_vars(own(self)) /\ WF_vars(Acquire(self)) /\ WF_vars(Publish(self))
        /\ \A self \in PlainRuns : /\ WF_vars(plain(self))
                                   /\ WF_vars(Classify(self))
                                   /\ WF_vars(Recover(self))
                                   /\ WF_vars(Publish(self))
                                   /\ WF_vars(Acquire(self))
        /\ \A self \in Recoverers : /\ WF_vars(rec(self))
                                    /\ WF_vars(Classify(self))
                                    /\ WF_vars(Recover(self))
                                    /\ WF_vars(Publish(self))
                                    /\ WF_vars(Acquire(self))
        /\ \A self \in Cleanups : WF_vars(clean(self)) /\ WF_vars(Classify(self)) /\ WF_vars(Recover(self))
        /\ \A self \in Breakers : /\ WF_vars(brk(self))
                                  /\ WF_vars(Classify(self))
                                  /\ WF_vars(TakeOver(self))
                                  /\ WF_vars(Recover(self))
                                  /\ WF_vars(Publish(self))
                                  /\ WF_vars(Acquire(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* ------------------------------------------------------------------------------------------
\* Properties (design Section 7).
\*
\* Safety invariants hold in every reachable state and are checked in the scenario's `check` run.
\* Reachability is proved two ways: a step a label performs is proved by that label's TLC coverage
\* count (design Section 4), and the two facts no single label states - a read that found a torn
\* record, and a replaced lock that a crash had left - keep a ghost flag and are checked as witnesses
\* in their own small run without `-continue`, which stops at the first violation and prints one
\* trace. To get a trace for any other path, re-run the configuration with that witness as an
\* invariant and no `-continue`.

\* The filesystem model's own assumptions (FsModel.tla), so a simplification there cannot pass
\* unnoticed.
FsOk == FsInvariants(fs)

\* Every object's content is one of the forms the protocol knows, so a classifier's judgement table
\* covers every case it can meet (`Classifiable`, Section 7).
Classifiable == \A o \in Objs : fs.content[o] = NoContent \/ fs.content[o] \in Contents

\* For a target, at most one process is inside a publishing step whose last Section 99 check passed, or has
\* a publishing write in flight. Tenure generations (owner ruling for plan 3, 2026-09-15): a new lock tenure -
\* a create, a recovery or a takeover that stands - makes every other process's last check and issued write stale. As the spec stands, the one exception
\* is a call already started before a later tenure began (240.5: "a filesystem call it had already started can
\* still complete"). FIX_REMOTE_LEASE_SPEC models the amendments the open finding calls for: a process whose
\* check passed in an earlier generation is no longer counted (the check-to-call window, however the lock was
\* lost), and Section 99's check also tries the lock (Relock).
Superseded(p) == IF FIX_REMOTE_LEASE_SPEC THEN checkStale[p] ELSE writing[p] /\ writeStale[p]
SingleWriter == Cardinality({p \in Procs : (checked[p] \/ writing[p]) /\ ~Superseded(p)}) <= 1

\* A process without `--break-lock` never removes, renames, or overwrites a lock it classified as
\* uncertain, and creates a lock only at an empty lock path (Section 7).
PlainNeverOwnsUncertain == ~touchedUncertain

\* A `Foreign` object at a lock path is never written, renamed, or deleted (Section 7): the one an initial
\* state holds is still the object at the lock path and still holds Foreign. A state predicate, so no
\* misplaced ghost can make it vacuous.
ForeignUntouched == foreignObj # NoObj => LockObj = foreignObj /\ fs.content[foreignObj] = Foreign

\* A REGRESSION GUARD, not a liveness check. TARGET_LOCK_BUSY means the target's lock is held, not that
\* its recorded owner is alive (240.2): a held OS-native lock cannot tell the owner from another
\* invocation inspecting or recovering it, so no refusal-time check can establish owner liveness on
\* that path. What this catches is a refusal with nothing behind it - a decision table that refuses
\* BUSY for a lock it judged dead, or a Section 99 check (S99_check, S99_release_check, S21_1_s3) refusing with
\* no cause: such a refusal is justified only by the ghost lostLock, set when another process's write, unlink,
\* rename or replacement hit the lock file this process holds, or its lease lapsed (owner ruling for plan 3,
\* 2026-09-15). The other refusing labels record the evidence of RefusalEvidence. The
\* refusing label records its evidence because the refusal may be reported after what it saw has changed: the
\* refusal rests on what the classifier observed, not on a re-read.
RefusalJustified == \A p \in Procs : refused[p] = "TARGET_LOCK_BUSY" => refusedOk[p]

\* The ghost witnesses, for the witness runs.
NeverTornRead == ~tornRead
\* A write issued in an earlier tenure generation landed after a later tenure began (240.5; remote scenarios).
NeverInflightLandedAfterTakeover == ~landedAfterTakeover
\* A process passed its Section 99 check, so SingleWriter's ghost is set (design Section 7).
NeverChecked == \A p \in Procs : ~checked[p]
NeverRecoveredAfterCrash == ~recoveredAfterCrash
\* A host crash changed which object the lock path names: an unflushed create, move-aside or removal
\* was undone. Label coverage cannot show this, because the host crash shares `env_loop` with the
\* process crash (design Section 11).
NeverHostCrashChangedLock == ~hostCrashChangedLock

\* ------------------------------------------------------------------------------------------
\* Temporal properties (design Section 7). A configuration that checks one lists exactly one
\* PROPERTY, because TLC reports a temporal violation without naming the property it belongs to.

\* Nothing more can go wrong: the environment has stopped, or has spent every crash and every lease
\* expiry it has.
EnvQuiet == pc["env"] \in {"env_done", "Done"} \/ (crashes = MaxCrashes /\ leases = MaxLeaseExpiries)

\* Some actor entitled to replace a dead lock (240.3, 251.1) has not started yet and has not been
\* killed, so it will still classify what is at the lock path. A PlainRun is not one: a plain rerun
\* refuses a dead operation's lock with RESUMABLE_OPERATION_EXISTS (21.1).
PendingMover == \E p \in Recoverers \cup Cleanups :
                    /\ ~crashed[p]
                    /\ pc[p] \in {"rec_start", "clean_start"}

\* An actor reported that it could not establish the owner was dead. 240.4 preserves such a lock, so
\* leaving it in place is the protocol working, not failing.
UncertainReported == \E p \in Recoverers \cup Cleanups : refused[p] = "TARGET_LOCK_UNCERTAIN"

\* A lock left behind by an owner that died does not stay there, PROVIDED someone is left to act on it
\* and nothing more can go wrong: while no further crash can occur and an entitled actor has yet to
\* run, the lock is eventually replaced or removed, or an actor reports it cannot tell the owner is
\* dead (design Section 7). Without those conditions the property is false in every
\* model whose actors all finish, because the last crash can always fall after the last actor has
\* acted: measured, and that counterexample is why they are here.
DeadLockEventuallyCleared ==
    [](DeadOwnerLock /\ EnvQuiet /\ PendingMover => <>(~DeadOwnerLock \/ UncertainReported))

\* The witness for that property's antecedent. Its run must stop with this violated, which is what
\* stops the liveness run from passing over a state space that never reaches the case it is about.
NeverDeadLockWithPendingMover == ~(DeadOwnerLock /\ EnvQuiet /\ PendingMover)

\* A lock whose owner no reader can establish: the file at the lock path holds no readable record (torn,
\* or created and not yet written). Only a --break-lock takeover clears one (240.4, 240.5).
UncertainLock == LockObj # NoObj /\ fs.content[LockObj] \in {Torn, EmptyFile}

\* A Breaker has not started yet and has not been killed, so it will still classify the lock.
PendingBreaker == \E p \in Breakers : ~crashed[p] /\ pc[p] = "brk_start"

\* A Breaker was refused because the lock was held (240.5 step 3 or later). RefusalJustified guards that
\* the refusal had its evidence, so this outcome cannot hide a refusal with nothing behind it.
BreakerReportedBusy == \E p \in Breakers : refused[p] = "TARGET_LOCK_BUSY"

\* The same promise for an uncertain lock (design Section 7): while nothing more can go wrong and a
\* Breaker has yet to run, an uncertain lock does not stay, or a Breaker was refused because something
\* held it. Measured (plan 3): the last Breaker can meet a backing-off acquirer holding the torn lock for
\* a few steps; the lock then stays until the next --break-lock, which the owner accepted.
UncertainLockEventuallyCleared ==
    [](UncertainLock /\ EnvQuiet /\ PendingBreaker => <>(~UncertainLock \/ BreakerReportedBusy))

\* Its antecedent's witness, which keeps the liveness run from passing vacuously.
NeverUncertainLockWithPendingBreaker == ~(UncertainLock /\ EnvQuiet /\ PendingBreaker)
====
