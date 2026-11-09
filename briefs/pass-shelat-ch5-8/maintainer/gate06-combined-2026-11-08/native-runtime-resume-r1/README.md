# Native continuation proposal r1 — unexecuted

Source `a495f3953afff46ad5dec2d29ac8a7f55bd8ae37`, unchanged own `oleans-r1` tree and PFR config4d1a. The311-line coordinator has not been imported/executed. It imports the reviewed64b native module only when Root invokes main, reuses its checking/source/package/cleanup helpers, and never edits that engine, old R1, prep/config, library source or package cache. Native work remains Root-owned.

```
python3 -I .lake/ps-maintainer/gate06-combined-20261108/native-runtime-resume-r1/continue_native.py bootstrap
python3 -I .lake/ps-maintainer/gate06-combined-20261108/native-runtime-resume-r1/continue_native.py local
```

Outputs are fresh `native-bootstrap-resume-r1/` and `native-local-resume-r1/`. The successful bootstrap aggregate has phase **`bootstrap-continuation`**. It is a new result, never `native-bootstrap-r1/RESULT.json`. The later host guard needs a separate reviewed version bound to this new successful aggregate. Tiny instance controls may run between phases with ordinary PATH, preserving all pinned sources/objects and evidence.

## Exact interrupted input and adoption

`R1-FINGERPRINTS.json` binds all21 original R1 files, including STOP and all three attempts. R1 was frozen separately at the parent's records `b95ac87db149322d6ba807e0349bd307b8e67536` with interruption archive SHA83616e332c0d397f80b480e65a9df3841fd390eae183a4b615e713b17cfdb529. The two reused successes are:

* CacheProbe:385 imports, rc0, one complete cache EOF, source/object/tool/tree/PATH/prerequisite data checked.
* First PFR module, `PFR.Mathlib.MeasureTheory.Constructions.Pi`: rc0, exact source/object/direct import context checked.

Kernel is retained as an **interrupted failure**: rc−15, zero Lean diagnostics, unchanged source/dependencies, exact HOST_COLLISION with foreign PGID45821, and no output object. Its failed output is never adopted. Native raw headers, child commands/session IDs, footers, start/end receipts, source/tool/config/PATH hashes, diagnostics/RSS, current objects and prerequisite hashes are independently checked before adoption and again at final reconciliation. R1's complete non-PFR external-object snapshot must still match, as must the437 copied objects and146 historical Mathlib hashes. No old success is inferred merely from rc0 or object existence.

## Per-call evidence and host-only retry

Every delegated64b check gets a new `calls/<ordinal>/` directory, its own isolated engine attempts list, and a `COORDINATOR.json` binding engine/coordinator hashes and idle policy. The aggregate append-only `attempt-ledger.jsonl` retains all three R1 attempts and all new native/deferred attempts. Partial prelaunch directories and failed logs are never reused or overwritten.

Only the exact engine RuntimeError HOST_COLLISION representation, with recognized foreign native processes, distinct child PGID, rc−15/−9, zero diagnostics, unchanged source/tool/dependencies and the engine's interruption-only post-validation error is retryable after native start. The exact prelaunch “Host became busy after stable-idle check” case is separately **HOST_DEFERRED_NO_NATIVE**, requiring no child/log and unchanged source/prerequisites. Source, setup, resource, signal, marker, pin, prerequisite and unrelated errors stop the phase; they are never relabeled as host interference.

The sole in-memory engine override is its wait_idle function:30 seconds of continuous idle at phase acquisition and after any observed foreign activity/collision/defer; the existing three0.25-second observations (0.5seconds) between uninterrupted own successes. This avoids adding30seconds to every one of638 checks. The64b file remains byte-identical; every native receipt still names64b, while the call metadata/aggregate names the coordinator. Existing real-time foreign-PGID monitoring, own-child-only cleanup, resource floors, ordinary PATH and PFR-only PATH separation remain in force.

A failed target may remain only as explicitly unadopted output pending its next source check. It is never entered into the validated prefix or used as a prerequisite. The unchanged checker removes that target before retry compilation. A copied reproduction target temporarily removed by an interruption is likewise excluded from prefix reliance until its exact-byte reproduction succeeds.

## Counts and final verification

Bootstrap adopts2 old successes, performs30 remaining PFR successes, one ordinary-PATH owner/identity probe and three fresh copied-object reproductions: **36 required successful checks**, of which34 are new. Including R1's interrupted Kernel, the minimum actual bootstrap history is **37 native attempts**, plus any new host interruptions or no-native deferred calls. It is never labeled36 cold successes.

Local requires the new complete bootstrap manifest and all36 current validated success contracts; it performs all638 fresh local/root/`audits/pass-shelat/Checks` checks. Warm437 + fresh638 =1075 local results. Minimum combined history is675 native attempts (674 successes plus the original interruption), with additional attempts reported dynamically. The ledger counts reused/new passes, retained collisions and no-native deferrals separately.

Final checks cover all1109 source files, all1075 local source/object/direct-local/direct-external contracts, all3637 package objects plus173 installed core leaves, full reached package-source/Git bindings,146 historical hashes, original21 R1 files and every old/new native receipt/marker. The result has explicit warm-copy and non-cold labels; it supplies no Rule10 or merge acceptance. Stopped whole continuation phases have no resume option: retain them and seek a fresh reviewed continuation if needed.

`validation.json` records14 independent read-only AST/data groups, including current hashes of both reusable objects and their direct imports. No coordinator/engine import, process simulation, native/cache command or source/object mutation was performed by the author. Root and peer review the final frozen source before launch.

**Not yet clear to merge — native and Rule10 verification pending**
