# Megafill D report

Outcome: **partial — E-Q checkpoint 1 proved; delivery not compliant**. The linear guard and the reduction to
the main query machine are proved. Checkpoints 2–7 remain open. `exists_queryTM` retains its
original admission in its own body; no new admission or admitted helper was introduced.

Proof work stops following process escalation **E-SERIAL**, described below. The final screen
then detects two prohibited new cross-file pairs (**E-DUP**). This is not a complete fill or
a compliant delivery; both findings are preserved for review.

## Queue and delivery

The queue contains one item, E-Q (`Turing.NTimeDiag.exists_queryTM`).

| Field | Value |
|---|---|
| Outcome | Partial; checkpoint 1 proved, checkpoints 2–7 open; E-SERIAL and E-DUP |
| Branch | `fill/eq-query` |
| Shared base | `ab09aa4124da9ffce36e939f652dc4bc30e6f3c5` |
| Source commit | `9d93626dadf1561c757494cfff992d1951a458e2` |
| Branch start, UTC | 2026-10-27T05:37:27.224140+00:00 |
| Item end, UTC | 2026-10-27T06:20:49.817880+00:00 |
| Final zip | `fill-eq-query.zip` |
| Final zip SHA-256 | `ecad72665bfcd0f7a5ca97a9189998812371adfb1b3b0eb31febc898dcb02124` |
| Final zip written, UTC | 2026-10-27T06:20:50.143721+00:00 |
| Checkpoint zip | `fill-eq-query-cp1.zip` |
| Checkpoint zip SHA-256 | `60d9e7c219412f5a0bca63f5f6eb3b859b6d50a954fde69a3f973419c780e4b1` |
| Checkpoint zip written, UTC | 2026-10-27T05:59:38.689114+00:00 |

Checkpoint 1 was committed and zipped separately, then delivered immediately. The final zip
contains the same source commit plus the completed final sweep, both text screens, comparison,
and final process-escalation evidence. No checkpoint was grouped with another. No PR or push
was made; no merge, rebase or cherry-pick was performed.

The final zip contains the complete modified source, `REPORT.md`, the two format patches,
a git bundle whose sole prerequisite is the shared base, shared environment logs, all check
logs and per-module timings, seal and control sources and raw outputs, both screens, and
`SHA256SUMS`. Patch replay reconstructs the committed tree exactly. No compiled shim or Lean
build product is shipped. The full item report lists every new declaration and all remaining
obligations, including a literal **Proof sketch** for the open target.

## Dispatch and source scope

All attachment hashes match the dispatch:

| Attachment | SHA-256 |
|---|---|
| `megafill-D.md` | `149d928510a34bcd691db565c672d4358bce37badf3d9b723a017967b8825ebd` |
| `eq-fill-query.md` | `77a7bdb505b405a4581992a0af2299e42590819d8cc6e5ca327ebadf301fc947` |
| `fill-environment-addendum.md` | `90851511cf164dfa84ac9264cb5ba7acd54b7f551c823ae5d1000e43e233abf0` |

All three match their repository copies at the shared base after replacing `@ANCESTOR@`.
The requested campaign branch was cloned and the ancestor check passed. The item branch was
created at the exact shared base, with the required owned-file blob
`3cdc4f33a1650df104c752f2783bf5dc734be3b3`. Its first edit was exactly the eight-import overlay.

Only the owned source file changes. Its frozen public statements and original docstrings,
including `exists_diagonalizer`, are preserved; the permitted implementation-status paragraph
was added. The final file has 542 lines, 22 public declarations and 3 new private lemmas:
`qy_guard`, `qy_guard_decider`, and `qy_query_of_main`.

## Shared preflight and cache

| Measurement | Recorded value |
|---|---|
| CPUs (`nproc`) | 9 |
| Initial free disk | 31103799296 bytes (28.968 GiB) |
| Filesystem | Disk-backed overlay for clone, scratch, toolchain, cache and oleans |
| Memory limit | 8,589,934,592 bytes (8 GiB) |
| Initial anon + kernel + shmem | 100,954,112 + 98,902,016 + 0 bytes |
| Initial memory headroom | 8390078464 bytes (7.814 GiB) |
| Initial `oom` / `oom_kill` | 0 / 0 |
| Pre-cache free disk after toolchain | 26,974,597,120 bytes |
| Cache store before first fetch | `/root/.cache/mathlib` absent; 0 files, 0 bytes |
| Mathlib roots fetched | 34 |
| Files downloaded / unpacked | 1003 / 1003 |
| Fetch status | Exit 0; no failed download, no retry |
| Tar environment | `TAR_OPTIONS=--no-same-owner` |
| Manifest | 11 present packages match; 4 ABSENT; 0 mismatches |

The initial 12 GiB disk and 4 GiB memory floors passed; the optional post-toolchain 8 GiB disk
floor also passed. No OOM or OOM-kill event was observed. The four absent manifest packages
are the unused documentation toolchain. The cache contains no empty oleans, and a Mathlib-root
probe passed through `scripts/lean_check_tree.sh`.

**Root extraction qualification.** The literal Part 3 command at the shared base yields 33
roots. The authorized overlay adds `Mathlib.Data.Nat.Log`; the pre-ship record explicitly says
33 + 1 = 34. The shared fetch included that authorized root, without editing source before
the item branch was created. The literal extraction and adjustment are both logged.

Lean 4.25.0 was freshly installed for this session. Unmodified Lean failed with
`error: failed to locate application`; the exact authorized Part 2 shim then allowed Lean to
start. Its source SHA-256 is
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
Its source and exact scoped environment are included; its compiled `.so` is excluded.
No unfiltered cache fetch and no project `lake build` was invoked.

## Checks and limitations

| Check | Result |
|---|---|
| Re-bootstrap after overlay | 83/83 pass; 493.631 summed seconds; peak RSS 2947100 KiB |
| Tail after proof edit | Owned module and downstream facade pass |
| Final sweep | 83/83 pass; 502.596 summed seconds; peak RSS 3053144 KiB |
| Sorry inventory | Exactly the baseline 22 entries, verified by declaration name |
| Helper axioms | Only `propext`, `Classical.choice`, `Quot.sound`; target retains its direct `sorryAx` |
| Extended import probe | 501 checks of 501 names; zero errors or warnings |
| Seal | Whole owned module passes with 29 external definitions sealed |
| Controls | All 29 close unsealed and fail sealed; no unexpected pass |
| Semantic probes | All three new private statements searched; `exact?` could not close them in the overlay environment |
| Lint | 0 FAIL, 2 WARN over 5 files; unchanged baseline |
| Freeze and replay | Frozen regions preserved; patches reproduce HEAD exactly |
| Before screen | Exit 0; 1158.702 seconds; peak RSS 514200 KiB |
| After screen | Exit 0; 1144.766 seconds; peak RSS 514344 KiB |

Every explicit Lean module and probe check was serialized, used the required script, and ran
under `nice -n 10`. Each logs its start, end, wall time and maximum RSS. `/usr/bin/time` was
absent, so actual checks use `os.wait4` child rusage. The failed attempt to invoke the missing
timer exited before Lean ran. Screens ran one at a time on frozen detached worktrees.

Before screen: declarations screened: 1734; copy pairs (target reproduces >= half of source): 2162; reproduced text: 758,806 chars
After screen: declarations screened: 1738; copy pairs (target reproduces >= half of source): 2164; reproduced text: 758,958 chars
Before frozen commit: fabce3bb1008815d8f592da0c628e40c1355015d; after frozen commit: 9d93626dadf1561c757494cfff992d1951a458e2.
Before output matches the required baseline byte for byte.
New pair identities: 2; removed: 0; changed measurements on existing pairs: 0.
New cross-file pairs involving the owned file: 2.
New owned in-file pairs: 0.
New pairs:
NTimeDiagonalizer.lean::qy_guard_decider  reproduces  Nondeterminism.lean::a3n_poly_fixed_eq: 76/114 = 67%
NTimeDiagonalizer.lean::qy_guard_decider  reproduces  TMSAT.lean::tmsat_pt_eq: 76/127 = 60%
new copies: none
New owned-file pairs require inspection; no blanket duplication pass is asserted.

**Process escalation E-SERIAL.** The cache executable's permitted automatic compilation used
Lake's default scheduler, without an explicit single-job bound. An audit of its reported build
durations and retained trace timestamps gives overlapping build-action intervals of about
316 ms for `Batteries.Data.String.Basic` and `Batteries.Data.Array.Match`. Each trace invokes a
separate Lean executable. This is an inference from retained evidence, not a contemporaneous
process monitor; full compliance with the one-Lean rule cannot be certified. The evidence and
pinned Lake timing semantics are recorded in `cache-bootstrap-concurrency.log` and its two raw
trace JSON files. No further proof construction follows the finding. The already-running
after-screen finishes for this partial delivery. Later serialized checks do not cure the
earlier process deviation. No mathematical obstruction or resource shortage is asserted.

**Duplication escalation E-DUP.** The final screen has two new cross-file pairs involving
`qy_guard_decider`: `a3n_poly_fixed_eq` at 67% and `tmsat_pt_eq` at 60%. They do not reach the
90% copy threshold, but the brief separately prohibits every new owned-file cross-file pair.
That requirement fails. No exemption as a generic idiom or pre-disclosed pair is asserted;
`duplication-escalation.md` records the source inspection and finding. There are no new
in-file pairs. The checkpoint source is preserved without a further proof edit after E-SERIAL.

The mathematical continuation is checkpoint 2's setup contract, followed by the released
clocked call and round, locator and ledger, stage code, budget, writer and final assembly.
No machine or cost bound for those open checkpoints is claimed here.
