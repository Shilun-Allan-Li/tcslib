# Final SG1 round3 compiled refresh

Final HEAD `79e7c63a6bfa5f002663924f5c7d4e72db705026` is compared against BASE
`3023dc1408c3d216fc07a7cbba9ae30135b861ed` in the original nine owners.
This is complete compiled accounting; it grants no audit closure or merge clearance.
No source fix is indicated by this metadata comparison. Root owns the external gate.

Fresh HEAD has **7,063 constants = 5,712 private + 1,351 nonprivate**, versus BASE
**7,101 = 5,750 + 1,351**. All nonprivate names, owners, kinds, privacy/internal flags,
full raw types, structural ConstantInfo fields, reflected attributes and axiom sets
are unchanged. The complete **168 effective owned simp rules** are exactly equal,
including priorities, phase/direction, flags, parameters and retained rule expressions.

| Owner | BASE total | Final total | Final nonprivate |
|---|---:|---:|---:|
| `ClassNP.SAT` | 737 | 723 | 15 |
| `ClassNP.Tautology` | 428 | 423 | 6 |
| `CookLevin.Hardness` | 1425 | 1411 | 7 |
| `SpaceComplexity.Machines.Frag` | 79 | 79 | 73 |
| `TuringMachine.Build.Catalog` | 2178 | 2178 | 626 |
| `TuringMachine.Build.Contract.Basic` | 276 | 276 | 274 |
| `TuringMachine.Build.CounterLoop` | 289 | 287 | 204 |
| `TuringMachine.Build.Primitives` | 1281 | 1281 | 136 |
| `TuringMachine.Robustness.SingleTape` | 408 | 405 | 10 |

This final 7,063 is not the historical pre-#230 count of 7,063: current dependencies
include the merged API230 baseline and the nonprivate count is 1,351. The old D0
metadata head `d0c4a292e781b55617e05b33fdd423bb059fd735` had 7,065 constants.
`historical-D0-to-final79.json` records the exact difference: the final public
on-image repoint removes two private generated Tautology auxiliaries and adds none.
All shared CI/attributes/owners/kinds/privacy/internal flags/axiom sets are unchanged
from D0. Two private generated raw types under `clA5Pair_sizes` differ; their exact
identities are listed in that comparison. The current Hardness source differs too;
its compiler population is unchanged, while these two auxiliary types are refreshed.

## Complete delta and source distinction

`comparison-staged.json` retains every shared-field comparison and every exact added
or removed compiler identity. There are **six additions and 44 removals, all private**:
three authored private replacement proofs plus three generated auxiliaries are added;
three authored private proofs plus 41 generated auxiliaries are removed. There is no
source-authored or generated nonprivate addition/removal. The three source pairs are:

- `tautDual_segment_add` → `tautDualSegment_iff_segment`;
- `counter_span_append` → `counterSpan_iff_segment`;
- `dgSpan_add` → `dgSpan_iff_segment`.

There are ten retained-name raw-type changes, all private generated proof auxiliaries,
with full exact before/after representations and a diff in `changed-shared-types-*`.
They are not authored/public header changes. All other shared owner/kind/privacy/
internal/CI/attribute fields are exact. The only shared AX change removes
`Classical.choice` from private `clA5Pair_sizes`; there is no axiom-set growth.
`delta-classification.json` retains literal identities without private-ID normalization.

Source identity accounting is **1,986 authored declarations at both endpoints**:
349 public and 1,637 private. Forty surviving proof chunks changed conservatively
(including comments), and three private replacement proofs were added. No executable
source chunk changed. `source-authored-inventory.json` is used for identity/root
association, not a substitute for a Lean syntax/type parser. The separate complete,
bracket-aware source-header/attribute freeze and actual final source SHA pins are
recorded in `separate-source-review-pins.json`; all nine current source files match
the final79 source review and stayed unchanged through this task.

## All owned AX and current repair roots

CENSUS and ALLAX cover every owned constant, and PUBLICAX covers exactly every
nonprivate owned constant. In addition to the exact native 16-root/7-descendant
markers, offline association against complete ALLAX covers **all 43 current changed
or replacement proof roots (38 private, five public) plus 93 prefix descendants**,
136 distinct constants, all with only `propext`, `Classical.choice`, `Quot.sound`.
Every root/descendant, owner, privacy, kind and actual AX set is preserved in
`all-current-repaired-roots.json`; this uses existing complete native output and
introduces no extra proof or native execution claim.

The same **nine inherited Primitives sorry-dependent constants** remain with exact
metadata/types/axiom sets: public `appendBitTM_computes`, `polyBitsTM_computes`,
`polyUnaryTM_spaceUsed`, `splitSolveTM_computes`, `splitSolveTM_spaceUsed`,
`splitSolveWithTM_computes`, `stripLastTM_computes`, `unaryTokenTM_computes`, and
private `split_fuel`. `inherited-nonstandard-closure.json` retains every full row.
No formerly proved shared constant acquired `sorryAx` or any nonstandard axiom;
no added constant has one. This does not clear inherited campaign admissions.

## Execution and baseline adoption

Only HEAD was executed freshly, through the approved plain `leanelab.sh` with
`nice10`, `-j4`, local budget three/machine five, and one own Lean process at a time.
The pinned private probe project has an exact4.25 toolchain file and the worktree's
package symlink. It imports only the stable, complete, root-authorized MSG7 snapshot;
no compiled output or snapshot write is requested.

| Stage | BASE seconds | Fresh HEAD seconds | Full HEAD raw UTF-8 bytes |
|---|---:|---:|---:|
| `census-v1` | 100.87 (adopted) | 124.07 | 2,101,755 |
| `types-v1` | 21.09 (adopted) | 26.46 | 114,068,945 |
| `ciattrs-v1` | 11.69 (adopted) | 14.62 | 5,361,153 |

All six successful endpoint/stage outputs have zero errors/warnings. Each full raw
UTF-8 stream is losslessly retained in deterministic gzip plus ASCII Base64; receipts
record raw/gzip/Base64 SHA256 and sizes. The complete raw type stream is not capped
or replaced by a pretty type summary. `map-Base.json`/`map-Head.json` index every full
type by exact raw hash and block locator; the raw stream preserves every byte.
For UTF-8 audit packets, use the `.out.gz.b64` sections in place of binary `.gz`
sections; their receipts verify the exact same compressed and raw bytes. Decode as
untrusted data with standard Base64/gzip readers; no supplied script execution is
needed. No ConstantInfo theorem/proof-value dump is produced.

`BASE-ADOPTION.json` verifies **all 71 BASE-manifest payloads and all 94 original
final-manifest payloads**, exact successful probe/population bytes, all three lossless
raw archives, the nine frozen BASE source files, and all nine currently fingerprinted
MAC4 owner oleans. A fresh trusted offline reparse reproduces the frozen BASE maps
byte-for-byte. BASE native execution is adopted, never rerun or relabeled as fresh.
The historical BASE receipts pin4.25/MAC4 but did not separately fingerprint the Lean
executable or every transitive olean; that stronger historical attestation is not
invented. Current executable/tool fingerprints are retained separately. Root supplies
the immutable complete MAC4 lineage.

`root-replay-lineage-pins.json` independently hashes the root-owned receipts/logs:
MAC4→MSG5 full329-module closure atD0; whole-clone MSG5→MSG6 26-module Hardness tail
at63; whole-clone MSG6→MSG7 two-module Tautology tail at79. Each passes/static0.
MSG5 retains66 inherited admissions; MSG6/7 scopes have zero. These are root's executed
replays, not this child's new replay. This metadata task does not splice snapshots.

Three trusted probe sources and the runner were read before execution. Earlier
failed/stopped instrumentation stays in the unchanged original frozen evidence.
There are no fresh native failures. One non-native process-list diagnostic was
unavailable under default permissions; it changed/signalled nothing and supports no
conclusion. `diagnostics.json` records the limit.

Structural CI retains all applicable fields, including complete recursor rules.
Reflected attributes cover simp/inverse/unfold, reducibility, protected, instance
priority/kind, class, noncomputable, inline and match_pattern. Arbitrary third-party
extension state and theorem-value equivalence are not claimed. This task performed
no source/Git mutation, screen, source compilation, cache operation, fill, proof edit,
external gate closure or push. All own native jobs are complete. All source and
original owner-artifact fingerprints remain unchanged.
