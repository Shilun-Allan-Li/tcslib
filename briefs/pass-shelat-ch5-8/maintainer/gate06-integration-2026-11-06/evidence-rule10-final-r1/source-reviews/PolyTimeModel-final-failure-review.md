# PolyTimeModel: final source-identity witnesses

**All 16 source diagnostics remain failures.** Static review found **13 failing declarations, zero new/changed failing header/body blocks**, and **13 new historical-observation keys requiring root review/dedup recording**. The newly added `polyTimeModel_eff_iff` is not among the failing declarations. This is neither acceptance nor a pass/exclusion/waiver.

Exact final pins read from `evidence-rule10-final-r1/pins.json`:

- Base `eee107e92a7db11f1f8c98a5c2867304f57ddc54`.
- Head `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`.
- Source `TCSlib/Complexity/Randomized/PolyTimeModel.lean`.
- Complete base source SHA-256 `e3cffbe20e78537fdc411197241a42ff0546913b019701c6c816d51e88f35ee4`.
- Complete head source SHA-256 `e3085eef1a3b51d03fb1442ce8b6206d4b0332a86e40e44734c6020bed6cf04c`.

No mutable worktree library source supplied comparison bytes. The full head file differs only by the nine-line new reader insertion; removing head lines 84–92 reproduces the **entire base file byte for byte**. Thus every preexisting declaration, docstring, formal statement, algorithm and proof in this module is unchanged, not merely token-equivalent. There is no doc-boundary overclassification here.

## Complete failing blocks

The ranges below cover each complete formal header and proof, excluding its preceding docstring. The JSON stores each full raw block and its SHA-256, exact error coordinates and root native log lines. Each head block was independently compared with the corresponding base block; all are byte-identical. Their preceding docstrings also remain byte-identical by the whole-file insertion witness.

| Declaration in `Randomized` | Base range | Head range | Diagnostics | Native log lines |
| --- | --- | --- | ---: | --- |
| `polyTimeComputable_takePrefixByLen` | 115–117 | 124–126 | 1 | 1572 |
| `polyTimeComputable_dropPrefixByLen` | 123–125 | 132–134 | 1 | 1578 |
| `polyTimeComputable_sliceTake` | 132–150 | 141–159 | 1 | 1584 |
| `polyTimeComputable_sliceDrop` | 155–173 | 164–182 | 1 | 1590 |
| `polyTimeModel_closedUnderRace` | 184–212 | 193–221 | 1 | 1596 |
| `polyTimeModel_closedUnderAnswerIs` | 218–241 | 227–250 | 1 | 1599 |
| `polyTimeModel_closedUnderMajority` | 250–300 | 259–309 | 1 | 1602 |
| `polyTimeModel_closedUnderAny` | 307–342 | 316–351 | 1 | 1605 |
| `polyTimeModel_closedUnderNot` | 346–352 | 355–361 | 1 | 1608 |
| `polyTimeModel_closedUnderShiftOr` | 364–392 | 373–401 | 1 | 1611 |
| `polyTimeModel_verifierHasCircuits` | 409–471 | 418–480 | 2 | 1614, 1620 |
| `inSigma2_polyTimeModel_iff` | 488–534 | 497–543 | 3 | 1621, 1622, 1625 |
| `sipser_gacs_polyTime` | 552–559 | 561–568 | 1 | 1626 |

The first four failures are existing foreign-function/length-schedule conversions. The six closure failures stop while introducing sealed foreign closure predicates. Circuit simulation reports the existing `PPoly`/`InPPoly` conversion plus destructuring; the Σ₂ equivalence reports two sealed-predicate construction/destructuring errors and the subsequent “No goals” diagnostic; Sipser–Gács reports the existing `InPi2`/complement-`InSigma2` conversion. All diagnostics, including the secondary “No goals” report, remain counted. No repairs are proposed here.

## Namespace, binding and operative definition context

Both versions remain in `namespace Randomized`, with exactly the same `open Complexity`, ten direct imports and three options. No variable, notation, attribute, instance or namespace-binding command changed. The local model definition, slice functions, prefix primitives and all formal contract/deviation prose are unchanged.

The exact current TCSlib import closure has 81 source files. **79 are completely byte-identical** between the actual base and head. The only two changed imports are:

- `CircuitComplexity/DAGCircuit.lean`: four plain public reading theorems (`DAGGate.eval_eq`, `DAGCircuit.values_eq`, `DAGCircuit.eval_eq`, `DAGCircuit.size_eq`). Removing only those insertions reproduces the whole base file.
- `Randomized/Classes.lean`: three plain public reading theorems (`randProb_eq`, `polyLen_eq`, `boolVerifier_apply`). Removing only those insertions reproduces the whole base file.

Neither import changes an existing definition, datatype, theorem header/body, module/formal-contract prose, scope command or attribute. The seven added theorems and the local new reader have no simp/instance attributes, and none of their newly introduced source names occurs in the thirteen failing blocks. Their addition does not alter the operative mathematical contracts read at these failure sites. The JSON records full source hashes for all 81 imports and the exact inserted bytes/ranges for both changed imports.

The important foreign definition homes in the actual seal catalog are unchanged:

- `Complexity.PrefixByLength.take/drop`: `ClassNP.PolyTimePrefix`.
- `Complexity.PolyTimeComputable`: `ClassNP.PolyTime`.
- `polyLen`, race/answer/majority/any/not closure predicates: `Randomized.Classes`.
- shifted-OR closure, `InSigma2`, `InPi2`: `Randomized.SipserGacs`.
- `VerifierHasCircuits`: `Randomized.Adleman`.
- `Language.InPPoly`: `CircuitComplexity.PPoly`.

Whole-home source identity, or the exhaustive reader-only insertion witness above, verifies their original bodies and binding contexts rather than merely assuming unchanged meanings from identical names. `lean-toolchain` and `lake-manifest.json` are also byte-identical between the pins (SHA-256 `dbbf063fc415c8e718172605f23a8f86679a3c320eff6d3890cc009534452925` and `cad7de215c4cc216d03acb77cb1abfbe9f3b4062a8988b29459504f932015100`). This does not claim a separately rebuilt base native environment.

## Historical deduplication

Neither frozen cleanup inventory contains **any row for this source path**, and neither contains an exact same source/qualified declaration name in another path. Consequently there are zero exact historical keys for the thirteen failures. They were also absent from both declaration sections of the initial 95/120 review.

Inventory fingerprints used:

- `cleanup-b-decls.tsv`: `371988e791191772c9c74b6d86879b2b688cba731dbd0f3dc4c5decc3411f6fb`.
- `cleanup-b.tsv`: `32d88f9f3ff992ba4b46033d8800e199b48fd5f7416a59e1d6aa1dee088cac92`.

Mixed literal `\t` and real tab separators were read. These are **13 new source-identity observation proposals for 16 diagnostics**, not additions already accepted into the 764 inventory and not a revision of the initial survey's totals. Root should record each exact `(file, Randomized.name)` key with its fresh ranges/hashes/log links and carry the failures into cleanup accounting. No ledger was changed.

## Native evidence read, not rerun

Read the completed root record `native-seal-runs/G06Seal_004_TCSlib_Complexity_Randomized_PolyTimeModel.classification.json` (SHA-256 `362524af3155fa17f7a81251e0360498eb9c68665912f54ef7ad89c6c4f7545e`) and its referenced native log (SHA-256 `6ab0386fc020cd195c3e71606b9beef35d2af4cbfb24f02f9f623b6644e1b3ac`).

Read-only independent text checks matched all 16 error headers to their recorded coordinates and source lines; all 1568 unique actual-name/home/previous-status rows to the fresh manifest; installation counts 1550 active + 18 already irreducible; and the 1568-name EOF verifier. Reversing every recorded probe insertion recovered the exact Git head source. The probe SHA-256 is `c913a50fc421fa79dba479aff06f4a584007b655f6f0224c0fb566908e55ca16`. The root run exited 1 with no fresh object, as a failed source seal should. This review does not rerun it or change its status.

The newly added owner reader is inside the same complete probe and has no diagnostic attributed to it. That statement is narrower than a whole-module pass.

At a single availability check, Encoding ordinal 39's completed classification did not yet exist. It has not been reviewed or polled repeatedly here.

Only independently authored read-only Git/text analysis was executed, writing temporary review artifacts. No received/repository helper, native/cache/build/app command, source edit, Git mutation or final evidence write occurred. The optional reproducer is main-guarded and writes only its fixed `/private/tmp` output, not campaign records or source. JSON SHA-256: `1a637b12709e1c31e136ea4042ed0c0eabbbd8374364adecb41fa08d5107204e`.

**Not yet clear to merge — all failures remain retained; root must review/file the thirteen new source observations and complete the final survey reconciliation.**
