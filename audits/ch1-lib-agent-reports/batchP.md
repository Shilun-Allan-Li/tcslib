# Batch P — partial fill delivery

**Status: 11 of 15 targets filled, in the prescribed order.** The continuation
frontier is target 12, `computesFunInTime_pairLenCheck`. Targets 12–15 retain
their original `sorry` bodies. This is the partial ZIP delivery permitted by
`briefs/lib-fill-batchP.md`; it is not a completed primitive-catalog batch.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required base branch: `complexity/arora-barak-ch1`.
- Base commit: `e346139ccc9e3141908f7414bf27f74d8759c9be`.
- Local working branch: `fill/lib-P`, created directly from that base.
- Delivery commit: `b855effc50795b4aa1625c9963b8387901e6af0d`.
- Only changed repository file:
  `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
- No push or PR was made. No other branch was checked out or changed.

## Target ledger, in fill order

All names below have prefix `Turing.FinTM.computesFunInTime_`.

| # | Target | Status | Construction and source | Validation before physical output |
|---|---|---|---|---|
| 1 | `prepend` | Filled | In-file `catalogPrefixTM` and its emission/copy invariants, adapted from `ClassNP/Reductions.lean`'s private `prefixTM` family. The sharp source budget is weakened to the frozen uniform linear envelope. | Every input is legal; no parser guard is needed. |
| 2 | `pairEncodeFixed` | Filled | Apply target 1 to the doubled fixed first word followed by `[false,true]`. This is the `fixedPair_computes` harvest's fixed-first-component direction. | Every input is legal. |
| 3 | `pairDup` | Filled | New zero-work-tape `pairDupTM`: double the first input pass, emit the first separator bit, rewind, emit the second separator bit, copy the input. Exact budget `4(n+1)`. | Every input is legal; no buffering obligation. |
| 4 | `incFixed` | Filled | New zero-work-tape `incFixedTM`, adapting the enumerator's little-endian carry discipline from `ClassNP/EXP.lean` (`enumCarryTM`/`enumCarry_correct`) to native input and physical output. Bound `3(n+1)`. | State 0 scans silently for the first false; an all-true word, including `[]`, halts silently. Emission begins only after successful detection and rewind. |
| 5 | `pairValid` | Filled | New `pairValidTM`, finite control retaining the first bit of an aligned block; `pairValid_run` proves the `n+1` bound. | Only a terminal verdict transition emits. Equal-bit blocks remain silent; `01` succeeds; `10` and missing/incomplete separators fail. |
| 6 | `pairFst` | Filled | Shared private `pairExtractTM true false` and `extract_run`; bound `5(n+1)`. | Parser states emit nothing. `extract_block` sends a validated `01` to rewind/replay; malformed cases halt silently. The buffered decoded prefix is replayed only after this seam. |
| 7 | `pairSnd` | Filled | `pairExtractTM false true`; the same `5(n+1)` envelope. | The shared parser validates first. Its replay is silent when the first flag is false, and then it copies the suffix. |
| 8 | `pairConcat` | Filled | `pairExtractTM true true`; the same `5(n+1)` envelope. | Validated replay emits the buffered first component, then suffix copying emits the second. No physical output occurs during parsing. |
| 9 | `lengthBits` | Filled | Reuse the public, already-proved `Complexity.timeConstructible_id`. Its witness is exactly a linear-time machine for `Nat.bits x.length`, with the amortized in-place counter required by the sketch. | No parser. The public proof handles empty input and halts with `[]`. |
| 10 | `polyUnary` | Filled | The in-file `catalogPolyUnaryTM` family is adapted from `ClassNP/TMSAT.lean`'s `polyUnaryTM` through `poly_unary_computes`. For positive exponent, the predecessor is the loop parameter, implementing the audited `e-1` indexing. Degree zero uses the public fixed-word emission-chain contract. | Every input is legal. Coefficient zero, degree zero, and empty input are covered by the formal proof. |
| 11 | `polyBits` | Filled | Targets 10 and 9 composed with public `computesFunInTime_comp`. Monotonicity and explicit coefficient arithmetic retain exponent `e+1`. | Both total stages are already proved. |
| 12 | `pairLenCheck` | **Pending: next target** | Original admitted statement and body, unchanged. | Buffer/parse, polynomial unary generation, countdown comparison, and malformed `[false]` remain obligations. |
| 13 | `stripLast` | **Pending** | Original admitted statement and body, unchanged. | Validity and last-true detection before re-encoding remain obligations. |
| 14 | `pairMapSnd` | **Pending** | Original admitted statement and body, unchanged. | Silent parsing, relocated capture, and postcapture pair emission remain obligations. |
| 15 | `splitSolve` | **Pending** | Original admitted statement and body, unchanged. The continuation must use the audited `exists_loopFindTM` route. | The concrete body, invariant, fuel connection, and payload assembly remain obligations. |

The continuation begins at target 12; no later target was filled out of order.
No incomplete helper proof, temporary admission, or speculative controller is
included in this delivery.

## Proof-route notes and documentation preservation

The length counter reuses a **public** theorem from the already-earlier
`ClassP/TimeConstructible` module. No other module's private declaration is
cited in a proof. The prefix and polynomial-generator harvests are copied and
adapted as private declarations inside the owned file.

For fixed-width increment, the enumerator is the semantic carry template,
not a verbatim in-place-machine copy: the new machine first detects overflow
on native input, then rewinds and emits the incremented word. The final proof
handles every input by the proved all-true/first-false decomposition.

Suffix-only extraction shares the buffered parser, so it performs a silent
buffer replay before copying the suffix. This adds only linear work and
preserves the frozen function and budget.

All 15 original contract docstrings are byte-identical. The module docstring
has one appended implementation-status paragraph explaining these points and
identifying the four remaining stubs. Additional private helper docstrings and
two harvest-attribution notes were inserted without changing audited prose.

## Verification

- Lean: `4.25.0`, release commit
  `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- PFR: `e1095d58b7c6f10734988816f7764f2103b9bf29`.
- `lake build` was never invoked. The single `lake exe cache get` invocation
  was interrupted by download/transport failures and a shared-cache
  configuration-file disappearance. The pinned 916-module import closure was
  recovered in an isolated cache using the pinned cache library's hash map,
  parallel downloads, and unpacking. Dependency pins and source files were
  not changed. `verification/cache-resume.log` records successful recovery.
- The 57-module dependency order was bootstrapped; local proof iterations
  used the owned-module checker. Later modules were checked after the initial
  fills, and the final result was checked by a complete fresh sweep.
- **Final sweep:** all 57 modules in the committed order, a fresh output tree,
  exit 0, zero error diagnostics, and `SWEEP_PASS modules=57`. All 57 expected
  headers and their order were independently recounted.
- **Admission-warning count:** 40 total: 4 wrapper, 4 loop, 4 pending primitive,
  and 28 outside Build. The owned module's final check has exactly its four
  pending-admission warnings and no other warnings.
- **Axiom checks:** all 15 target prints and checked-kernel root traversals
  passed. Every one of the 11 filled targets uses exactly
  `[propext, Classical.choice, Quot.sound]`, with an empty admission-root set.
  Each pending target has only its own unchanged root.
- **Sanctioned cross-batch roots:** `Turing.capture_run` and
  `Turing.FinTM.exists_loopFindTM` are **unused**. Pending targets are not
  presented as completed proofs justified by those roots.
- **Statement freeze:** all 15 raw signatures, and their comment-stripped
  forms, are unchanged; the public declaration sequence and multiset are
  unchanged; zero public declarations gained/lost/reordered. Each pending
  theorem through its original `sorry` is byte-identical.
- **Ownership:** the git diff from the pinned base touches only the owned
  `Primitives.lean`. `git diff --check` passed; the final worktree is clean.
- **Style lint:** 0 FAIL, 1 WARN over the four Build files. The warning is
  the owned file's size, justified below.

The axiom walker in `verification/PrimitiveAxioms.lean` adapts the committed
`ch1-infra-BridgeExportAxioms.lean` template. It traverses checked declarations'
types and values with `allowOpaque := true`, visits inductive constructors,
identifies direct `sorryAx` consumers, compares exact root sets, and rejects
any unexpected axiom. The source freeze checker and its per-signature hashes
are included in `verification/`.

### Final sweep tail

```text
MODULE 52 TCSlib/Complexity/TuringMachine
MODULE 53 TCSlib/Complexity/ClassP
MODULE 54 TCSlib/Complexity/Uncomputability
MODULE 55 TCSlib/Complexity/Formulas
MODULE 56 TCSlib/Complexity/CookLevin
MODULE 57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
```

## Requests and size justification

**Statement escalations: none. Shared-lemma requests: none.**

The owned file is 1,687 lines. The brief explicitly permits an over-1,000-line
file with a recorded justification. Exclusive ownership requires the finite
machines, transition/run invariants, and harvested nested-loop generator to
remain private in this one file. The generator alone needs roughly 420 lines,
and the frozen public specification/docstrings already occupy roughly 345.
The implementation shares one parser across three contracts and common scan
lemmas across the zero-tape machines. Compressing the remaining proofs to fit
1,000 lines would sacrifice the required readable invariants and sketches;
moving them into other modules would violate this batch's file boundary.
This size exception is recorded for the maintainer's decision log.

## Archive and integration

The archive contains the full modified source, one `git format-patch` patch,
an incremental git bundle, this report, verification logs/programs, and
`SHA256SUMS`. The bundle has the pinned base as its prerequisite and was
verified with `git bundle verify`. The patch changes only the owned file.
Applying it to the pinned base source in an isolated directory reproduced
the checked source byte-for-byte (`verification/patch.log`).

After verifying checksums, integrate the patch series onto the required
branch with the workflow's `git am -3` procedure. The integration commit's
source must match SHA-256
`90bd09a4deb607e47484f3fefb2163eb779d84ef45e173c7a47b07cff4f2b324`.
Re-run the repository's 57-module checker in its committed order, then run
the included axiom program with that fresh output tree first on `LEAN_PATH`.

## All new explicit private declarations

The following inventory lists all 54 new explicit private declarations in
source order. Lean-generated constructors, recursors, matchers, and instance
auxiliaries are generated from these declarations; the kernel traversal also
follows their dependencies.

| Kind | Declaration |
|---|---|
| def | `catalogPrefixTM` |
| def | `catalogPrefixCfg` |
| lemma | `catalogPrefixTM_emit` |
| lemma | `catalogPrefixTM_copy` |
| lemma | `catalogPrefixTM_computes` |
| def | `scanCfg` |
| lemma | `scanCfg_read` |
| lemma | `scanCopy_run` |
| lemma | `scanCopy_finish` |
| def | `pairDupTM` |
| lemma | `pairDup_double` |
| lemma | `pairDup_computes` |
| lemma | `scanCopy_suffix` |
| lemma | `scanTrues_run` |
| lemma | `incFixed_cases` |
| def | `incFixedTM` |
| lemma | `incFixed_computes` |
| lemma | `scanStep_right` |
| def | `pairValidTM` |
| lemma | `pairValid_block` |
| lemma | `pairValid_run` |
| lemma | `pairValid_computes` |
| def | `pairExtractTM` |
| def | `extractCfg` |
| lemma | `extractCfg_read` |
| lemma | `extract_first` |
| lemma | `extract_block` |
| lemma | `extract_rewind` |
| lemma | `extract_replay` |
| lemma | `extract_replay_finish` |
| lemma | `extract_suffix` |
| lemma | `extract_finish` |
| lemma | `extract_run` |
| lemma | `pairExtract_computes` |
| inductive | `CatalogPolyControl` |
| instance | `catalogPolyControlFintype` |
| instance | `catalogPolyControlDecidableEq` |
| def | `catalogPolyTape` |
| def | `catalogPolyMove` |
| def | `catalogPolyUnaryTM` |
| def | `catalogPolyCfg` |
| lemma | `catalogPolyMove_apply` |
| lemma | `catalogPoly_emit` |
| lemma | `catalogPoly_rewind` |
| lemma | `catalogPoly_advance` |
| def | `catalogPolyCost` |
| lemma | `catalogPoly_loop` |
| lemma | `catalogPolyTape_write` |
| lemma | `catalogPolyCost_le` |
| def | `catalogPolyCopyCfg` |
| lemma | `catalogPoly_copy` |
| lemma | `catalogPoly_setup` |
| lemma | `catalogPoly_start` |
| lemma | `catalogPoly_unary_computes` |

## Axiom prints

```text
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairDup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairConcat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The complete per-target root report is in `verification/axioms.log`.

**Notation glossary.** `n` is input length; `e` is the frozen polynomial exponent; `[]` is the empty list. All Lean identifiers refer to declarations named above or in the frozen brief.
