# Emitter fill — Batch P2: complete

**Completed the sole target, `computesFunInTime_splitSolveWith`.** Its audited
statement is unchanged. The emitter layer is **7/7**, the complete `Build/`
tree is admission-free, and the 57-module campaign sweep has exactly **12**
remaining admissions, all outside this batch.

## Provenance and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested starting branch: `complexity/arora-barak-ch1`; `main` was never checked out.
- Required base, resolved and object-verified: `08884731b3c86d13218470f23dc850c3c96c6314`.
- Base tree: `c35256a3e175a055570e3fc08b059ecfc9688807`.
- P2 brief read at `09e10c8987cf292c19bf6e8f2c9267de837bf6a8`; its parent is the required base.
- Working branch: `fill/emitter-P2`, created directly from the required base.
- Delivery commit: `32695dcb53e7f8dde6ee2e7f36796a407542fed0`.
- Delivery tree: `5cfe15ad1f3cb414b6a612d2ae7784aa9dfa2e80`.
- Only changed repository file: `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
- Single-agent execution. No other branch modification, push, or pull request.

The binding P2 brief, predecessor REPORT, gate resolutions, original P brief,
policy/workflow, inherited pitfalls, and cited audit construction were read.
Batch L's `emCall` controller, relocation, endpoint, and ledger proofs were
studied before implementation. Exact local object acquisition and pinned
runtime/cache details are recorded in `environment.txt`; no alternative base
was substituted.

## Route and the five continuation steps

**Route: bridge embedding.** Both evaluators use the proved public
`exists_installCallTM`. It already supplies elapsed-time visited-region
cleanup and full canonical entry/exit configurations. Reusing it avoids
reassembling the predecessor's tracked banks inside this body. The two
module witnesses are extracted once in `emitterP2_closed`, and the fixed
layout is candidate / width-call bank / suffix-length-call bank. All
predecessor declarations, including the 83 banked helpers, are unchanged.
The generic relocation layer is reimplemented from L's private `emCall`
family in accordance with the harvest rule; no foreign private is cited.

| Continuation step | Discharging declarations and exact result |
|---|---|
| 1. Controller, layout, startup, positive past-end stall | `EmitterP2State`, `emitterP2BodyTM`, `emitterP2Words`, all index/selection/frame lemmas, `emitterP2_body_start`, `emitterP2_prepare_first`, and `emitterP2_body_round`. Genuine startup is already the empty-word anchor. Every round executes one departure step. Preparation records the actual past-end condition; that branch bypasses both evaluators, erases preparation words, and returns silently. |
| 2. Actual candidate and actual prepared suffix, both charged before acceptance | `emitterP2_prepare_candidate`, `emitterP2_prepare_suffix`, `emitterP2_body_width`, `emitterP2_body_length`, `emitterP2_body_test`, and `emitterP2_closed`. The literal candidate is copied to the width argument; the suffix is copied from the native input. The clean calls install the complete canonical binary answers. `emitter_width_budget` first charges the evaluator at the actual candidate length; only then is monotonicity used. The suffix evaluator is likewise charged at the actual suffix length. |
| 3. Whole source-bank cleanup, administrative cleanup, and head restoration | The public install-call contract restores each entire module scratch bank. `emitterP2EraseTM` and its scan/back/run/first lemmas erase each complete returned word; `emitterP2_body_erase_left` and `emitterP2_body_erase_right` relocate those erasures. `emitterP2_prepare_run` restores the native head and all preparation heads. The frame equalities retain every inactive tape and head. `emitterP2_words_clean` identifies the resulting complete layout with `stateWord`. |
| 4. Whole-word comparison, verdict retention, payload, and exact rejection | `emitterP2_body_compare` embeds the predecessor's whole-word comparator at head zero. The verdict survives both erasers in finite control. `emitterP2_emit_initial` and `emitterP2_body_emit` enter `splitEmitTM 0` at its full genuine entry and emit only native-input bits. `emitterP2_body_advance` embeds `splitRestoreTM 0`, preserving arbitrary candidate bits and appending exactly one true bit only within the input range. `emitterP2_body_finish` makes the final rejecting transition to the literal canonical anchor configuration. |
| 5. Strict interior exclusion, one envelope, and loop closure | `emitterP2_segment`, `emitterP2_call_segment`, `emitterP2_after`, `emitterP2_strict_join`, and `emitterP2_body_round` account for every phase and dispatch. `emitterP2_closed` derives the common linear evaluator envelope and applies the untouched `emitterSplit_of_body`; the public proof is exactly `emitterP2_closed f E TE hTE hE`. |

The bridge contract permits equal entry and exit states. The controller's
separate `widthStart` and `lengthStart` states execute the first module
action unconditionally; `emitterP2_call_segment` then uses only strictly
positive source times for return tests. No deadline, `TE`, or width function
occurs in `emitterP2BodyTM`'s transition table.

**Boundary cases.** The one-past-end candidate returns to exactly its same
state word: the out-of-range branch of `splitStep` appends nothing. Its round
is positive because of the outer departure, independently of any zero-tape
source cleaner. Original source evaluators may have zero work tapes; the
extracted clean-call modules have positive tape counts, as required by the
layout. Empty captured words are recognized through module completion. For
empty input with zero width, both binary words are empty and acceptance
emits `pairEncode [] [] = [false, true]`. Exhaustion emits `[]` through the
already proved result-bearing loop. No monotonicity of the width function
is assumed. All payload bits come from the preserved native input.

## Verification

- **Full fresh final sweep: 57/57, exit 0, zero error diagnostics, 57 fresh nonempty oleans.** The final output directory was created empty. The committed direct-Lean script and exact module order were used; no `lake build` was invoked.
- **All seven emitter contracts have empty admission roots.** The target's printed axioms are exactly `[propext, Classical.choice, Quot.sound]`.
- **All 68 new private source declarations and 387 helper/generated kernel declarations are admission-free**, with axioms contained in the standard triple. The checked-environment traversal includes types, values including opaque values, and inductive constructors. The regression roots for `splitSolve`, `exists_loopFindTM`, and `capture_run` are empty.
- The sweep has exactly **12** remaining campaign admission warnings and **zero** in `Build/`. Their exact locations are in `verification.json`.
- **Freeze preserved byte-for-byte.** Deleting the single new private block and restoring the one target admission reconstructs the entire original file. Every other declaration, proof, signature, order, docstring, and import is unchanged. No public helper or new import was added. The portable `check-preservation.py` verifies this against the required base.
- `git diff --check`, incremental bundle verification, and temporary-index patch replay pass. Replay yields the exact delivery tree stated above. The working tree is clean.
- **Build-folder style lint: 0 FAIL, two recorded size warnings.** Repository-wide lint has **113 pre-existing FAIL lines**, byte-identical to an extraction of the required base; **zero new failures**. Global zero-FAIL lint is not claimed, and no out-of-scope file was changed.
- Lean 4.25.0 (`cdd38ac5115b`) and mathlib `029db123ddaa` were verified. All 11 materialized dependency checkouts match the committed manifest with unchanged tracked sources. Environment/cache qualifications are in `environment.txt`.

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1271:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

The source grows from 6,213 to **7,636 lines**, **403,447 UTF-8 bytes**:
1,424 insertions and one deletion, the deleted line being the target's
original admission. The inherited size exception applies: exclusive file
ownership requires the new helpers to remain private in this file. No shared
module was split or edited.

## All new private source declarations

```text
emitterP2Action
emitterP2Cfg
emitterP2_apply
emitterP2_relocate_run
emitterP2EraseTM
emitterP2EraseCfg
emitterP2_erase_scan
emitterP2_erase_back
emitterP2_erase_run
emitterP2_erase_first
emitterP2PrepareTM
emitterP2PrepareCfg
emitterP2_prepare_candidate
emitterP2_prepare_suffix
emitterP2_prepare_rewind_candidate
emitterP2_prepare_rewind_suffix
emitterP2_join
emitterP2_prepare_run
emitterP2_prepare_first
emitterP2_segment
emitterP2_call_segment
emitterP2Words
emitterP2LeftIndex
emitterP2LeftSelect
emitterP2RightIndex
emitterP2RightSelect
emitterP2_left_inverse
emitterP2_right_inverse
emitterP2_left_frame
emitterP2_right_frame
emitterP2_words_clean
emitterP2OneSelect
emitterP2_one_inverse
emitterP2_one_frame
emitterP2SmallIndex
emitterP2SmallSelect
emitterP2_small_inverse
emitterP2_small_frame
emitterP2PairIndex
emitterP2PairSelect
emitterP2_pair_inverse
emitterP2_pair_frame
emitterP2_update_left
emitterP2_update_right
emitterP2_update_candidate
EmitterP2State
emitterP2StateFintype
emitterP2StateDecidableEq
emitterP2BodyTM
emitterP2_body_start
emitterP2_control
emitterP2_body_prepare
emitterP2_body_width
emitterP2_body_length
emitterP2_body_compare
emitterP2_body_erase_left
emitterP2_body_erase_right
emitterP2_advance_initial
emitterP2_stateWord_one
emitterP2_body_advance
emitterP2_emit_initial
emitterP2_body_emit
emitterP2_after
emitterP2_body_test
emitterP2_body_finish
emitterP2_strict_join
emitterP2_body_round
emitterP2_closed
```

## Escalations and delivery

Statement escalations: **none**. Requested shared lemmas: **none**. No open
proof frontier or new admission remains. The repository-wide inherited lint
failures are recorded above and preserved unchanged.

`fill-emitter-P2.zip` is flat, with `SHA256SUMS` at its root. `Primitives.lean`
maps to the single owned repository path above. The archive contains this
REPORT, full source, one format-patch, the incremental git bundle (whose sole
prerequisite is the required base), final sweep and axiom logs, the kernel
traversal program, preservation/replay/pin/lint evidence, the module order,
and the binding briefs/resolutions and predecessor REPORT. `SHA256SUMS`
covers every payload except itself. Delivery is by this archive only.
