# Emitter fill — Batch P: verified partial checkpoint

**INCOMPLETE: 2 of 3 public targets closed.** `appendBit` and `unaryToken`
are proved, in the required order. `computesFunInTime_splitSolveWith` retains
its original admission and unchanged statement. The three-target completion
gate does **not** pass. This is the continuation delivery permitted by the
brief, not an admission-free completion of `Primitives.lean`.

## Provenance and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required starting branch: `complexity/arora-barak-ch1`; never checked out `main`.
- Exact required base, resolved and object-verified: `d7b5b6f94d28df8095165dd4dfe82fd09ba0d414`.
- Brief read first at branch tip `dd22fb9e33a17b81ce7f334c248c59893af17e48`,
  whose only intervening commit adds the fill briefs. The work branch was
  created from the **required base**, not substituted with that newer tip.
- Working branch: `fill/emitter-P`.
- Delivery commit: `a272ad8c59af9c6828231d0fe6690e54b53c36b1`.
- Delivery tree: `8f5a49d09f9e68978a5eccc9eedff3fb5f759b74`.
- Single-agent execution; no push, PR, other branch modification, or sibling
  source modification. Temporary-index patch replay did not check out or
  modify another branch.
- Only changed repository file:
  `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
- The standalone `audits/emitter-infra-r2-findings.md` is absent at this base.
  Its exact attachment in the committed `audits/emitter-infra-r3-bundle.md`
  was read instead, including finding 8. The resolutions, round-3 findings,
  A-continuation report/source, design §8, prior fill pitfalls, policy, and
  workflow were read. No missing evidence was silently replaced by memory.

## Targets and exact boundary

| Order | Target | Result |
|---|---|---|
| 1 | `computesFunInTime_appendBit` | Closed with `emitterAppendTM` and `emitterAppend_run`; coefficient 1. Each input bit is copied, and the final right-blank transition both emits the fixed bit and halts. |
| 2 | `computesFunInTime_unaryToken` | Closed with `emitterTokenTM`, `emitterToken_double`, `emitterToken_separator`, `emitterToken_run`, and `emitterToken_length`; coefficient 3. The complete recursive token convention is implemented. |
| 3 | `computesFunInTime_splitSolveWith` | Open at the unchanged original `sorry`. The loop reduction and native phase components below are proved; the full body/controller is not constructed. |

The token run takes exactly twice the token length, plus the remainder
length, plus three transitions. Since the two lengths sum to the input
length, this is at most twice the input length plus three, hence at most
three times (the input length plus one). Its exported bound
is `3 * (n + 1)`. Empty input, leading false, terminated tokens, and all-true
unterminated tokens follow the same proved recursion. The suffix copier
preserves any already-emitted prefix. No standalone marker or polarity-bit
parsing is substituted for the unary-token convention.

## Split-search obligations: proved components and remaining seams

| Binding obligation | Discharging declarations and limits |
|---|---|
| Least-success semantics; exhaustion | `emitterSplit_find`, `emitterSplit_result`, `emitterSplit_loop_bound`, and `emitterSplit_of_body` instantiate the already proved `exists_loopFindTM` from explicit startup/round contracts. They reuse `splitStep_inv`/`splitStep_orbit`. No monotonicity of the width function is assumed. This is a conditional body-to-result theorem, not a constructed body. |
| Actual candidate before budget enlargement | `emitter_width_budget` first applies the supplied evaluator to the actual candidate at `TE s.length`, bounds its output at that same deadline, and only then applies budget monotonicity. `emitter_width_eval_first` supplies a positive observed prepared-evaluation return within the common input-length envelope. No generic composition deadline is fed back into `TE`. |
| Complete captured evaluation; empty output | `emitter_eval_initial`, `emitter_eval_run`, `emitter_eval_first`, and `emitter_prepared_eval_first` preserve the candidate and capture every output bit, including a halting emission. Dispatch follows the source halt, including an empty captured word. `emitterRightTM` normalizes the candidate to its known right boundary, even for empty input. Physical output is empty and the native input head stays at one. |
| Actual visited-region accounting | `emitterTrackTM`, `emitter_track_run`, `emitter_track_extent`, and `emitter_track_support` maintain source data, interval markers, and origin markers. They cover the halting transition's write and move. The tracked run costs one initialization plus two native steps per source step; every written cell lies in a span of width at most twice elapsed source time plus one. This is interval tracking, not overwritten-symbol history/undo. |
| Entire source-bank cleanup | `emitter_track_clearable` and `emitter_clear_first` prove each triple's exact blank endpoint within `6*T+7`. The new `emitterBankTM`/`emitterBank_step`/`emitterBank_run` combine all triples into a simultaneous native controller. `emitterBank_clear` restores the **entire** bank within the same bound, including zero source tapes; `emitterBank_first` dispatches at actual first completion. A zero-tape bank can return at time zero, so the outer body must supply its own positive departure/dispatch. |
| Whole canonical-word comparison | `emitterCompareTM`, `emitter_compare_run`, and `emitter_compare_first` compare both complete optional-bit words, including unequal lengths, and return silently with both heads zero. `emitter_bits_injective` and `emitter_binary_check` identify that comparison with the exact width equation when the candidate is within the input. Preparing the suffix-length word and connecting the comparison buffers remain open. |
| Native accepting payload | The existing in-file `splitEmitTM`/`splitEmit_run` are available unchanged. Their output uses the original native input, not candidate bits. The new controller has not yet been connected to that emitter's entry configuration. |
| Positive past-end stall; full canonical return | The pure `splitStep` and its invariant already specify the stall and preservation of arbitrary candidate bits. `emitterSplit_of_body` requires positive time, strict-interior anchor exclusion, and exact complete configuration equalities. A concrete controller discharging those requirements is still missing. |

The semantic reduction preserves the distinction between successful empty
splits (`pairEncode [] [] = [false, true]`) and exhausted search (`[]`). This
does not claim that the missing native body has already implemented those
branches.

## Continuation plan

No concrete `body`, `anchor`, or common coefficient has been supplied to
`emitterSplit_of_body`. Keep the audited public statement frozen.

1. Define the finite outer controller and complete tape layout, with distinct
   phases for entry, candidate/suffix preparation, the two evaluators,
   comparison, cleanup, restoration, and accepting emission. Implement the
   genuine startup and positive silent one-past-end stall first.
2. Embed `emitter_width_eval_first` on the actual candidate. Prepare the
   actual native suffix and invoke a witness of `computesFunInTime_lengthBits`
   on it with capture/tracking. Charge this before any accepted-equation
   assumption; retain the native input and candidate bits exactly.
3. Relocate `emitterBankTM` onto each tracked source bank while preserving
   the surrounding argument/capture tapes. Its full-bank theorem is proved,
   but those outer embeddings are not. Clear all administrative, suffix,
   and capture words as well; bank cleanup alone does not clear them.
4. Prepare the two comparison buffers at head zero, use
   `emitter_compare_first` and `emitter_binary_check`, and retain the verdict
   through cleanup. Restore the native input head to one and every scratch
   head to zero. On acceptance enter `splitEmitTM` with its complete entry
   configuration. On failure append a true candidate bit only within the
   input length and restore exactly `Cfg.ofWords anchor (stateWord ... )`.
5. Prove the concatenated trace's strict-interior anchor exclusion and common
   linear evaluator envelope, including all dispatches and the zero-tape
   cleaner case. Apply `emitterSplit_of_body` and replace only the final
   public proof body. Re-run the full sweep and require the remaining public
   admission roots to become empty.

## Verification

- **Fresh final sweep: 57/57 modules, exit 0, zero `error:` diagnostics,
  57 fresh nonempty oleans.** The output directory was newly created and
  empty before the sweep; the committed direct-Lean script was used.
- The final sweep has **18 admission warnings**: the remaining owned split
  theorem, the four untouched concurrent emitter admissions, and the
  thirteen untouched campaign admissions.
- `ClosureAxioms.lean` traverses checked kernel declaration types, values
  (including opaque values), and inductive constructors. Both completed
  targets and **83 source helpers / 241 helper-and-generated declarations**
  have empty admission roots and axioms contained in
  `[propext, Classical.choice, Quot.sound]`.
- The remaining split theorem has **exactly its original self-root**. No
  concurrent admitted contract is cited. Regression roots for
  `computesFunInTime_splitSolve`, `exists_loopFindTM`, and `capture_run`
  remain empty. `PARTIAL_CLOSURE_AUDIT_PASS` checks these explicit partial
  expectations; it is not the three-target completion gate.
- Preservation is stronger than a signature comparison: removing only the
  new private blocks/import and restoring the two filled proof bodies
  reconstructs the entire original file **byte-for-byte**. Thus every
  existing declaration, order, signature, docstring, and out-of-scope proof
  is preserved. No new public source declaration was added.
- `git diff --check`, incremental bundle verification, and temporary-index
  patch replay pass. Replay yields the identical complete tree `8f5a49d09f9e68978a5eccc9eedff3fb5f759b74`.
- Build-folder style lint: **0 FAIL**, two size warnings. Repository-wide
  style lint: **113 FAIL**, identical line-for-line to a fresh extraction
  of the required base; **zero new failures**. They are in untouched
  circuit/reduction files and `Formulas/DNF.lean`. Global zero-FAIL lint
  cannot be certified at this base, and those files were not altered.
- Pinned Lean and mathlib verified; all 11 active dependency checkouts match
  the manifest with unchanged tracked sources. Four inactive documentation
  dependencies were not materialized. Cache recovery and the runtime's
  executable-path adapter are recorded in `environment.txt`; no `lake build`
  was invoked.

Final sweep tail:

```text
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

## Source size, provenance, and declarations

The file grows from 4480 to **6213 lines**
(321430 UTF-8 bytes): 1,735 insertions and two deletions, the two
removed lines being the completed admissions. The recorded size exception
continues to apply: exclusive ownership requires the harvests and their
proofs to remain private in this file. No shared file was split or edited.
The only added import is the precise `Mathlib.Tactic.FinCases` import.
All original docstrings remain byte-identical; a separate module comment
records the partial implementation and harvest attribution.

The evaluator, comparator, interval cleaner, tracker, and right-boundary
families were reimplemented from the A-continuation's `e3c*` templates in
the unchanged `ClassNP/Nondeterminism.lean` at the required base. The
`emitterSplit*` reduction adapts the existing in-file `splitSolve_of_body`
pattern. The `emitterBank*` simultaneous product controller and its complete
restoration/first-return proofs are new. The streaming primitives reuse the
in-file `scanCfg` and `scanCopy_suffix` infrastructure.

All 83 new private source declarations (compiler-generated helpers are
enumerated separately in `axiom-print.log`):

- `emitterSplitAccept`
- `emitterSplit_find`
- `emitterSplit_result`
- `emitterSplit_loop_bound`
- `emitterSplit_of_body`
- `emitterIdleTM`
- `emitterEvalTM`
- `emitterEvalCfg`
- `emitter_eval_run`
- `emitter_eval_initial`
- `emitter_eval_first`
- `emitter_take_succ_eq`
- `emitterCompareTM`
- `emitterCompareCfg`
- `emitter_compare_nonblank`
- `emitter_compare_scan`
- `emitter_compare_rewind`
- `emitter_compare_run`
- `emitterInterval`
- `emitterCleared`
- `emitter_cleared_step`
- `emitterClearTM`
- `emitterClearCfg`
- `emitter_clear_left`
- `emitter_cleared_zero`
- `emitter_cleared_all`
- `emitter_clear_scan`
- `emitter_origin_erase`
- `emitter_clear_origin`
- `emitter_clear_run`
- `emitterSpan`
- `emitter_span_extend`
- `emitterSlots`
- `emitterTrackTM`
- `emitterTrackCfg`
- `emitterTrackMid`
- `emitter_track_action`
- `emitter_track_stamp`
- `emitterLo`
- `emitterHi`
- `emitter_track_extent`
- `emitter_track_support`
- `emitter_span_zero`
- `emitter_track_initial`
- `emitter_track_run`
- `emitter_track_computes`
- `emitter_span_interval`
- `emitter_track_clearable`
- `emitter_first_entry`
- `emitter_compare_first`
- `emitter_clear_first`
- `emitter_bits_injective`
- `emitterBankSymbols`
- `emitterBankPart`
- `emitterBankTM`
- `emitterBankCfg`
- `emitterBank_part`
- `emitterBank_step`
- `emitterBank_run`
- `emitterClear_fixed`
- `emitterBank_clear`
- `emitterBank_fixed`
- `emitterBank_first`
- `emitterRightTM`
- `emitterRightCfg`
- `emitter_right_step`
- `emitter_right_run`
- `emitterRightScan`
- `emitter_right_scan`
- `emitter_right_finish`
- `emitter_right_endpoint`
- `emitter_right_computes`
- `emitter_prepared_eval_first`
- `emitter_binary_check`
- `emitter_width_budget`
- `emitter_width_eval_first`
- `emitterTokenTM`
- `emitterToken_double`
- `emitterToken_separator`
- `emitterToken_run`
- `emitterToken_length`
- `emitterAppendTM`
- `emitterAppend_run`

## Escalations and archive

Statement escalations: **none**. Requested shared lemmas: **none**.
Inherited verification issue: repository-wide lint has 113 preexisting
failures as documented above. The unfinished split body is an explicit
continuation frontier, not a proposed statement repair.

Delivery is `fill-emitter-P.zip`, flat with `SHA256SUMS` at its root.
`Primitives.lean` maps to the owned repository path stated above. The archive
includes this report, the full modified source, one format-patch,
`fill-emitter-P.bundle`, the final sweep and axiom logs, the audit program,
preservation/replay/pin/lint evidence, and the binding brief/resolutions.
`SHA256SUMS` covers every payload except itself. No push or PR is required.
