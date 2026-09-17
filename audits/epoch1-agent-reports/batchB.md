Fill epoch 1 batch B from `briefs/epoch1-batchB.md`. Base is `complexity/arora-barak-ch1` at `9f735248212c1d1d842b299b431b2b680220ac5b`; head is `fill/epoch1-B`.

The three audited construction statements now have checked proofs. The conditional reproduces the selected branch's completed relation on the original input, including divergence, using disjoint work tapes and an input-head rewind.

## Targets filled

- [x] `computesFunInTime_const`: follows the emission-chain sketch; a reusable induction proves the emitted prefix and final halting step, then monotonicity gives the stated linear bound.
- [x] `computesFunInTime_ifEq`: follows the comparison-and-emission sketch; induction on the remaining fixed word covers early blanks, extra symbols, empty words, and the boundary read, with the stated constant absorbed into the linear bound.
- [x] `exists_cond`: follows the captured-emission, rewind, and fresh-tape sketch. The controller invariant stores the first emitted symbol (`head?` of its simulated output), waits for the first halt, and uses output uniqueness to identify the register. Rewind and branch lockstep are proved explicitly. Absorbing halting transports any completed composite run past the known branch-start prefix, proving the forward implication without a separate phase-decomposition induction.

## New declarations for audit restatement

- [x] Every new declaration is listed below. All 31 are **private**, within `Turing.FinTM`; no public declarations were added.

| Purpose | New declarations |
| --- | --- |
| Reusable emission chain and constant machine | `emitAction`, `emit_run`, `emit_halts`, `constTM` |
| Control action and fixed-string comparison | `controlAction`, `inputSymbol_at`, `ifEqTM`, `ifEq_finish`, `ifEq_run` |
| Disjoint tape embeddings and lockstep | `leftAction`, `rightAction`, `leftCfg`, `rightCfg`, `leftCfg_apply`, `rightCfg_apply`, `leftCfg_step`, `rightCfg_step`, `leftCfg_run`, `rightCfg_run` |
| Time-only semantics and branch sum | `computesInTime_iff`, `branchTM`, `branchTM_computes` |
| Input-head rewind | `controlAction_apply`, `moveInputPos_neg_val`, `rewind_scan`, `rewind_from_any` |
| Controller and dispatch | `condTM`, `controlCfg`, `controlCfg_step`, `controlCfg_run`, `condTM_start` |

**Epoch-2 reuse:** the left/right action and configuration embeddings preserve arbitrary inactive tapes and head positions; `rightCfg_run` therefore handles a fresh machine alongside a previous phase's completed work. `controlAction_apply`, `moveInputPos_neg_val`, `rewind_scan`, and `rewind_from_any` isolate the input-head rewind, including both boundaries and empty input. The emission lemmas are independent of the input and work-tape contents. All remain in the owned file as required; the file is 947 lines because this batch must retain its private simulation infrastructure here.

## Requested shared lemmas

- [x] Requests recorded; no shared or vendored file was modified.
- Consider placing `computesInTime_iff` in `Finite.lean` at epoch merge.
- Consider exposing `inputSymbol_at` and `moveInputPos_neg_val` in a non-vendored helper module rather than editing `Configuration.lean`.
- Consider a shared simulation-helper home for `controlAction` / `controlAction_apply`, the left/right embedding families, and the two rewind lemmas when epoch 2 needs them. Their present private copies comply with this batch's ownership rule.

## Escalations

- [x] None. All three frozen statements are proved.

## Statement, sketch, and scope checks

- [x] Diff touches only `TCSlib/Complexity/TuringMachine/Composition.lean`.
- [x] All eight pre-existing declaration signatures are unchanged; the identity machine and its proofs are unchanged.
- [x] `computesFunInTime_comp` and `exists_comp_partial`, including their full docstrings and sorry bodies, are unchanged. These are the only two remaining sorries in this file.
- [x] All original docstrings are retained. The `exists_cond` proof-sketch paragraph has an appended clarification describing the first-emission invariant, the live administrative state after simulated halt, and the absorbing-halting argument. No attribution changed.
- [x] Imports remain precise and the option headers are retained. `git diff --check` passes.

## Verification evidence

- [x] Lean **4.25.0**, official release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, and the repository's pinned dependencies.
- [x] Initial bootstrap sweep, incremental `Composition` checks, and final full sweep used `scripts/lean_check_tree.sh`. No `lake build` was run.
- [x] Final sweep regenerated **22/22** module oleans after its recorded start time, with **zero `error:` lines** and **18 expected out-of-scope sorry warnings**. `Composition.lean` itself reports exactly the two untouched out-of-scope declarations; baseline linter warnings in vendored `Configuration.lean` remain untouched.
- [x] Temporary `#print axioms` checks for all three filled targets report exactly `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**. The temporary commands were removed before the final sweep and are absent from this diff.

Commands used for proof verification:

```bash
bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Composition
while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt
```

Environment setup note: the dependency-cache fetch was narrowed to the chapter's complete transitive Mathlib imports plus the three new Fintype imports, then unpacked with `lake exe cache unpack`. Archive extraction used `--no-same-owner`. This cloud runtime also needed a small executable-path compatibility shim redirecting only the process's own numeric `/proc/<pid>/exe` lookup to the permitted `/proc/self/exe`; the official Lean binary, kernel, and library sources were not modified. Setup files and logs were kept outside the repository.

Final full-sweep log tail:

```text
TCSlib/Complexity/ClassP/TimeConstructible.lean:85:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:109:8: warning: declaration uses 'sorry'


TCSlib/Complexity/ClassP/Examples.lean:69:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:117:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:137:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:252:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:265:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:102:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:124:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:148:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Computable.lean:64:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Diagonalization.lean:98:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Halting.lean:139:8: warning: declaration uses 'sorry'
```

Axiom-check output:

```text
'Turing.FinTM.computesFunInTime_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_ifEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_cond' depends on axioms: [propext, Classical.choice, Quot.sound]
```
