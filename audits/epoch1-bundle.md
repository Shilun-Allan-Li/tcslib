# External audit pack — Fill campaign, Epoch 1 (first fill round)

Audits commit `d3393b35` on `complexity/arora-barak-ch1`. Since the phase-4 gate
(`audits/phase4-resolutions.md`; pre-fill HEAD `9f735248`), the **epoch-1 fill
round** landed: four independent cloud agents (cross-vendor), one per batch of
the campaign schedule (plan §5 "Fill campaign", briefs in `briefs/`), filled
**12 of the 21 audited-true sorries**. The maintainer reviewed each delivery
line by line against its brief, applied the four patches with authorship
preserved (commits `5b468f61`, `f32fde05`, `5564c6a8`, `d3393b35`), and
re-verified everything locally, independently of the agents' own logs. **No
statement changed.** Record findings in `audits/epoch1-findings.md`.

This round differs from the phase audits: the headline trusted surface is
(deliberately) almost unchanged — the fills close existing audited statements.
What is new for audit is (a) the integration attestations below, (b) the
private supporting declarations, two of which are requested for promotion to
shared files at epoch merge, and (c) the flagged docstring appendices.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Statement freeze.** `git diff 9f735248..HEAD` removes exactly 15 lines:
   the 12 target `sorry`s, plus 3 docstring closing lines
   (`` `Nat.bits 0 = []`). -/ ``, `` `cond (p x) M₁ M₂`. -/ ``,
   `` cast uses `hk : M.k = 1`. -/ ``), each re-appearing verbatim with an
   appended implementation note (the flagged sketch-appendix mechanism of the
   campaign ground rules). Every other pre-existing line — every declaration
   name, signature, hypothesis, and attribution — is untouched. All other diff
   lines are additions.
2. **Elaboration** (phase-4 finding 8 obligation). Full 22-module sweep via
   `scripts/lean_check_tree.sh` over `scripts/ab_ch1_module_order.txt`, fresh
   olean tree, Lean 4.25.0 / mathlib `029db123ddaa` (unchanged manifest):
   **zero `error:` lines**; exactly 9 `declaration uses 'sorry'` warnings:
   `computesFunInTime_comp` (Composition:427), `exists_comp_partial`
   (Composition:475), `alphabet_reduction`, `one_work_tape`,
   `nonnegative_heads`, `oblivious_of_mem_DTIME`,
   `exists_effectiveMachineCode` (Encoding:454), `universal` (Universal:102),
   `timed_universal` (Universal:165). The 9 remaining sorry bodies and their
   sketches are textually unchanged.
3. **Axiom footprint** (`#print axioms`, maintainer-run):

   ```text
   'Turing.FinTM.computesFunInTime_const'  [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.computesFunInTime_ifEq'   [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.exists_cond'              [propext, Classical.choice, Quot.sound]
   'Turing.pairEncode_injective'           [propext, Quot.sound]
   'Turing.computesFunInTime_pairEncode_diag' [propext, Classical.choice, Quot.sound]
   'Turing.exists_codeTM'                  [propext, Classical.choice, Quot.sound]
   'Complexity.PAL_mem_DTIME_linear'       [propext, Classical.choice, Quot.sound]
   'Complexity.timeConstructible_id'       [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.Computes.exists_computesFunInTime' [propext, Classical.choice, Quot.sound]
   'Turing.universal_quadratic'            [propext, sorryAx, Classical.choice, Quot.sound]
   'Complexity.UC_not_computable'          [propext, sorryAx, Classical.choice, Quot.sound]
   'Complexity.UC_computable_of_HALT_computable' [propext, sorryAx, Classical.choice, Quot.sound]
   'Complexity.HALT_not_computable'        [propext, sorryAx, Classical.choice, Quot.sound]
   ```

   The nine construction theorems are fully machine-checked with no `sorryAx`.
   The four assembly theorems inherit `sorryAx` exactly through their declared
   unfilled dependencies (`one_work_tape`/`alphabet_reduction` via
   `one_work_tape_binary`; `universal`; `exists_comp_partial`) — by design:
   epoch 1A machine-checked the *assembly*, and these footprints clear as
   epochs 2-3 fill the constructions.
4. **Soundness scan.** No added `axiom`, `native_decide`, `implemented_by`,
   `extern`, `unsafe`, `set_option`, or attribute lines anywhere in the diff;
   all new declarations are `private`. New imports:
   `Mathlib.Data.Fintype.{Vector,Sum,Prod,Option,EquivFin}` (precise, per use).
5. **Delivery provenance.** The agents could not push (no repository write
   credentials on the runners); deliveries arrived as archives whose git
   bundles/patches, standalone sources, and hashes were mutually consistent
   and based on `9f735248` exactly. Agent-side verification environments used
   a small `readlink` compatibility shim; it is moot for trust purposes —
   attestations 1-4 above were produced on the maintainer's machine from the
   integrated tree. The four agent reports are attached
   (`audits/epoch1-agent-reports/`), including their own logs and claims.

## What was filled

| Batch | Now proved | New private declarations (blind-restate; all `private`, per-file) |
|---|---|---|
| A (assemblies) | `Computes.exists_computesFunInTime`, `UC_not_computable`, `universal_quadratic`, `UC_computable_of_HALT_computable` | `Complexity.halts_iff_eq_of_computes` (Halting.lean) |
| B (Composition.lean) | `computesFunInTime_const`, `computesFunInTime_ifEq`, `exists_cond` | `emitAction`, `emit_run`, `emit_halts`, `constTM`, `controlAction`, `controlAction_apply`, `inputSymbol_at`, `ifEqTM`, `ifEq_finish`, `ifEq_run`, `leftAction`, `rightAction`, `leftCfg`, `rightCfg`, `leftCfg_apply`, `rightCfg_apply`, `leftCfg_step`, `rightCfg_step`, `leftCfg_run`, `rightCfg_run`, `computesInTime_iff`, `branchTM`, `branchTM_computes`, `moveInputPos_neg_val`, `rewind_scan`, `rewind_from_any`, `condTM`, `controlCfg`, `controlCfg_step`, `controlCfg_run`, `condTM_start` |
| C (Encoding.lean) | `pairEncode_injective`, `computesFunInTime_pairEncode_diag`, `exists_codeTM` | `pairDecode`, `pairDecode_pairEncode`, `pairDiagTM`, `pairDiagCfg`, `pairDiag_step`, `pairDiag_inner`, `pairDiag_right`, `pairDiag_double`, `pairDiag_rewind`, `pairDiag_copy`, `pairDiag_separator`, `pairDiag_run`, `codeMapAction`, `codeMapCfg`, `codeMapCfg_apply`, `codeRelabelTM`, `codeRelabel_step`, `codeRelabel_run` |
| D (Examples, TimeConstructible) | `PAL_mem_DTIME_linear`, `timeConstructible_id` | `palTM`, `palTape`, `palCfg`, `palTape_write`, `pal_copy_step`, `pal_copy`, `pal_copy_end`, `pal_rewind_step`, `pal_rewind`, `pal_test_start`, `pal_test_read`, `pal_test_step`, `palMatches`, `palMatches_succ`, `pal_test`; `counterInc`, `counterCarry`, `counterInc_potential`, `counterInc_bits`, `counterInc_length`, `counter_bits_length`, `counterBump`, `counterTM`, `counterTape`, `counterCfg`, `counterTape_read`, `counterTape_write`, `counter_carry_step`, `counter_carry`, `counter_rewind`, `counter_start`, `counter_increment`, `counter_count`, `counter_emit_run`, `counter_emit` |

Since every new declaration is `private` and consumed only by proofs of frozen,
audited statements, and the headline theorems are existential over machines, a
defective private helper cannot make a headline theorem *false* — only its
proof, which Lean checks. The audit interest in the private layer is therefore
targeted: the items below.

## Brief for the auditor

Ground rules as in all previous rounds (trusted surface; no blanket approval;
tactic scripts out of scope). Priority order:

1. **Verify the freeze attestation independently**: comment-stripped comparison
   of every declaration in the six modified Lean files between `9f735248` and
   `d3393b35`; confirm the three docstring appendices describe the delivered
   implementations accurately and change no mathematical claim.
2. **Blind-restate the promotion candidates** — the private declarations the
   epoch merge may make public (question 1) — as these are about to become
   trusted surface: `halts_iff_eq_of_computes` (A), `computesInTime_iff` (B),
   and C's state-renaming suite (`codeMapAction` … `codeRelabel_run`).
3. **Spot-check delivered machines against their audited sketches** (not the
   tactics — the *definitions*): does `pairDiagTM` implement the corrected
   `4n + 5` schedule of phase-4 finding 1; does `palTM` implement the phase-1
   findings' copy/rewind/test table with the audited boundary transitions; does
   `counterTM` implement the four-state counter with the potential accounting
   (`counterInc_potential` as the local identity); does `condTM` implement the
   register/rewind/dispatch design of phase-4 finding 4, including the
   first-emission register (`Option.or`), the live administrative state after
   the simulated halt, and the safe halt on an empty register?
4. **Confirm the 9 remaining sorries** match their audited forms and that their
   sketches remain implementable over the now-existing gadget vocabulary
   (epoch 2 builds `exists_comp_partial`/`computesFunInTime_comp` on B's
   `leftCfg`/`rightCfg` lockstep and rewind gadgets).
5. Assess attestations 2-5, including the axiom-footprint reasoning for the
   four assembly theorems.

## Specific questions

1. **Shared-lemma promotions at epoch merge** (from the agent reports):
   (a) batch A requests the completed-output characterization
   `(∃ t, M.ComputesInTime x w t) ↔ w = g x` (for `M.Computes g`) as
   `Turing.FinTM.Computes.halts_iff_eq` in `Finite.lean`; (b) batch B's
   `computesInTime_iff` (drop the space witness) overlaps it and serves the
   same role; (c) batch C requests a shared, non-vendored state-renaming module
   unifying its `codeMap*`/`codeRelabel*` suite with `Oracle.lean`'s embedding
   machinery. Which promotions, names, and homes do you endorse? Anything about
   their statements to fix *before* they become public API?
2. The docstring appendices (on `timeConstructible_id`, `exists_cond`,
   `exists_codeTM`): accurate, and appropriately scoped to implementation
   notes?
3. `exists_codeTM`'s witness sets `numStates := Fintype.card State - 1` via
   `Fintype.equivFinOfCardEq` — any objection to the card arithmetic at
   degenerate instances (the state type is inhabited by `q₀`, so the card is
   positive)?
4. Batch D's amortization: `counter_count`'s invariant
   `t + 2 · popcount(i) ≤ 4i` with `counterInc_potential` — confirm the
   arithmetic yields the claimed `c = 5` bound including `n = 0`, and that
   `counterInc_bits` is the right bridge to `Nat.bits` (LSB-first, no
   redundant zeros).
5. Is anything in the new private layer *accidentally load-bearing* beyond its
   file — e.g. a helper whose statement, if wrong, would silently weaken a
   *future* fill that the epoch-2 briefs will tell agents to reuse?
6. The four assembly proofs use the forward evaluator clause only, one
   evaluator witness chosen once per proof, per Argument F — confirm from the
   sources that no proof silently requires the converse clause or a globally
   named evaluator (statement-level check; the tactics are Lean-checked).

## Scope

| Item | Where |
|---|---|
| Files under audit | The six modified modules: `TuringMachine/{Composition,Encoding,Universal}.lean`, `Uncomputability/{Computable,Diagonalization,Halting}.lean`, `ClassP/{Examples,TimeConstructible}.lean`; all 19 modules attached for context |
| Source text | Arora & Barak 2009, §§1.2-1.5.1 (PDF pp. 35-49), for the sketch-conformance spot checks |
| Context | `AroraBarakChapter1Plan.md` (campaign schedule + decision log), `policy.md`, `audits/phase4-{findings,resolutions}.md`, `briefs/epoch1-batch{A-D}.md`, agent reports in `audits/epoch1-agent-reports/` |
| Out of scope | tactic proofs (Lean-checked, axiom-audited above); statements confirmed in closed rounds beyond the freeze check; the agents' runner environments (superseded by maintainer-side verification) |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.

---

# ATTACHMENT A — Agent delivery reports (per batch)

## ===== audits/epoch1-agent-reports/batchA.md =====

The audited phase-3/4 interfaces had not yet been checked together in the four Batch A assembly proofs. This PR fills those proofs using the stated normalization, coding, evaluator, and guarded-composition interfaces.

Base: `complexity/arora-barak-ch1` at `9f735248212c1d1d842b299b431b2b680220ac5b`. Head: `fill/epoch1-A`.

- [x] **Targets filled (4).**
  - `Turing.FinTM.Computes.exists_computesFunInTime`: follows the sketch, choosing halting times and taking their `Finset.univ.sup` over `List.Vector Symbol n`, then applying `ComputesInTime.mono`. No positivity, monotonicity, or nonempty-alphabet assumption is added.
  - `Complexity.UC_not_computable`: follows the audit derivation through binary one-work-tape normalization, `exists_codeTM`, `decode_encode`, and the two Boolean cases using output uniqueness. The statement still covers arbitrary `MachineCode`.
  - `Turing.universal_quadratic`: follows the sketch with one universal-machine witness, the normal-form code, only the forward evaluator clause, and the in-repo constant-absorption calculation.
  - `Complexity.UC_computable_of_HALT_computable`: follows the audit construction with three partial compositions, the fixed-word postprocessor, the constant branch, and `exists_cond`. The positive HALT witness justifies the forward evaluator clause; no totality of the evaluator or converse evaluator clause is used.
- [x] **New declarations added:** exactly one private helper, `Complexity.halts_iff_eq_of_computes`, in `Halting.lean`; no new public declarations. Its complete signature is below for audit restatement.
- [x] **Requested shared lemmas:** at epoch integration, consider moving the generic completed-output lemma below into `Finite.lean`, e.g. as `Turing.FinTM.Computes.halts_iff_eq`. This PR keeps its copy private in its owned file and does not edit the shared file.
- [x] **Escalations:** none.
- [x] **Verification evidence:** all 22 modules in `scripts/ab_ch1_module_order.txt` passed the final direct-`lean` sweep, with zero `error:` lines and exactly the 17 stipulated out-of-scope `declaration uses 'sorry'` warnings. Each edited module and every later module were rechecked during iteration. The final complete per-module log is included below.
- [x] **Diff touches only the owned files:** `Uncomputability/{Computable,Diagonalization,Halting}.lean` and only the `universal_quadratic` proof in `TuringMachine/Universal.lean`. All pre-existing statements, hypotheses, names, options, attributions, and docstrings are retained. The only removed lines are the four target `sorry`s. No new `sorry`, axiom, or admission was introduced. `git diff --check` passes.

```lean
private theorem halts_iff_eq_of_computes {Symbol : Type} {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x
```

All four delivered proofs match their existing sketches; no docstring updates were needed. As intended by the brief, they retain dependencies on the unfilled construction theorems. The full-sweep warning locations were checked against the brief's exact set of 17 declarations. The other three warnings are unchanged style/unused-variable warnings in the unowned `Configuration.lean`, also shown below.

Verification environment: Lean 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, and the unchanged repository manifest. The full cache download was narrowed to the 15 Mathlib roots imported by this sweep and their transitive dependencies (876 cache files). All TCSlib checks used the prescribed `scripts/lean_check_tree.sh`; no `lake build` was used to check TCSlib. The cloud runner exposes a procfs/PID-namespace mismatch, so a local, out-of-repository compatibility shim maps only `readlink("/proc/<own getpid()>/exe", ...)` to the equivalent `/proc/self/exe`; no Lean binary, proof checker, dependency source, or repository script was modified. Cache archive extraction used `TAR_OPTIONS=--no-same-owner` for the runner's UID mapping. Each scratch `.olean` was removed before its check and required to be regenerated successfully.

Verified source commit: `3d1a82c9cb6dad4ca348a3d7cfc07f37da3e05cd`.

Final full-sweep log (exit 0; zero `error:` lines; 22 modules; 17 expected sorry warnings):

```text
[check] TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
[check] TCSlib/Complexity/TuringMachine/Deterministic

[check] TCSlib/Complexity/TuringMachine/Finite

[check] TCSlib/Complexity/TuringMachine/Oracle

[check] TCSlib/Complexity/TuringMachine/Composition
TCSlib/Complexity/TuringMachine/Composition.lean:162:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:179:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:201:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:249:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:275:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean:69:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:68:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean:76:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/ClassP/DTIME

[check] TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/ClassP/TimeConstructible.lean:85:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:109:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/ClassP/P

[check] TCSlib/Complexity/ClassP/ModelInvariance

[check] TCSlib/Complexity/ClassP/Examples
TCSlib/Complexity/ClassP/Examples.lean:69:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/TuringMachine/Encoding.lean:117:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:137:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:252:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:265:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:102:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:165:8: warning: declaration uses 'sorry'
[check] TCSlib/Complexity/Uncomputability/Computable

[check] TCSlib/Complexity/Uncomputability/Diagonalization

[check] TCSlib/Complexity/Uncomputability/Halting

[check] TCSlib/Complexity/TuringMachine

[check] TCSlib/Complexity/ClassP

[check] TCSlib/Complexity/Uncomputability
```

## ===== audits/epoch1-agent-reports/batchB.md =====

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

## ===== audits/epoch1-agent-reports/batchC.md =====

Completes the three audited Epoch 1 Batch C obligations in `Encoding.lean`, relative to `complexity/arora-barak-ch1` at `9f735248212c1d1d842b299b431b2b680220ac5b`. The existing theorem statements and attributions are unchanged; `exists_effectiveMachineCode` and its proof sketch remain byte-identical.

## Targets filled

- [x] `Turing.pairEncode_injective`: a private aligned two-bit parser recovers both components by induction, and equality after parsing proves injectivity, as sketched.
- [x] `Turing.computesFunInTime_pairEncode_diag`: an explicit six-state, zero-work-tape machine follows the audited schedule. Whole-configuration invariants prove completion by `4 * input.length + 5` transitions, including empty input; `ComputesInTime.mono` supplies the stated bound with constant 6.
- [x] `Turing.exists_codeTM`: relabel states with `Fintype.equivFinOfCardEq`, prove action/step/run correspondence, and recover both directions of the time/output equivalence. The tape-count equality is eliminated after destructuring the bundle, avoiding casts in transition proofs.

## New declarations

- [x] All 18 new explicitly declared helpers are private; no new public declaration is exported. In particular, the parser is not exported for the later canonizer fill.

| Private declaration in `Turing` | Purpose |
| --- | --- |
| `pairDecode` | Aligned doubled-bit parser; the separator leaves the suffix unchanged. |
| `pairDecode_pairEncode` | Parser round trip on encoded pairs. |
| `pairDiagTM` | Six-state diagonal-pairing controller. |
| `pairDiagCfg` | Configurations of the zero-work-tape controller. |
| `pairDiag_step` | One controller transition given its scanned input symbol. |
| `pairDiag_inner` | Read the input bit at an interior head position. |
| `pairDiag_right` | Read blank at the right boundary, including empty input. |
| `pairDiag_double` | Doubled-prefix invariant for the first pass. |
| `pairDiag_rewind` | Leftward rewind and return to initial input position. |
| `pairDiag_copy` | Prefix invariant for the second pass. |
| `pairDiag_separator` | Two separator emissions and the first unconditional left move. |
| `pairDiag_run` | Complete halted configuration by the audited time bound. |
| `codeMapAction` | Map only an action's successor state. |
| `codeMapCfg` | Map only a configuration's optional state. |
| `codeMapCfg_apply` | Action application commutes with state mapping. |
| `codeRelabelTM` | Transport a transition table through a state equivalence. |
| `codeRelabel_step` | Step commutation, including absorbing halting. |
| `codeRelabel_run` | Initialized run correspondence at every time. |

## Requested shared lemmas

- [x] At epoch merge, consider placing the generic state-renaming support in a non-vendored shared module: make the existing `Oracle.lean` action-state mapping available there, and share configuration mapping, action/step commutation, and run correspondence. This batch keeps `codeMapAction`, `codeMapCfg`, `codeMapCfg_apply`, `codeRelabelTM`, `codeRelabel_step`, and `codeRelabel_run` private to honor file ownership. Neither vendored file is edited.

## Escalations

- [x] None concerning theorem statements or proof obligations.

## Documentation and statement freeze

The only existing docstring change is an appended implementation note on `exists_codeTM`, identifying the private action mapper, elimination of the tape-count equality, and use of `runFrom_comm_of_step`. All existing proof sketches are retained. A comment-stripped comparison checked all 18 pre-existing declaration headers; none changed.

## Verification

- [x] Lean 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- [x] Dependency-order bootstrap and repeated `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Encoding` checks completed. The final full sweep checked all 22 modules from `scripts/ab_ch1_module_order.txt`, including Universal, all Uncomputability files, and the facades: zero `error:` lines.
- [x] Exactly 18 remaining `sorry` warnings, all at declarations listed as out of scope in the brief. `Encoding.lean` has one, at `exists_effectiveMachineCode`. Its isolated check has no other warnings. The full sweep also reports three pre-existing linter warnings in frozen `Configuration.lean`.
- [x] A temporary `#print axioms` check showed no `sorryAx` dependency in any filled theorem. The temporary commands are absent from the final source.
- [x] `git diff --check` passes; the diff touches only `TCSlib/Complexity/TuringMachine/Encoding.lean`.

Verification used only the authorized direct-Lean script; `lake build` was never run. The environment required an executable-path compatibility shim mapping the running process's `/proc/<its-pid>/exe` lookup to `/proc/self/exe`; the pinned Lean binaries and sources were unchanged. After the initial full-cache attempt, a task-local cache download populated all direct imports and their transitive dependencies.

Elaborated axiom evidence:

```text
'Turing.pairEncode_injective' depends on axioms: [propext, Quot.sound]
'Turing.computesFunInTime_pairEncode_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_codeTM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Final full-sweep log tail:

```text
TCSlib/Complexity/ClassP/TimeConstructible.lean:85:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:109:8: warning: declaration uses 'sorry'


TCSlib/Complexity/ClassP/Examples.lean:69:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Encoding.lean:454:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:102:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:124:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Universal.lean:148:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Computable.lean:64:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Diagonalization.lean:98:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Uncomputability/Halting.lean:139:8: warning: declaration uses 'sorry'



Full sweep: 22/22 modules checked.
```


## ===== audits/epoch1-agent-reports/batchD.md =====

This fills the two audited machine-construction proofs assigned by `briefs/epoch1-batchD.md`, based on `complexity/arora-barak-ch1` at `9f735248212c1d1d842b299b431b2b680220ac5b`. Both machines are explicit finite one-work-tape machines, with complete run invariants and all-length bounds.

## Targets filled

- [x] `Complexity.PAL_mem_DTIME_linear`: follows the audited copy/rewind/test construction, including all boundary transitions and early rejection; establishes the budget `3 * (n + 1)`, including the three-step accepting empty-input run.
- [x] `Complexity.timeConstructible_id`: follows the reaudit's four-state count/carry/rewind/emit table. Uses the **potential route**: `elapsed + 2 * popcount(i) ≤ 4 * i`. An increment with `r` initial true bits costs exactly `2 * r + 2`, while the potential changes by `2 - 2 * r`. Final emission writes exactly `Nat.bits n` and yields `5 * (n + 1)` total budget; empty input emits `[]` and halts in two steps.

The original theorem statements, names, hypotheses, imports, option headers, and `[AB09 …]` attributions are unchanged. Existing docstrings are retained. The only update to an existing docstring appends the explicit potential and `c = 5` calculation to `timeConstructible_id`'s proof sketch; neither construction deviates from its audited transition table.

## New declarations

- [x] All **35** new explicit declarations are private, in namespace `Complexity`; no new public declarations.

`TCSlib/Complexity/ClassP/Examples.lean` (15):

`palTM`, `palTape`, `palCfg`, `palTape_write`, `pal_copy_step`, `pal_copy`, `pal_copy_end`, `pal_rewind_step`, `pal_rewind`, `pal_test_start`, `pal_test_read`, `pal_test_step`, `palMatches`, `palMatches_succ`, `pal_test`.

`TCSlib/Complexity/ClassP/TimeConstructible.lean` (20):

`counterInc`, `counterCarry`, `counterInc_potential`, `counterInc_bits`, `counterInc_length`, `counter_bits_length`, `counterBump`, `counterTM`, `counterTape`, `counterCfg`, `counterTape_read`, `counterTape_write`, `counter_carry_step`, `counter_carry`, `counter_rewind`, `counter_start`, `counter_increment`, `counter_count`, `counter_emit_run`, `counter_emit`.

Standalone arithmetic/list lemmas worth considering for later promotion are `counterInc_potential` (the local carry/popcount identity), `counterInc_bits` (exact compatibility with `Nat.bits`), `counterInc_length`, and `counter_bits_length`. The tape representation and its read/write lemmas remain private to this construction.

## Requested shared lemmas

- [x] None required. No shared or vendored file was modified.

## Escalations

- [x] None. Both targets were proved as stated.

## Verification

- [x] Direct Lean checks after proof edits, using `scripts/lean_check_tree.sh`; both owned files now produce no warnings or errors.
- [x] Final complete sweep over all 22 modules in `scripts/ab_ch1_module_order.txt`, including every later module: **zero `error:` lines**. All 19 remaining `sorry` warnings correspond to the brief's untouched out-of-scope declarations.
- [x] `#print axioms` for both completed targets reports only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, additional axiom, or unchecked proof dependency.
- [x] Existing declaration headers compared byte-for-byte with the pinned base; unchanged. `git diff --check` passes.
- [x] Diff touches only the two owned files: `Examples.lean` and `TimeConstructible.lean`.

Toolchain: official Lean 4.25.0, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Dependency setup started with `lake exe cache get`; the cache download was narrowed to the chapter's exact imports and unpacked after a concurrent cache process removed the shared curl configuration. No dependency source was changed. The container needed a local executable-path compatibility shim: only the current process's `/proc/<pid>/exe` lookup is redirected to `/proc/self/exe`, because its PID namespace and mounted procfs differ. Lean's compiler, kernel, and library binaries were not modified. Verification used the designated direct-`lean` script, never a repository `lake build` command.

Final sweep command:

```bash
while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt
```

Final full-sweep log tail:

```text


TCSlib/Complexity/TuringMachine/Composition.lean:162:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:179:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:201:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:249:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Composition.lean:275:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean:69:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:68:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean:76:8: warning: declaration uses 'sorry'


TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:109:8: warning: declaration uses 'sorry'



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

---

# ATTACHMENT B — Context documents

## ===== AroraBarakChapter1Plan.md =====

# Formalization Plan: Arora-Barak Chapter 1

**Branch:** `complexity/arora-barak-ch1` · **Governing standards:** [`policy.md`](policy.md)

This document is the working plan for formalizing Chapter 1 of Arora & Barak,
*Computational Complexity: A Modern Approach* (CUP 2009) — "The computational model — and
why it doesn't matter" (book pages 9–37) — in TCSlib. It records the foundation decision,
the architecture that keeps the model robust to variations (oracles, nondeterminism), the
module layout, and the phasing. Source tag throughout the development: `[AB09]`.

## 1. Scope: what Chapter 1 contains

| Section | Content | In scope |
|---|---|---|
| §1.2 | k-tape TM `(Γ, Q, δ)`: read-only input tape, work tapes, output tape (read-write in [AB09]; append-only write-only in our model — a variation [AB09, p. 19] itself sanctions, declared in `DTIME.lean`); start configuration; halting; Example 1.1 (palindromes in 3n steps) | Yes |
| §1.3 | Computing `f` in time `T(n)` (Def 1.3); time-constructibility; Claim 1.5 (alphabet reduction, `4 log|Γ|` slowdown); Claim 1.6 (k tapes → 1 tape, `5kT²`); Remark 1.7 (oblivious TMs); Claim 1.8 (bidirectional → unidirectional, `4T`) | Yes (oblivious: statement only at first) |
| §1.4 | Machines as strings: every string decodes to some TM, every TM has infinitely many encodings; universal TM; Theorem 1.9 (universal simulation), relaxed `O(T²)` version; time-bounded universal TM | Yes |
| §1.5 | Uncomputability: `UC` via diagonalization (Thm 1.10); `HALT` via reduction (Thm 1.11); §1.5.2 Gödel discussion | Thms 1.10–1.11 yes; Gödel material is prose — out of scope |
| §1.6 | `DTIME(T(n))` (Def 1.12, with constant absorption), `P` (Def 1.13), examples | Yes |
| §1.7 | Hennie-Stearns `O(T log T)` universal simulation (amortized zone argument) | Stretch goal, off the critical path |

Additionally in scope, ahead of the book's own ordering: the **oracle TM** definition
(the book defers it to §3.4). We pull it forward to validate that the architecture supports
model variations before the expensive theorems are built on it.

## 2. Foundation decision

**Decision: vendor cslib's multi-tape TM model; do not build on Mathlib's TMs; do not take
cslib as a dependency.** Findings behind this (surveyed Sept 2026, against our pinned
mathlib `029db123ddaa`, toolchain v4.25.0):

- **Mathlib** is a computability library, not a complexity library. It has no multi-tape TM
  (TM0/TM1 are single-tape, TM2 is a stack machine); its model-simulation theorems carry no
  time bounds; `TM2ComputableInPolyTime` is a stub whose only instance is `id`. Building
  Arora-Barak on it means fighting the design. What we do reuse: `Language`,
  `Turing.FinEncoding`, and (later, as an optional bridge) the recursion-theory stack
  (`Nat.Partrec`, `Halting`/Rice, `Reduce`, `RecursiveIn`).
- **cslib** (github.com/leanprover/cslib, `Cslib/Computability/Machines/Turing/MultiTape/`,
  Apache-2.0) has an Arora-Barak-style `MultiTapeTM` (its write-only output tape is an
  [AB09, p. 19]-sanctioned variation of the book's read-write one): read-only input
  tape, k work tapes, explicit time and space semantics, a nondeterministic
  variant, and configuration-count bounds — actively developed, with a complexity roadmap
  (issue #611) that plans oracles as a wrapper over any model.
- **Why vendor rather than depend:** cslib targets Lean v4.35.0-rc1 with the new module
  system; TCSlib is pinned to v4.25.0 and the PFR dependency chains us there. The vendored
  surface is small (~1,400 lines). We stay structurally aligned with upstream so we can
  migrate to a real dependency at the next toolchain bump, and upstream anything we prove
  that they lack (universal TM, robustness claims).
- Vendored files follow `policy.md` §2: original copyright headers preserved, source commit
  recorded, local modifications listed (expected: de-module-system syntax, import-path
  ports to v4.25 mathlib).

Reference mechanization to mine for proof architecture: the Isabelle AFP entry
`Cook_Levin` (Balbach) — the only completed Arora-Barak-faithful development. Its lemma
decomposition, especially for TM composition and the universal machine, transfers.

## 3. Architecture

### 3.1 The Action/apply split (model variations)

cslib's configuration layer mentions no machine: a step is an **`Action`** (input-head
move, per-work-tape write/move, optional output symbol, successor state) plus
**`Action.apply`** (its effect on a configuration). A *machine* is then just the thing
that **chooses** the action from the current state and read symbols. Every model twist is a
different chooser over the same configurations, the same `apply`, and the same run/time/
space measures:

| Model | Chooser |
|---|---|
| Deterministic TM (Ch. 1) | function `State × reads → Action` |
| Nondeterministic TM (Ch. 2) | relation over actions |
| Oracle TM (§3.4, Definition 3.4, pulled forward) | function consulting `O : Language _` via query tape and `q_query`/`q_yes`/`q_no` states (pairwise distinct: `OracleTM.WellFormed`) |
| Probabilistic TM (Ch. 7, future) | two transition functions + coin |

Because `DTIME`-style definitions are stated over the shared run layer, `P`, `Pᴼ`, and
later `NP`/`BPP` are instances of one pattern, not parallel developments. Phase 1 locks
the design with sanity theorems in both directions: a plain machine embeds as an oracle
machine whose runs are in lockstep with the original under *every* oracle
(`ofMultiTapeTM`), and conversely an oracle machine run with the empty oracle is
eliminated into a plain machine in exact lockstep (`plainEmptyOracle`).

### 3.2 Finiteness: raw layer vs. bundled layer

Finiteness of `Γ` and `Q` is mathematically non-negotiable: with infinite states, δ can
memorize the input and decide any language in linear time (P would collapse to all
languages), and `⌞M⌟` has no finite representation. The design question is only *where*
the hypothesis lives:

- **Raw layer** (`MultiTapeTM k Γ Q`, parametric types, no finiteness): configurations,
  `step`, runs, time/space counting, and simulation *constructions*. Deferring finiteness
  here keeps semantics lemmas clean and lets compound state types (`Q × Γᵏ`, `Option Q`,
  sums) arise without instance-threading; finiteness of a constructed machine is an
  afterthought (`inferInstance`). This follows both cslib and mathlib TM0/TM1 practice.
- **Bundled layer** (`FinTM Symbol`: a raw machine bundled with `Fintype`/`DecidableEq`
  instances for its *state* type — analogous to mathlib's `FinTM2`): **all headline
  definitions and theorems** — `DTIME`, `P`, `⌞M⌟`, Theorem 1.9, oracle classes — are
  stated exclusively over the bundled layer, so a finiteness hypothesis can never be
  forgotten. The alphabet is *not* bundled: it stays an explicit parameter, fixed to
  `Bool` by the headline classes; results over a general `Symbol` (e.g. machine
  encodings) take `[Fintype Symbol]`/`[DecidableEq Symbol]` at their statements, and
  oracle complexity classes (Ch. 3) will introduce a finite oracle-machine bundle
  before they are defined. Encoding needs `Fintype`/`DecidableEq` as *data* (δ's table
  must be enumerated), which is why the bundle carries instances rather than `Finite`
  propositions.

Per `policy.md` §1 (layering), the raw layer is internal plumbing; the bundled layer is
the textbook object.

### 3.3 Conventions

- **Strings/languages:** `{0,1}*` as in the book; languages via mathlib's `Language`.
- **Namespaces:** `Turing` for the vendored core (minimizes diff against upstream; no
  clashes with mathlib's `Turing.*` at our pin), `Complexity` for classes and
  uncomputability. Revisit only if a clash appears.
- **NP/NTM:** strictly Chapter 1 here. cslib's nondeterministic file is in the vendorable
  set but lands with the Chapter 2 effort.

## 4. Module layout

Per `policy.md` §1: facades, 150–600-line files, precise imports, `TCSlib.lean` exports.

```
TCSlib/Complexity/TuringMachine.lean          -- facade + module docstring
TCSlib/Complexity/TuringMachine/
  Configuration.lean      -- Cfg, Action, Action.apply, space measure   [vendored]
  Deterministic.lean      -- MultiTapeTM, run, ComputesInTime(AndSpace) [vendored]
  Finite.lean             -- bundled FinTM layer (§3.2)
  Oracle.lean             -- oracle wrapper over the same Cfg/Action layer
  Composition.lean        -- sequential composition, basic combinators
  Robustness/
    AlphabetReduction.lean  -- [AB09, Claim 1.5]
    SingleTape.lean         -- [AB09, Claim 1.6]
    Bidirectional.lean      -- [AB09, Claim 1.8]
    Oblivious.lean          -- [AB09, Remark 1.7] (statement; proof deferred)
  Encoding.lean           -- ⌞M⌟ : TM ↔ string; totality + padding [AB09, §1.4]
  Universal.lean          -- [AB09, Thm 1.9] relaxed O(T²) + timed variant
  UniversalEfficient.lean -- [AB09, §1.7] Hennie-Stearns O(T log T)  [stretch]
TCSlib/Complexity/Uncomputability.lean        -- facade
TCSlib/Complexity/Uncomputability/
  Computable.lean         -- computable functions, no time bound [AB09, §1.4-§1.5]
  Diagonalization.lean    -- UC, [AB09, Thm 1.10]
  Halting.lean            -- HALT, [AB09, Thm 1.11]
  MathlibBridge.lean      -- link to Nat.Partrec / Rice  [optional, later]
TCSlib/Complexity/ClassP.lean                 -- facade
TCSlib/Complexity/ClassP/
  DTIME.lean              -- decides, DTIME with constant absorption [AB09, Def 1.12]
  TimeConstructible.lean  -- time-constructibility [AB09, §1.3]
  P.lean                  -- P, closure basics, model-invariance [AB09, Def 1.13]
  Examples.lean           -- PAL ∈ DTIME(n+1) [AB09, Ex 1.1]; selected Ex 1.14
```

## 5. Phasing

Each phase lands first as a **compiling sorry-skeleton** (the GraphTheory/Core precedent):
statements are the contract, proofs fill in via the sorry-ladder workflow. Per `policy.md`
§3, proof sketches are written at skeleton time — each `sorry` corresponds to a named
sketch step. After each phase compiles: dep-graph rebuild, `/blueprint-extract`,
`blueprint_validate.py --strict`, `dataset_hygiene.py --strict`. The blueprint is
**late-bound**: extraction runs only at phase boundaries, and no blueprint LaTeX is
written by hand ahead of the Lean.

### Audit protocol (between phases)

Right after a phase's skeleton lands — statements frozen, proofs mostly `sorry` — an
**external audit** runs before the next phase begins: an LLM from a different vendor, in
a fresh context, reviews the phase's trusted surface (definitions, theorem statements,
remaining sorries) against the book, adversarially. Statement bugs are the dominant
failure mode of formalization (Lean already checks proofs) and are cheapest to fix at
this moment. Mechanics: instantiate `audits/TEMPLATE.md` as `audits/phaseN-pack.md`, hand
it plus the listed files to the auditor, record results in `audits/phaseN-findings.md`;
every finding is fixed or explicitly waived before the next phase starts. An optional
light second pass when a phase's proofs complete diffs the statements for quiet
weakening. Audits complement, not replace, in-Lean sanity theorems, which are the
machine-checked and permanent form of the same checks.

1. **Core model + classes.** Port the two vendored files to v4.25; `Finite.lean`;
   `ComputesInTime`, `decides`, `DTIME`, `P`; the oracle wrapper + trivial-oracle sanity
   theorem; PAL as an end-to-end usability check. *This phase alone unblocks future
   chapters (NP needs only these definitions).*
2. **Robustness.** Claims 1.5, 1.6, 1.8; `Composition.lean` combinators; corollary that P
   is invariant under the model tweaks. First real machine-construction proofs — builds
   the simulation vocabulary everything later reuses. The convention obligations
   recorded by the phase-1 audit are dispositioned per the phase-2 audit (findings 3
   and 13): the append-only-output and initialization bridges are **waived** (no
   read-write-output model is formalized; no exact step count is ever imported from
   [AB09]), to be revisited only if a downstream result needs a formal bridge; the
   persistent vs auto-erased query-tape statement (polynomial overhead only — constant
   overhead provably impossible) moves to the Chapter 3 oracle-class work.
3. **Encodings + universal machine.** `⌞M⌟` with totality and padding lemmas; Theorem 1.9
   in the relaxed `O(T²)` form (U simulates the one-work-tape *binary* normal form from
   phase 2 — `FinTM Bool`, i.e. three tape symbols counting blank; if the construction
   wants [AB09]'s four-symbol alphabet, that is an additional named embedding step) and
   the time-bounded variant.
4. **Uncomputability.** Thm 1.10 (needs only encoding + semantics; the diagonalization is
   short); Thm 1.11 (needs composition + the universal machine). Proof blueprints for
   both are in `audits/phase3-reaudit-findings.md`, Argument F. Scope additionally
   includes the API pieces that audit identified: a **guarded/partial composition (or
   guarded-simulation) lemma** with buffered intermediate output — the total-function
   `computesFunInTime_comp` cannot take the partial evaluator as a component — and,
   where a proof needs a globally chosen evaluator or a semantically identified code,
   an explicitly stated named-evaluator interface.
5. **Stretch — explicitly off the critical path, and deferred to a much later
   effort.** §1.7's `O(T log T)` simulation; oblivious TMs; the RAM-TM exercise
   (Ex 1.9); the mathlib recursion-theory bridge. **Not scheduled** (decision of
   2026-09-16): phase 5 is a task for much later — it is not part of the current
   push, no audit pack will be prepared for it, and it is revisited only after the
   phase-1-4 fill campaign completes. Chapter 1's critical path *ends with phase 4*.

### Fill campaign (epochs and batches)

With all four phase gates closed, the remaining critical-path work is filling the
21 audited-true sorries. The campaign runs in **epochs** — sequential, with an
audit round at each epoch boundary — each consisting of **batches** run in
parallel, one agent per batch, with disjoint file ownership. Difficulty points
(1-15 scale) are planning estimates. Agents work in the cloud from the
self-contained briefs in `briefs/`, branching off `complexity/arora-barak-ch1`
and PRing back into it (`github.com/Shilun-Allan-Li/tcslib`). Verification is
`scripts/lean_check_tree.sh` over `scripts/ab_ch1_module_order.txt` (direct
`lean`; `lake build` stays banned).

| Epoch | Batch | Contents (points) | Owned files |
|---|---|---|---|
| **1** | 1A | `Computes.exists_computesFunInTime` (2), `UC_not_computable` (2), `universal_quadratic` (2), `UC_computable_of_HALT_computable` (3) — the assembly/integration tests | `Uncomputability/{Computable,Diagonalization,Halting}.lean`, `Universal.lean` (quadratic only) |
| 1 | 1B | `computesFunInTime_const` (2), `computesFunInTime_ifEq` (3), `exists_cond` (6) | `Composition.lean` |
| 1 | 1C | `pairEncode_injective` (3), `computesFunInTime_pairEncode_diag` (4), `exists_codeTM` (5) | `Encoding.lean` |
| 1 | 1D | `PAL_mem_DTIME_linear` (4), `timeConstructible_id` (5) | `Examples.lean`, `TimeConstructible.lean` |
| **2** | 2A | `exists_comp_partial` (8) then `computesFunInTime_comp` (7) — shared infrastructure, sequential within the batch | `Composition.lean` |
| 2 | 2B | `one_work_tape` (12) | `Robustness/SingleTape.lean` |
| 2 | 2C | `nonnegative_heads` (7), `alphabet_reduction` (8) | `Robustness/{Bidirectional,AlphabetReduction}.lean` |
| **3** | 3A | `exists_effectiveMachineCode` (13) | `Encoding.lean` |
| 3 | 3B | `universal` (15) | `Universal.lean` |
| 3 | 3C | `oblivious_of_mem_DTIME` (12) — droppable per the phase-5 deferral without reopening any gate | `Robustness/Oblivious.lean` |
| **4** | 4A | `timed_universal` (10), reusing `universal`'s infrastructure | `Universal.lean` |
| 4 | — | Closure: zero-sorry sweep with build evidence (phase-4 finding 8), final drift attestation across all gates, fill-round audit pack, `/blueprint-extract` | — |

Epoch loads: ≈ 41 / 42 / 40 / 10 points. Rationale: epoch 1 maximizes
risk-retirement per point (the assemblies machine-check that the phase-3/4
interfaces compose; the machine batches validate the invariant pattern at small
scale), epoch 2 retires the two biggest technique risks (guarded composition
with buffered output; sweep-based simulation), epoch 3 climbs the summit with
every needed technique already precedented in-repo, epoch 4 is wind-down.

**Ground rules** (binding on every batch; full text in each brief): (1)
exclusive file ownership — helpers live `private` in owned files; lemmas
belonging in shared files are *requested* via the PR description and added
serially at epoch merge, flagged for audit; (2) statement freeze — audited
declarations are never renamed, re-signatured, or re-stated by a fill PR; a
target that looks unprovable as stated is an *escalation*, reported in the PR
with the obstruction, never "fixed" inline; (3) verification per batch via the
check script, zero `error:` lines, sorry warnings only at documented
out-of-scope items; (4) at epoch merge the maintainer re-runs the full sweep,
produces the comment-stripped drift attestation, and prepares the epoch's
fill-round audit pack with elaboration evidence.

**Blueprint reference ingestion:** ingest Chapter 1 as
`blueprint/src/references/arora-barak-ch01-*.md` (raw/clean pair, ch. 13 shows the format)
so `\statementsource`/`\proofsource` citations are possible once proofmatch runs are
approved.

## 6. Risks and honest effort assessment

- **The proof-sketch gap is the main cost.** The book proves Claims 1.5/1.6 and Thm 1.9 in
  a paragraph each; formally these are the expensive items. The AFP `Cook_Levin` entry
  spent most of its effort exactly here. `Composition.lean` is the hidden load-bearing
  file — budget for it.
- **Vendoring means drift** against a fast-moving upstream. Mitigation: minimal local
  modification, source commit recorded per file, periodic upstream diffs.
- **Definitions before theorems pays off:** phases 1–2 already give TCSlib a citable,
  blueprint-documented model of computation with P and oracles, onto which the existing
  `Complexity/NPReductions/` files can eventually be retargeted — even if phases 3–5 fill
  slowly.

## 7. Decision log

| Decision | Status |
|---|---|
| Vendor cslib `MultiTapeTM`; reuse mathlib only for `Language`/`FinEncoding`/bridge | Decided |
| Finiteness deferred in raw layer, enforced via bundled `FinTM` for all headline defs | Decided |
| Oracle wrapper lands in phase 1 (ahead of book order) | Decided |
| Work on branch `complexity/arora-barak-ch1`; verify via `scripts/lean_check.sh` (CI runs on main only) | Decided |
| Namespaces: `Turing` (vendored core) / `Complexity` (classes) | Working assumption; revisit on clash |
| NP/NTM signatures deferred to Chapter 2 work | Decided |
| §1.7 `O(T log T)` and oblivious-TM proofs are stretch goals | Decided |
| Blueprint: late-bound — generated from compiled Lean at phase boundaries only, nothing hand-written ahead of the Lean | Decided |
| External audits between phases: cross-vendor LLM with prepared packs (`audits/`), findings gate the next phase | Decided |
| Vendored cslib source commit: `a374775894efb9b7196cccf11235c60a97086dc1` (2026-09-14); relational semantics (`RelatesInSteps`) dropped in the port | Decided |
| Phase-1 audit round 1 (`audits/phase1-findings.md`): all 8 sorries confirmed true; 3 majors fixed — `TimeConstructible` repaired to `∃ c > 0, … c·(T n + 1)` (the literal exact bound refutes AB's own `id` example in this model), `OracleTM.WellFormed` added, oracle-tape constant-overhead claim corrected to polynomial; minors swept; audit-requested sanity statements added. Oracle citation is [AB09, Definition 3.4] (not 3.6) | Decided |
| Phase 1 requires a clean re-audit of the fixes before phase 2 starts | Decided |
| Phase-1 audit round 2 (`audits/phase1-reaudit-findings.md`): zero blockers/majors — all round-1 resolutions verified, all 8 new sorries confirmed true (with a worked `timeConstructible_id` witness machine reusable in the fill phase); 5 prose minors swept, blankness-certificate lemma added per note 6. **Phase-1 audit gate closed**; see `audits/phase1-resolutions.md` | Decided |
| Phase-2 renderings: Claim 1.6 rendered as **one work tape** (the merged input/work/output single-tape model is a genuinely different structure — it has an `Ω(n²)` palindrome lower bound our model beats — and is out of scope, with no identification claimed); Claim 1.8 rendered as **`NonnegativeHeads`** (our tapes are already bidirectional, so the meaningful direction is unidirectional use); obliviousness constrains input/work-head trajectories only — it does **not** force length-determined halting (phase-2 audit finding 1 refuted that with a stationary-head counterexample) and leaves emission schedules unconstrained; the `TimeConstructible` hypothesis in Exercise 1.5 is needed by the padding construction, not by the definition | Decided — audited (phase-2 round 1) |
| Output-tape/initialization convention obligations (phase-1 finding 4): **waived**, per phase-2 audit finding 3 — no formal bridge is possible without formalizing [AB09]'s read-write-output model, which this development does not do; the compensating restriction is that no exact-step-count transfer from [AB09] is ever claimed (all bounds carry existential constants, all results are self-contained in-model). The buffer-and-flush technique is documented in `Composition.lean`; a formal bridge is added only if a downstream result needs it | Decided — waiver accepted by phase-2 audit as a labeled option |
| Persistent-vs-erased query-tape polynomial-overhead statement moved from phase 2 to the Chapter 3 oracle-class work, where polynomial overhead is meaningful (class level); the impossibility of constant overhead stays documented in `Oracle.lean`. Outstanding obligation before importing any oracle-class invariance | Decided — deferral accepted by phase-2 audit (finding 13) |
| Phase-2 audit round 1 (`audits/phase2-findings.md`): 4 majors, 6 minors, 3 notes — **no theorem formula refuted**; all 11 new sorries assessed true as stated. Majors were prose/sketch-level: the false frozen-heads implication removed, the oblivious-simulation sketch replaced by the audit's corrected construction, the convention-discharge overclaim converted to the waiver above, ModelInvariance's invariance claims stated at delivered strength (alphabet: DTIME up to constants; tape count: P only). Sketch repairs: all-blank block for logical blank (1.5), tagged `Option Γ` payloads and `k = 0` case (1.6), piecewise fold coordinate with origin tags and safe-halt on non-embedded symbols (1.8) | Decided |
| Phase-3 audit round 2 (`audits/phase3-reaudit-findings.md`): zero blockers/majors — both round-1 counterexamples formally excluded (`serialize` proved injective and prefix-free from its parse grammar; the canonizer contract shown to decide the undecidable set for Argument A's scheme, so it cannot instantiate `EffectiveMachineCode`; code-first startup arithmetic verified with no input-length term). The α-dependent evaluator constant confirmed **necessary** (Argument E) — never to be described as [AB09]'s machine-dependent constant. Two minors swept (left-boundary marker in the evaluator sketch; `Nat.bits` order wording). Argument F provides complete phase-4 proof blueprints and identifies the guarded-composition API obligation. **Phase-3 audit gate closed**; see `audits/phase3-resolutions.md` | Decided |
| Phase-3 audit round 1 (`audits/phase3-findings.md`): **two blockers on the phase-3 statements, both accepted** — (1) the algebraic `MachineCode` admits noncomputable-meaning schemes against which no universal machine exists (Argument A), repaired by `EffectiveMachineCode`: an in-model canonizer into the new **fixed scheme-independent** `CodeTM.serialize` (canonizing into the scheme's own encode provably does not exclude the pathology); (2) the input-first `pairEncode x α` layout falsifies all three time bounds (Argument B), repaired by the **code-first** layout `pairEncode α x`. Majors: `universal` restated as the all-string evaluator `U(x, α) = M_α(x)` with a divergence-preservation converse and α-dependent constants; `universal_quadratic` labeled as the total-function corollary; `serialize` records the initial state (finding 5's collision). Minors: deadline-inclusive timeout convention documented; pack namespace erratum (`Complexity.succ_pow_le`). Fill round and supporting lemmas: audited clean (findings 9-13). Re-audit pending | Decided |
| Fill round 1 (commit `f8621285`): 20 of 28 phase-1/2 sorries proved — all semantics/arithmetic/chaining obligations, both oracle lockstep theorems, `mem_P_iff`, and `computesFunInTime_id` with an explicit machine. The 8 remaining sorries are exactly the heavy machine constructions (`const`, `comp`, the four robustness simulations, `timeConstructible_id`, `PAL_mem_DTIME_linear`), each with an audited outline. Repository-side verification: no audited declaration signature changed or was removed. Phase-3 skeleton delivered (5 statement sorries): `CodeTM`, abstract `MachineCode` scheme, `pairEncode`, Theorem 1.9 (linear for coded machines / relaxed quadratic / timed). Audit round covering fills + phase-3 pending | Decided |
| Phase-2 audit round 2 (`audits/phase2-reaudit-findings.md`): zero blockers/majors — both corrected load-bearing sketches certified as adequate proof outlines; 4 prose minors swept (fold alphabet `Bool × Option Γ × Option Γ`, waiver-prose synchronization, `O((k+1)·L)` overhead, one-work-tape *binary* normal form in phase 3); Lean-code identity between the audited commits verified repository-side by comment-stripped git comparison. **Phase-2 audit gate closed**; see `audits/phase2-resolutions.md` | Decided |
| Phase-4 skeleton landed (after the closed phase-3 loop, gate commit `b61e876d`): `Uncomputability/{Computable,Diagonalization,Halting}.lean` + facade — `Complexity.Computable`, `UC` (over an **arbitrary** `MachineCode`: the diagonalization never computes `encode`/`decode`, per round-2 Argument F; effectivity appears only in Theorem 1.11), `HALT` (totalized `false` off the `pairEncode` image; pair format = the evaluator's code-first layout), `UC_not_computable`, the reduction `UC_computable_of_HALT_computable` (uses only the *forward* clause of `universal`), `HALT_not_computable` (proved from the two). The audit-mandated guarded API landed in `Composition.lean` (`exists_comp_partial` — partial sequential composition with buffered intermediate output; `exists_cond` — branch on a decided predicate; `computesFunInTime_ifEq`), plus `computesFunInTime_pairEncode_diag` in `Encoding.lean` and `FinTM.Computes`/`ComputesInTime.output_unique`/`ComputesFunInTime.computes` in `Finite.lean` (additions to audited files, flagged for the phase-4 audit). 7 new sorries (21 total), every phase-4 proof sketch names only stated results. Phase-4 audit pack pending | Decided |
| Phase-4 audit round 1 (`audits/phase4-findings.md`, audited at `49d25a27`): **zero blockers, zero majors — the first single-round gate**. All 18 new declarations blind-restated in agreement; both headline arguments (UC diagonalization over an arbitrary `MachineCode`; `HALT → UC` reduction using only the forward evaluator clause) independently re-derived end-to-end from stated interfaces — no missing machine-construction API. One minor swept (the diagonal-pairing sketch's step count corrected to the auditor's `4n + 5 ≤ 6(n+1)` schedule; statement unchanged); note-level sketch refinements (unconditional first rewind move + empty-buffer boundary tag in `exists_comp_partial`; `HALT` off-image convention warning for downstream clients). **Phase-4 audit gate closed** — Chapter 1's critical path is fully specified and audited; see `audits/phase4-resolutions.md`. Remaining critical-path work: the 21-sorry fill campaign | Decided |
| Phase 5 (§1.7 `O(T log T)`, oblivious proofs, RAM-TM, mathlib bridge) **deferred to a much later effort** — not scheduled in the current push; revisit only after the phase-1-4 fill campaign completes | Decided |
| Fill campaign schedule (2026-09-16, §5 "Fill campaign"): 4 epochs of parallel disjoint-ownership batches (E1 ≈ 41 pts: assemblies + small machines + encoding list layer + classic machines; E2 ≈ 42: guarded-composition core + `one_work_tape` + remaining simulations; E3 ≈ 40: canonizer + `universal` + oblivious (droppable); E4 ≈ 10: `timed_universal` + closure), audit rounds at epoch boundaries. Cloud agents work from `briefs/epoch1-batch{A,B,C,D}.md`, branch off `complexity/arora-barak-ch1`, PR back into it; verification via `scripts/lean_check_tree.sh` + `scripts/ab_ch1_module_order.txt` | Decided |
| Fate of this file at merge (graduate to `docs/` vs. superseded by blueprint) | Open — decide at merge time |

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
6. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.

## ===== audits/phase4-resolutions.md =====

# Phase 4 — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Audit protocol". External auditor:
cross-vendor LLM per decision log.

## Round 1 (`phase4-pack.md` → `phase4-findings.md`, audited at `49d25a27`)

**Zero blockers, zero majors — the first phase to clear its audit loop in a single
round.** All 18 new declarations were blind-restated in agreement with their
statements; both headline assembly arguments — the `UC` diagonalization over an
arbitrary `MachineCode` and the `HALT → UC` reduction — were independently
re-derived end-to-end from the stated interfaces, confirming the skeleton's design
goal that the fill is assembly, not new mathematics ("no missing
machine-construction interface"). The repository attestations were corroborated
source-side (sole-parent commit relation, matching blob hashes for all six touched
modules, insertion-only comment-stripped diffs, unchanged carried sorries, and the
`14 + 7 = 21` sorry count). One minor and seven notes, resolved in the closing
commit:

| Finding | Resolution |
|---|---|
| 1 minor — the diagonal-pairing sketch's `3n + 6` step count undercounts the doubled first pass (one emitted symbol per transition forces `2n` steps); the described schedule takes `4n + 5` | Sketch corrected to the auditor's explicit schedule (`2n + 2 + (n+2) + n + 1 = 4n + 5 ≤ 6(n+1)`); the theorem's existential linear bound is unchanged |
| 2 note — the arbitrary-`MachineCode` generality of Theorem 1.10 survives the noncomputable-meaning attack; no runtime encode/decode occurs | No change; no effectivity hypothesis is to be added. The auditor's full derivation is on file for the fill |
| 3 note — `exists_comp_partial`'s iff is the right contract; the construction must make the buffer rewind's first left move unconditional (the head rests on the blank right of the written word) and initialize the boundary tag for an empty buffer | Both details added to the sketch |
| 4 note — `exists_cond`'s register/rewind construction verified (head calculation `j ↦ max(j−1,0) ↦ 0 ↦ 1` from every valid position; append-only singleton output forces exactly one emission, so early emission is harmless) | No change |
| 5 note — the bare `∃ T` of `Computes.exists_computesFunInTime` suffices (`one_work_tape_binary` imposes no regularity on the bound; empty alphabets vacuous) | No change |
| 6 note — `HALT`'s off-image totalization is correct and immaterial to Theorem 1.11, but convention-dependent elsewhere (`HALT c [] = false`) | Docstring now warns downstream clients: keep the convention or prove inputs are genuine pairs. **Carried obligation** |
| 7 note — the reduction assembles entirely from stated declarations; the forward universal clause suffices, no timed partial composition and no globally named evaluator needed | No change; the auditor's assembly derivation is on file for the fill |
| 8 note — the zero-error elaboration attestation was not independently reproduced (no Lean in the audit environment); source-history checks corroborate the additive-change and sorry-count attestations only | Standing practice: repository-side verification continues; fill rounds must ship elaboration evidence from the pinned toolchain, and neither this audit nor a sorry-accepting elaboration is completed correctness |

## Gate status

**CLOSED.** With phases 1-4 all gated, **Chapter 1's critical path is fully
specified and audited**: every headline definition and theorem of [AB09, §§1.2-1.6]
is stated, with 21 audited-true sorries. Carried obligations, tracked in the plan:

- **Fill campaign** (the remaining critical-path work): 21 sorries, each with an
  audited sketch. Beyond the earlier construction manuals, the phase-4 findings add
  the explicit diagonal-pairing schedule (`4n + 5`), the completed-output ↔
  halted-state equivalence proof (with its space witness), the rewind head
  calculations, and complete assembly derivations of both phase-4 theorems.
- Downstream uses of `HALT` on arbitrary (non-pair) strings must keep the off-image
  `false` convention or prove their inputs are genuine pairs (finding 6).
- Fill rounds ship build/elaboration evidence from the pinned toolchain
  (finding 8).
- Phase 5 remains deferred to a much later effort (plan §5); no pack will be
  prepared for it in the current push.

## ===== briefs/epoch1-batchA.md =====

# Fill campaign — Epoch 1, Batch A: the assembly proofs

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. The statement
layer is complete and has passed four external audit gates (see `audits/`); what
remains is filling audited-true `sorry`s. This batch is the **integration test of
the whole interface stack**: four proofs that are pure *assembly* — they chain
already-stated results and construct no machines. Filling them machine-checks that
the phase-3/4 interfaces genuinely compose, which is the single highest
risk-retirement step of the campaign. Your proofs may (and must) cite theorems
that are themselves still `sorry`d — that is by design; citing a `sorry`d theorem
produces no new warning on your declaration.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Create a working branch `fill/epoch1-A` off `complexity/arora-barak-ch1`; when
  done, open a PR **into `complexity/arora-barak-ch1`**.
- Read first: `policy.md` (repo standards), `AroraBarakChapter1Plan.md` §5
  (phasing, audit protocol, fill-campaign ground rules), and
  `audits/phase4-findings.md` (your two hardest targets follow its derivations
  line by line).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/Uncomputability/Computable.lean`
- `TCSlib/Complexity/Uncomputability/Diagonalization.lean`
- `TCSlib/Complexity/Uncomputability/Halting.lean`
- `TCSlib/Complexity/TuringMachine/Universal.lean` — **only** the proof of
  `universal_quadratic`; the `universal` and `timed_universal` sorries stay.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned by the
  manifest. One-time setup from the repo root: `lake exe cache get` (first run
  installs the toolchain and downloads the mathlib build cache; several GB).
- **Never run `lake build`** — banned on this branch (plan decision log). The
  repo's `.claude/CLAUDE.md` tells agents to rely on the VS Code LeanInfoView and
  run no build commands; that rule presumes a local interactive session. For this
  cloud task the maintainer-designated verification path (recorded in the plan
  decision log) is the direct-`lean` check script:
  - Bootstrap once on a fresh clone (fills the scratch olean tree, dependency
    order):
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  - Iterate: `bash scripts/lean_check_tree.sh <module>` after each edit (module
    path without `.lean`). When you edit a file, re-check it and every *later*
    module in the order list before relying on the result.
  - Final sweep before the PR: the full bootstrap loop again; **zero `error:`
    lines**; `declaration uses 'sorry'` warnings only at the out-of-scope
    declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only the owned files. Helper lemmas go in your
   owned files, `private` unless there is a documented reason to export; list
   every new declaration (public and private) in the PR description — the next
   audit round blind-restates them. If a helper belongs in a shared file
   (`Finite.lean`, say): do **not** edit that file — add a `private` copy in your
   own file and record the request under "Requested shared lemmas" in the PR.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration — this is
   externally audited surface. You may append to a docstring's proof-sketch
   paragraph if your delivered proof deviates from the sketch; flag such updates
   in the PR.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction (approach,
   failing goal, candidate counterexample) under "Escalations" in the PR, and
   continue with your other targets. Statement changes go through the audit
   process, never through fill PRs.
4. Do not remove, weaken, or fill any sorry outside your target list — including
   in your own files.
5. Every remaining `sorry` keeps its docstring sketch (policy.md §3); filled
   proofs keep their docstrings.
6. Precise imports: add exactly what you use; never bare `import Mathlib`; keep
   the existing `set_option` headers.

## Targets

### 1. `Turing.FinTM.Computes.exists_computesFunInTime` (Computable.lean)

A machine computing `f` with no stated bound admits some time bound. Plan (per
the docstring sketch): `choose t ht using h` to name a halting time per input;
for each `n`, the inputs of length `n` form a finite type — transport `Fintype`
from `Fin n → Symbol` (via `List.Vector Symbol n` and its equivalence, or any
route you prefer, e.g. `Fintype.ofEquiv` on the subtype
`{x : List Symbol // x.length = n}`); set `T n` to the `Finset.univ.sup` of the
chosen times; conclude with `ComputesInTime.mono` (`Finite.lean`). No
monotonicity or positivity of `T` is claimed. Mind the degenerate cases the audit
checked: empty `Symbol` (positive lengths have no inputs — `sup` of an empty set
is `0`, harmless) and `n = 0` (the empty input still has its chosen time).

### 2. `Complexity.UC_not_computable` (Diagonalization.lean)

[AB09, Theorem 1.10] for an arbitrary `MachineCode`. Follow the docstring sketch
and, in more detail, `audits/phase4-findings.md`, section "The diagonalization
assembles without an effectivity assumption". Chain:
`Computes.exists_computesFunInTime` → `Turing.FinTM.one_work_tape_binary`
(in `Robustness/SingleTape.lean` — add the precise import
`TCSlib.Complexity.TuringMachine.Robustness.SingleTape` to Diagonalization.lean)
→ `Turing.exists_codeTM` → set `α₀ := c.encode N`, rewrite with
`Turing.MachineCode.decode_encode` → case on `UC c α₀` using
`Complexity.UC_eq_false_iff` and
`Turing.FinTM.ComputesInTime.output_unique`; both cases end in `[false] = [true]`
or a Bool contradiction (`simp` closes singleton-list injectivity).

### 3. `Turing.universal_quadratic` (Universal.lean)

The total-function corollary of Theorem 1.9. Plan (docstring sketch): obtain
`⟨U, hU⟩ := universal c`; given `M₀` computing `f` within `T`, apply
`one_work_tape_binary`, then `exists_codeTM`, take `α := c.encode` of the coded
machine, rewrite with `MachineCode.decode_encode`, and use the **forward clause**
of `hU α`. The constant arithmetic
`C_U * (c₁ * (T n + 1)^2 + 1) ≤ C_U * (c₁ + 1) * (T n + 1)^2` has a direct
in-repo template: the `calc` block closing `one_work_tape_binary` in
`Robustness/SingleTape.lean` (uses `Nat.pow_pos`, `Nat.mul_le_mul`, `ring`).
Finish with `ComputesInTime.mono`.

### 4. `Complexity.UC_computable_of_HALT_computable` (Halting.lean)

The [AB09, Theorem 1.11] reduction. Follow `audits/phase4-findings.md`, section
"The HALT reduction also assembles entirely through the stated interfaces" — it
is a line-by-line script. Ingredients (all stated): `universal c` (forward clause
only), `Turing.computesFunInTime_pairEncode_diag` (Encoding.lean),
`Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]` and
`computesFunInTime_const [true]` (Composition.lean), `exists_comp_partial`
(three uses), `exists_cond`, `ComputesFunInTime.computes`,
`ComputesInTime.output_unique`, `HALT_pairEncode_eq_true_iff`, and the `UC`
unfolding lemmas. Suggested skeleton: first prove a small private lemma "a total
machine's halting relation is equality with its prescribed output"
(`hM : M.Computes g → ((∃ t, M.ComputesInTime x w t) ↔ w = g x)`, via
`output_unique`), which collapses each `exists_comp_partial` application; then
the two-case correctness argument over `p α`.

## Out-of-scope sorries you will see (leave every one untouched)

In your owned files: `universal`, `timed_universal` (Universal.lean). Everywhere
else: `computesFunInTime_const`, `computesFunInTime_ifEq`,
`computesFunInTime_comp`, `exists_comp_partial`, `exists_cond`
(Composition.lean); `pairEncode_injective`, `computesFunInTime_pairEncode_diag`,
`exists_effectiveMachineCode`, `exists_codeTM` (Encoding.lean);
`alphabet_reduction`, `one_work_tape`, `nonnegative_heads`,
`oblivious_of_mem_DTIME` (Robustness/); `timeConstructible_id`
(TimeConstructible.lean); `PAL_mem_DTIME_linear` (Examples.lean). After your
batch, exactly these 17 sorry warnings remain in the sweep.

## PR checklist (all of it in the PR description)

- [ ] Targets filled (4), one line each on how the proof went vs the sketch.
- [ ] New declarations added (public and private), for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Verification evidence: the final full-sweep log tail (per-module lines and
      warnings) and confirmation of zero `error:` lines.
- [ ] Diff touches only the owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (the pin has no `Function.update_noteq`).
- Use core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: use `split <;> simp <;> omega` or
  explicit cases.
- After `cases hs : cfg.state`, goals can keep `match some q with …` unreduced —
  insert `dsimp only` before rewriting, or restructure with nested `split`.
- Avoid bare `simp` when hypotheses use folded forms (`initCfg` is `@[simp]` and
  full `simp` desynchronizes goal from hypotheses); prefer targeted `simp only`.
- `ring` needs `import Mathlib.Tactic.Ring`.
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` or un-beta-reduced `(fun n => …) n`:
  normalize with `show` / `simp only` / `le_of_eq` first.
- `Nat.find` under classical: `classical` tactic plus explicit `(p := fun n : ℕ => …)`.
- `⋃`-membership via `Set.mem_iUnion`; `Language` has `Zero`
  (`(0 : Language _)`, `Language.notMem_zero`), not `∅`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩` (see `ComputesInTime.mono` / `output_unique` in
  `Finite.lean` for the pattern).

## ===== briefs/epoch1-batchB.md =====

# Fill campaign — Epoch 1, Batch B: small machines and the branch combinator

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. The statement
layer is complete and has passed four external audit gates (see `audits/`); what
remains is filling audited-true `sorry`s. This batch builds **explicit machines
with machine-checked run invariants** in `Composition.lean`: two small emission
machines, then the branch combinator `exists_cond` — the first control-flow
construction in the development. The worked in-repo pattern for all three is the
already-proved `idTM` / `idTM_run` / `computesFunInTime_id` at the top of your
file: a `private` machine, a run invariant by induction on the step count, one
final halting step, `ComputesInTime.mono` to reach the stated bound. Design your
helper gadgets (especially the input-head rewind and the "fresh-tape lockstep"
lemmas) for reuse: epoch 2 fills `exists_comp_partial` in this same file and will
want them.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Create a working branch `fill/epoch1-B` off `complexity/arora-barak-ch1`; when
  done, open a PR **into `complexity/arora-barak-ch1`**.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5 (fill-campaign ground
  rules), and `audits/phase4-findings.md` findings 3–4 plus the surrounding
  prose (the auditor verified your constructions' key gadgets: the rewind head
  calculation and the one-emission register argument).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Composition.lean`

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned. Setup
  once from the repo root: `lake exe cache get` (several GB on first run).
- **Never run `lake build`** — banned on this branch (plan decision log). The
  repo's `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; for this cloud task the maintainer-designated verification path is
  the direct-`lean` check script:
  - Bootstrap once on a fresh clone:
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  - Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Composition`
    after each edit; re-check later modules in the order list before the PR.
  - Final sweep: the full loop; **zero `error:` lines**; `sorry` warnings only
    at the out-of-scope declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only `Composition.lean`. Helpers are `private`
   unless there is a documented reason to export; list every new declaration
   (public and private) in the PR — the next audit round blind-restates them.
   If a helper belongs in a shared file (`Finite.lean`, `Configuration.lean` —
   the latter is **vendored, never touch it**): add a `private` copy in your file
   and record the request under "Requested shared lemmas" in the PR.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration. You may
   append to a docstring's proof-sketch paragraph if the delivered proof
   deviates; flag such updates in the PR.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction under
   "Escalations" in the PR, and continue with your other targets.
4. Do not remove, weaken, or fill any sorry outside your target list — in your
   file that means `computesFunInTime_comp` and `exists_comp_partial` stay.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep their
   docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets (recommended order)

### 1. `Turing.FinTM.computesFunInTime_const`

A machine computing `fun _ => w` within `c * (n + 1)`. Simplest possible
machine: `k := 0`, `State := Fin (w.length + 1)`, transition ignoring both reads
(`fun q _ _ => …`): state `i < w.length` emits `w[i]`, keeps the input head
stationary (`SignType.zero`), steps to `i + 1`; state `w.length` takes one
halting step (`state := none`, no emission). Run invariant (induction on
`t ≤ w.length`): state is `some t`, output is `w.take t`; the input head never
moves, so no position tracking is needed — strictly easier than `idTM_run`.
Total: `w.length + 1` steps; `c := w.length + 1` works since
`c * (n + 1) ≥ c`.

### 2. `Turing.FinTM.computesFunInTime_ifEq`

The fixed-string comparator: `fun w => if w = w₀ then u else v` in linear
(actually constant) time. Note the audited disposition
(`audits/phase4-findings.md`, first table row): compare at most the first
`w₀.length + 1` positions, treating an early blank or an extra symbol as a
mismatch, then emit the selected word. Suggested state type (Fintype by
`inferInstance`): `Fin (w₀.length + 1) ⊕ Fin (u.length + 1) ⊕ Fin (v.length + 1)`
— match-progress states, then two emission chains ending in a halting step; the
transition hardcodes `w₀`, `u`, `v` by indexing. Case analysis in the invariant:
matched-so-far / mismatch-seen; the audited edge cases are `w₀ = u = v = []`
(constant machine, halts after its boundary read; no time-zero halting is
claimed) and inputs shorter/longer than `w₀`. Every run halts within
`w₀.length + max u.length v.length + 3` steps, absorbed by `c * (n + 1)`.

### 3. `Turing.FinTM.exists_cond`

The branch combinator — the substantial item. The statement is **untimed**
(halting relations only), which spares you all step accounting. Architecture,
per the audited docstring sketch:

- **State**: three phases, e.g.
  `(D.State × Option Bool) ⊕ RewindState ⊕ (M₁.State ⊕ M₂.State)` with a small
  `RewindState` carrying the register bit (`Bool × Fin 2`-style). All Fintype by
  `inferInstance`.
- **Tapes**: `D.k + M₁.k + M₂.k` fresh, disjoint tapes (no reuse — simplest).
  Define private tape-embedding helpers (`Fin.castAdd`/`Fin.natAdd`) once and
  use them consistently; expect this to be the fiddliest part.
- **Phase 1**: lockstep simulation of `D` on the true input, with `D`'s single
  emission captured in the register instead of emitted. Justification that the
  register never overflows: `hD` says the completed output is the singleton
  `[p x]`, and output is append-only
  (`Turing.MultiTapeTM.output_length_le` / `output_prefix` in `Finite.lean`),
  so `D` emits exactly one symbol over the whole run — the auditor verified
  this inference (finding 4), including *early* emission long before halting.
- **Phase 2 (rewind)**: on `D`'s halting transition, return the input head to
  its initial position (which is `1` — see `idTM_run`'s base case): one
  unconditional left step, then left while `inputSymbol` is `some _`, then one
  right step. The audited head calculation is
  `j ↦ max (j−1) 0 ↦ 0 ↦ 1` from every valid position `j ∈ [0, n+1]`,
  including the empty input (the clamp at position `0` — see
  `Turing.moveInputPos` in the vendored `Configuration.lean` — makes it safe).
  If the register is (unreachably) still empty at dispatch, have the machine
  halt — totality of the machine must not depend on `hD`; the correctness proof
  discharges reachability.
- **Phase 3 (dispatch)**: transfer to a disjoint copy of `M₁` or `M₂` per the
  register, running on the true input with its own fresh tapes and the untouched
  output tape. The key lemma is a lockstep correspondence: from (input position
  `1`, blank branch tapes, empty output, embedded branch start state), the
  composite's run mirrors the branch machine's initialized run step for step.
  The in-repo precedent for exactly this "embedded machine in lockstep" proof
  shape is the `Cfg.embedOracle_*` lemma suite in `Oracle.lean` — read it before
  designing your invariant.
- **The iff**: forward — any completed composite run decomposes into the three
  phases (phase 1 completes because `hD` gives `D` a halting time; use
  determinism, `Turing.FinTM.ComputesInTime.output_unique`, to identify the
  register with `p x`); backward — from a halting run of the selected branch,
  assemble the composite witness (D-time + rewind steps + branch time).

## Out-of-scope sorries you will see (leave every one untouched)

In your file: `computesFunInTime_comp`, `exists_comp_partial`. Elsewhere:
`universal`, `universal_quadratic`, `timed_universal` (Universal.lean);
`pairEncode_injective`, `computesFunInTime_pairEncode_diag`,
`exists_effectiveMachineCode`, `exists_codeTM` (Encoding.lean);
`alphabet_reduction`, `one_work_tape`, `nonnegative_heads`,
`oblivious_of_mem_DTIME` (Robustness/); `timeConstructible_id`
(TimeConstructible.lean); `PAL_mem_DTIME_linear` (Examples.lean);
`Computes.exists_computesFunInTime` (Computable.lean); `UC_not_computable`
(Diagonalization.lean); `UC_computable_of_HALT_computable` (Halting.lean).

## PR checklist (all of it in the PR description)

- [ ] Targets filled (3), one line each on how the proof went vs the sketch.
- [ ] New declarations (public and private) listed, for audit restatement;
      call out gadgets designed for epoch-2 reuse (rewind, tape embeddings,
      lockstep lemmas).
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Verification evidence: final full-sweep log tail; zero `error:` lines.
- [ ] Diff touches only `Composition.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin).
- Core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: `split <;> simp <;> omega`.
- After `cases hs : cfg.state`, insert `dsimp only` to iota-reduce
  `match some q with …` before rewriting, or use nested `split`.
- Avoid bare `simp` when hypotheses use folded forms (`initCfg` is `@[simp]`);
  prefer targeted `simp only`.
- `ring` needs `import Mathlib.Tactic.Ring` (check the file's imports before
  using it; add precisely what you use).
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` or un-beta-reduced lambdas:
  normalize with `show` / `simp only` first (see `idTM_run`'s
  `show ((… ).inputPos : ℕ) + 1 = t + 2` trick).
- SignType lemma names at the pin: `SignType.coe_one`, `SignType.neg_eq_neg_one`,
  `SignType.coe_neg_one`, `SignType.pos_eq_one`.
- Vendored API you will lean on: `MultiTapeTM.runFrom_succ_eq_step'`,
  `MultiTapeTM.step`, `Action.apply`, `Cfg.inputSymbol` (a double `dite` —
  destructure with `dif_neg`/`dif_pos` as in `computesFunInTime_id`),
  `moveInputPos_pos_of_ne_right`, `inputSymbolInner`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩`.

## ===== briefs/epoch1-batchC.md =====

# Fill campaign — Epoch 1, Batch C: the encoding list layer

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. The statement
layer is complete and has passed four external audit gates (see `audits/`); what
remains is filling audited-true `sorry`s. This batch owns `Encoding.lean` and
fills its three tractable obligations: the pairing injectivity (a pure list
lemma), the diagonal-pairing machine (a three-phase concrete machine), and the
state-relabeling theorem (a configuration-bijection simulation). The big
`exists_effectiveMachineCode` stays sorry — it is a later epoch.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Create a working branch `fill/epoch1-C` off `complexity/arora-barak-ch1`; when
  done, open a PR **into `complexity/arora-barak-ch1`**.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5 (fill-campaign ground
  rules), `audits/phase3-reaudit-findings.md` (Argument A's parse-grammar
  analysis — your injectivity proof formalizes its first step) and
  `audits/phase4-findings.md` finding 1 (the corrected `4n + 5` schedule for the
  diagonal-pairing machine).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Encoding.lean`

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned. Setup
  once from the repo root: `lake exe cache get` (several GB on first run).
- **Never run `lake build`** — banned on this branch (plan decision log). The
  repo's `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; for this cloud task the maintainer-designated verification path is
  the direct-`lean` check script:
  - Bootstrap once on a fresh clone:
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  - Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Encoding`
    after each edit; re-check the later modules in the order list before the PR
    (Universal, the Uncomputability files, and the facades import you).
  - Final sweep: the full loop; **zero `error:` lines**; `sorry` warnings only
    at the out-of-scope declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only `Encoding.lean`. Helpers are `private` unless
   there is a documented reason to export (a parser definition may deserve
   export if `exists_effectiveMachineCode`'s later fill will reuse it — if you
   export, say so in the PR); list every new declaration (public and private)
   in the PR — the next audit round blind-restates them. **The vendored files
   (`Configuration.lean`, `Deterministic.lean`) are frozen — never edit them.**
   If a helper belongs in another shared file, add a `private` copy in your file
   and record the request under "Requested shared lemmas" in the PR.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration. You may
   append to a docstring's proof-sketch paragraph if the delivered proof
   deviates; flag such updates in the PR.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction under
   "Escalations" in the PR, and continue with your other targets.
4. Do not remove, weaken, or fill any sorry outside your target list — in your
   file that means `exists_effectiveMachineCode` stays.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep their
   docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets (recommended order)

### 1. `Turing.pairEncode_injective`

Pure list lemma, no machines. Recommended route (the docstring's aligned-pair
parser, which the phase-3 audit certified): define a `private` parser
`pairDecode : List Bool → Option (List Bool × List Bool)` by two-at-a-time
structural recursion — `false :: true :: rest ↦ some ([], rest)` (separator),
`b :: b' :: rest` with `b = b'` ↦ prepend `b` to the first component of
`pairDecode rest`, anything else ↦ `none` — then prove
`pairDecode (pairEncode x α) = some (x, α)` by induction on `x` (the doubled
blocks are `00`/`11`, never the aligned `01` separator), and derive injectivity
from the left inverse (`Function.LeftInverse.injective` or a two-line direct
argument on the `Prod`). Watch the `x = []` base case
(`pairEncode [] α = [false, true] ++ α`) and note `pairEncode`'s definition
uses `List.flatMap` — `simp [pairEncode, List.flatMap_cons]`-style unfolding.

### 2. `Turing.computesFunInTime_pairEncode_diag`

The diagonal pairing `α ↦ pairEncode α α` in linear time. The docstring sketch
carries the audited schedule (`audits/phase4-findings.md`, finding 1): pass one
costs **two steps per input bit** (emit the bit staying put, emit it again
moving right), then two stationary separator emissions, then the rewind (one
unconditional left step, left while reading `some _`, one right step — total
`n + 2`), then the verbatim pass (`n`), then one halting step: `4n + 5 ≤
6 * (n + 1)`. Machine outline: `k := 0`; states for
{pass1-emit-stay, pass1-emit-move, sep1, sep2, rewind, pass2} (a small inductive
or a sum of `Fin`s — either way `Fintype`/`DecidableEq` derivable or by
`inferInstance`). The proof pattern is `Composition.lean`'s `idTM` /
`idTM_run` / `computesFunInTime_id`: per-phase run invariants by induction on
steps, chained at phase boundaries, then `ComputesInTime.mono`. The rewind
invariant must track the input head moving *left* — `idTM_run` only walks
right, so you will prove the mirror-image position lemma with the
`Turing.moveInputPos` clamp at `0` (the head-position calculation
`j ↦ max (j−1) 0 ↦ 0 ↦ 1`, verified by the phase-4 auditor, covers every
starting position including the empty input).

### 3. `Turing.exists_codeTM`

Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine — a simulation by *bijection*, no new behavior. Plan:

- `M.State` carries `Fintype`/`DecidableEq` (bundled in `FinTM`) and is
  inhabited (`M.tm.q₀`), so `Fintype.card M.State = numStates + 1` for
  `numStates := Fintype.card M.State - 1` (positivity from
  `Fintype.card_pos_iff` + `Nonempty`; close the arithmetic with `omega`).
  `e := Fintype.equivFin M.State` composed with the card equality gives
  `e : M.State ≃ Fin (numStates + 1)` (`Equiv.cast` or `finCongr` on the card
  proof).
- **The sketch mentions `Turing.Action.mapState` — that helper does *not* exist
  in the vendored `Configuration.lean`, and the vendored files are frozen.**
  Define a `private` helper in `Encoding.lean` that maps an action's state
  field through `e` (record update: `{ a with state := a.state.map e }` — check
  `Action`'s exact field names in `Configuration.lean`), and build the coded
  transition `fun q inp ws => mapState e (M.tm.tr (e.symm q) inp ws')`.
- The tape-count cast: `hk : M.k = 1` means the work-tape read/write vectors
  must be transported between `Fin M.k` and `Fin 1`. Rather than `hk ▸`
  gymnastics, consider destructuring: reindex with `Fin.cast hk` explicitly in
  the transition definition and keep every cast in one helper so the
  commutation lemmas see a single normal form.
- Then a configuration bijection `Cfg … M.State ≃ Cfg … (Fin (numStates+1))`
  (mapping only the state component; tapes, heads, output unchanged) commuting
  with `step`, hence with `runFrom` by induction, hence the per-input
  `ComputesInTime` iff in both directions. The in-repo precedent for exactly
  this proof shape is the `Cfg.embedOracle_*` lemma suite in `Oracle.lean`
  (`embedOracle_apply`, `_init`, `_state_eq_none`, `_output`) — mirror its
  structure.

## Out-of-scope sorries you will see (leave every one untouched)

In your file: `exists_effectiveMachineCode`. Elsewhere: `universal`,
`universal_quadratic`, `timed_universal` (Universal.lean);
`computesFunInTime_const`, `computesFunInTime_ifEq`, `computesFunInTime_comp`,
`exists_comp_partial`, `exists_cond` (Composition.lean); `alphabet_reduction`,
`one_work_tape`, `nonnegative_heads`, `oblivious_of_mem_DTIME` (Robustness/);
`timeConstructible_id` (TimeConstructible.lean); `PAL_mem_DTIME_linear`
(Examples.lean); `Computes.exists_computesFunInTime` (Computable.lean);
`UC_not_computable` (Diagonalization.lean); `UC_computable_of_HALT_computable`
(Halting.lean).

## PR checklist (all of it in the PR description)

- [ ] Targets filled (3), one line each on how the proof went vs the sketch.
- [ ] New declarations (public and private) listed, for audit restatement —
      especially the parser and the state-mapping helper, with a note on
      whether the parser is exported for the future canonizer fill.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Verification evidence: final full-sweep log tail; zero `error:` lines.
- [ ] Diff touches only `Encoding.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin).
- Core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: `split <;> simp <;> omega`.
- After `cases hs : cfg.state`, insert `dsimp only` to iota-reduce
  `match some q with …` before rewriting, or use nested `split`.
- Avoid bare `simp` when hypotheses use folded forms (`initCfg` is `@[simp]`);
  prefer targeted `simp only`.
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` or un-beta-reduced lambdas:
  normalize with `show` / `simp only` first (see `idTM_run` in
  `Composition.lean`).
- SignType lemma names at the pin: `SignType.coe_one`, `SignType.neg_eq_neg_one`,
  `SignType.coe_neg_one`, `SignType.pos_eq_one`.
- Vendored API: `MultiTapeTM.runFrom_succ_eq_step'`, `MultiTapeTM.step`,
  `Action.apply`, `Cfg.inputSymbol` (double `dite`),
  `moveInputPos_pos_of_ne_right`, `inputSymbolInner`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩` (pattern in `Finite.lean`'s `mono`/`output_unique`).

## ===== briefs/epoch1-batchD.md =====

# Fill campaign — Epoch 1, Batch D: the classic machines

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. The statement
layer is complete and has passed four external audit gates (see `audits/`); what
remains is filling audited-true `sorry`s. This batch delivers the chapter's two
"textbook example" machines: the three-phase palindrome decider ([AB09,
Example 1.1]) and the binary-counter witness that the identity function is time
constructible — the latter's **amortized** step accounting is the real content.
Both have worked constructions in the phase-1 audit records; your job is to
formalize them. The worked in-repo proof pattern is `Composition.lean`'s `idTM`
/ `idTM_run` / `computesFunInTime_id`: a `private` machine, a run invariant by
induction on the step count, a final halting step, `ComputesInTime.mono`.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Create a working branch `fill/epoch1-D` off `complexity/arora-barak-ch1`; when
  done, open a PR **into `complexity/arora-barak-ch1`**.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5 (fill-campaign ground
  rules), and the phase-1 audit records: `audits/phase1-findings.md` (the
  per-sorry dispositions — the `PAL_mem_DTIME_linear` row spells out the
  boundary transitions and the `n = 0` trace) and
  `audits/phase1-reaudit-findings.md` (the explicit four-state counter witness
  — states named `count`/`carry`/`rewind`/`emit` — with its carry-length field
  calculation; the notation glossary at the end decodes the variables).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/ClassP/Examples.lean` (`PAL_mem_DTIME_linear`)
- `TCSlib/Complexity/ClassP/TimeConstructible.lean` (`timeConstructible_id`)

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned. Setup
  once from the repo root: `lake exe cache get` (several GB on first run).
- **Never run `lake build`** — banned on this branch (plan decision log). The
  repo's `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; for this cloud task the maintainer-designated verification path is
  the direct-`lean` check script:
  - Bootstrap once on a fresh clone:
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  - Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassP/Examples`
    (resp. `…/TimeConstructible`) after each edit; re-check the later modules
    in the order list before the PR.
  - Final sweep: the full loop; **zero `error:` lines**; `sorry` warnings only
    at the out-of-scope declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only the two owned files. Helpers are `private`
   unless there is a documented reason to export; list every new declaration
   (public and private) in the PR — the next audit round blind-restates them.
   If a helper belongs in a shared file (`Finite.lean`; the vendored
   `Configuration.lean`/`Deterministic.lean` are **frozen**): add a `private`
   copy in your file and record the request under "Requested shared lemmas" in
   the PR.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration. You may
   append to a docstring's proof-sketch paragraph if the delivered proof
   deviates; flag such updates in the PR.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction under
   "Escalations" in the PR, and continue with the other target.
4. Do not remove, weaken, or fill any sorry outside your target list.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep their
   docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets

### 1. `Complexity.PAL_mem_DTIME_linear` (Examples.lean)

`PAL ∈ DTIME (fun n => n + 1)`: exhibit `c` and a machine deciding palindromes
within `c * (n + 1)`. The file's docstring sketch gives the machine — one work
tape, phases `copy` / `rewind` / `test`:

1. *Copy* (`n + 1` steps): input head and work head move right in unison,
   copying each input symbol; ends when the input head reads the boundary blank.
2. *Rewind* (`n + 1` steps): input head walks back to the left boundary (the
   clamp at `0` — `Turing.moveInputPos` — makes the walk safe); one step of the
   work head left onto the last copied symbol.
3. *Test* (`n + 1` steps): input head right, work head left, in unison,
   comparing; mismatch → emit `false`, halt; input head reads blank again →
   emit `true`, halt.

`audits/phase1-findings.md` (the `PAL_mem_DTIME_linear` row) confirms the
boundary transitions and that constant `3` (any `c ≥ 3`, e.g. `c = 4` per the
sketch) covers every input including `n = 0` (three boundary transitions
emitting `true`). Proof shape: per-phase run invariants by induction (the copy
phase generalizes `idTM_run` with a work tape: after `t` steps, work-tape cells
`0..t-1` hold the first `t` input bits and the work head is at `t`); note the
target output is `[MultiTapeTM.indicator (PAL : Set (List Bool)) x]`, so you
will relate the mismatch/match outcome to `x = x.reverse` — expect a small
list-lemma bridge (e.g. comparing `x` against its reversal position by position:
`x.reverse.get ⟨i, _⟩ = x.get ⟨n - 1 - i, _⟩`-style, via `List.getElem_reverse`
at the pin). Work-tape cells are ℤ-indexed `Option Bool`; blanks are `none`.

### 2. `Complexity.timeConstructible_id` (TimeConstructible.lean)

`TimeConstructible id`: the `∀ n, n ≤ id n` half is `le_refl`; the content is a
machine computing `x ↦ (Nat.bits x.length)` within `c * (x.length + 1)`. The
audited construction (`audits/phase1-reaudit-findings.md`, the explicit counter
witness) is a one-work-tape, four-state machine `count`/`carry`/`rewind`/`emit`
maintaining a little-endian binary counter:

- For each input symbol read, increment the counter: walk right from cell `0`
  over `true` cells flipping them `false` (`carry`), write `true` in the first
  `false`/blank cell, walk back to cell `0` (`rewind`), advance the input head
  (`count`).
- When the input head reads the boundary blank, walk the counter left to right
  emitting each bit (`emit`), and halt at the first blank counter cell. For
  `n = 0` the counter region is empty and nothing is emitted — matching
  `Nat.bits 0 = []` (`Nat.bits` is least-significant-bit first).

**The amortized accounting is the crux.** Increment `i` costs
`Θ(trailing-ones of i)`, so a per-increment worst-case bound gives only
`O(n log n)` — not enough. You need the global bound: total carry work over
increments `0, 1, …, n−1` is at most `2n` (each cell flip `false → true`
happens once per increment and pays for the single later flip back). Two
formalization routes — pick whichever goes through:

- **Potential invariant**: strong induction maintaining "after `i` increments,
  the work tape holds the bits of `i`, the head is at `0`, and the total steps
  so far are `≤ B(i)`" with an explicit `B(i) ≤ c₀ * (i + 1)` — e.g.
  `B(i) = c₀*i + (number of true bits of i)`-style so the per-increment cost
  telescopes against the popcount change (cost of increment ≈ 2·(trailing ones)
  + O(1), and popcount drops by (trailing ones) − 1).
- **Closed sum**: prove `∑_{i<n} (trailing ones of i) ≤ n` (equivalently
  `∑ carries = n − popcount n`) as a standalone `private` arithmetic lemma by
  induction, then bound the run time by the sum.

The reaudit findings' field calculation (variables `r` = trailing ones, `v` =
high part, `j` = carry lengths) is exactly this arithmetic — mirror it. Also
budget the final `emit` phase: `O(|Nat.bits n|) ≤ O(n)` steps, and the emitted
list must be *exactly* `Nat.bits x.length` — expect small `Nat.bits` bridging
lemmas (`Nat.bits` interacts with `Nat.bit`/parity; `Mathlib.Data.Nat.Bits` is
already imported in this file). The stated bound has an existential `c > 0` —
be generous; no tight constant is needed.

## Out-of-scope sorries you will see (leave every one untouched)

`universal`, `universal_quadratic`, `timed_universal` (Universal.lean);
`computesFunInTime_const`, `computesFunInTime_ifEq`, `computesFunInTime_comp`,
`exists_comp_partial`, `exists_cond` (Composition.lean); `pairEncode_injective`,
`computesFunInTime_pairEncode_diag`, `exists_effectiveMachineCode`,
`exists_codeTM` (Encoding.lean); `alphabet_reduction`, `one_work_tape`,
`nonnegative_heads`, `oblivious_of_mem_DTIME` (Robustness/);
`Computes.exists_computesFunInTime` (Computable.lean); `UC_not_computable`
(Diagonalization.lean); `UC_computable_of_HALT_computable` (Halting.lean).

## PR checklist (all of it in the PR description)

- [ ] Targets filled (2), one line each on how the proof went vs the sketch —
      in particular, which amortization route `timeConstructible_id` took.
- [ ] New declarations (public and private) listed, for audit restatement —
      call out any standalone arithmetic lemmas (carry sums, `Nat.bits`
      bridges) that might merit later promotion.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Verification evidence: final full-sweep log tail; zero `error:` lines.
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin).
- Core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: `split <;> simp <;> omega`.
- After `cases hs : cfg.state`, insert `dsimp only` to iota-reduce
  `match some q with …` before rewriting, or use nested `split`.
- Avoid bare `simp` when hypotheses use folded forms (`initCfg` is `@[simp]`);
  prefer targeted `simp only`.
- `ring` needs `import Mathlib.Tactic.Ring`.
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` or un-beta-reduced lambdas:
  normalize with `show` / `simp only` first (see `idTM_run` in
  `Composition.lean`).
- SignType lemma names at the pin: `SignType.coe_one`, `SignType.neg_eq_neg_one`,
  `SignType.coe_neg_one`, `SignType.pos_eq_one`.
- Vendored API: `MultiTapeTM.runFrom_succ_eq_step'`, `MultiTapeTM.step`,
  `Action.apply`, `Cfg.inputSymbol` (double `dite`),
  `moveInputPos_pos_of_ne_right`, `inputSymbolInner`; work tapes are ℤ-indexed
  `Option Symbol` functions updated via `Function.update`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩` (pattern in `Finite.lean`'s `mono`/`output_unique`).

---

# ATTACHMENT C — Lean sources (modified modules first, then the rest)

## ===== TCSlib/Complexity/TuringMachine/Composition.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition of Turing machine computations

Basic computability combinators for the bundled machines: the identity and constant
functions are linear-time computable, and time-bounded computability is closed under
composition. Composition is the load-bearing lemma of the whole development — the
universal machine (phase 3) and the `HALT` reduction (phase 4) are built from it — and
it is the part [AB09] never spells out, dispatching it with "high-level descriptions"
of machines. The Isabelle AFP `Cook_Levin` entry spends a large fraction of its effort
exactly here.

## Design

Composition is stated at the *specification* level (`ComputesFunInTime`), not as an
operator on raw machines: the composed machine is existentially produced. Internally
(proof obligation, not API) the construction simulates `M₁` with its emissions
redirected to a fresh work tape, then simulates `M₂` reading that tape in place of its
input tape.

**Convention obligation status** (phase-1 audit finding 4; phase-2 audit finding 3):
this file does *not* formally discharge the append-only vs read-write output-tape
bridge. Every statement here — hypotheses and conclusions alike — lives in the
append-only model, and [AB09]'s read-write-output machine is not formalized in this
development, so no simulation between the two conventions can even be stated yet. The
obligation is recorded in the plan's decision log as **waived**, with the compensating
restriction that no exact-step-count transfer from [AB09] is ever claimed: every bound
*adapted from the source* carries an existential constant (purely internal results,
such as the oracle lockstep lemmas, are legitimately exact but never cross a
convention), and every result is self-contained in-model. A formal bridge (a
read-write-output machine variant plus a simulation theorem) will be added if and only
if a downstream result needs it. What this file *does* provide is the buffer-and-flush
technique — an emission can be deferred to a work tape and flushed at the end — which
is what delayed or revisable output looks like *within this model*; whether the
append-only convention matches [AB09]'s read-write one remains formally unestablished,
per the waiver.

## Main results

* Time-bounded combinators (all over the binary alphabet):
  `Turing.FinTM.computesFunInTime_id`, `Turing.FinTM.computesFunInTime_const`,
  `Turing.FinTM.computesFunInTime_ifEq`, `Turing.FinTM.computesFunInTime_comp`.
* **Partial (guarded) combinators** — the phase-4 API mandated by the phase-3 audit
  (round 2, finding 10 and Argument F: the total-function composition cannot take
  the partially computing universal evaluator as a component):
  `Turing.FinTM.exists_comp_partial` composes two arbitrary machines at the level of
  their halting relations, with the intermediate output buffered on a work tape;
  `Turing.FinTM.exists_cond` branches between two machines on a decided predicate.
  Both are stated untimed; time-bounded refinements are deliberately deferred until
  a result needs them.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
* [Balbach22] F. J. Balbach, *The Cook-Levin theorem*, Archive of Formal Proofs
  (Isabelle), 2022 — the composition-combinator architecture this file follows in
  spirit.
-/

namespace Turing.FinTM

/-- The one-state copy machine: emits each input bit moving right, and halts on the
boundary blank. -/
private def idTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some b => ⟨SignType.pos, fun i => i.elim0, some b, some ()⟩
        | none => ⟨SignType.zero, fun i => i.elim0, none, none⟩ }

/-- Run invariant of the copy machine: after `t ≤ n` steps it is live, its input head
sits at position `t + 1`, and it has emitted exactly the first `t` input bits. -/
private lemma idTM_run (x : List Bool) : ∀ t, t ≤ x.length →
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).state = some () ∧
    (((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) = t + 1) ∧
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).output = x.take t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hpos, hout⟩ := ih (Nat.le_of_succ_le ht)
    have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (t + 1) =
        (idTM.tm.tr () (some (x[t]'(by omega)))
          ((idTM.tm.runFrom (idTM.tm.initCfg x) t).workTapeSymbols)).apply
          (idTM.tm.runFrom (idTM.tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show ((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- The identity function is computable in linear time: the copy machine halts within
`n + 1` steps having emitted its input verbatim (invariant `idTM_run`, then one
halting step on the boundary blank). -/
theorem computesFunInTime_id :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id fun n => c * (n + 1) := by
  refine ⟨idTM, 1, fun x => ?_⟩
  obtain ⟨hstate, hpos, hout⟩ := idTM_run x x.length (le_refl _)
  have h0 : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputPos ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hsym : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputSymbol = none := by
    unfold Cfg.inputSymbol
    rw [dif_neg h0, dif_pos (by omega)]
  have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (x.length + 1) =
      (idTM.tm.tr () none
        ((idTM.tm.runFrom (idTM.tm.initCfg x) x.length).workTapeSymbols)).apply
        (idTM.tm.runFrom (idTM.tm.initCfg x) x.length) := by
    rw [MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    rw [hstate]
    dsimp only
    rw [hsym]
  have hbase : idTM.ComputesInTime x x (x.length + 1) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout]
      simp
  exact hbase.mono (le_of_eq (one_mul _).symm)

/-- One step of a fixed-word emission chain, with an arbitrary state embedding.
The input and all work tapes are left untouched. -/
private def emitAction {k : ℕ} {S : Type} (w : List Bool)
    (e : Fin (w.length + 1) → S) (i : Fin (w.length + 1)) : Action k Bool S :=
  if h : i.val < w.length then
    ⟨0, fun _ => (none, 0), some w[i.val], some (e ⟨i.val + 1, by omega⟩)⟩
  else
    ⟨0, fun _ => (none, 0), none, none⟩

/-- After `t` emission steps the state is the `t`-th chain state and exactly the
first `t` symbols have been appended. The induction uses no tape invariant because
emission transitions ignore all reads. -/
private lemma emit_run {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    ∀ t (ht : t ≤ w.length),
      (tm.runFrom cfg t).state = some (e ⟨t, by omega⟩) ∧
      (tm.runFrom cfg t).output = cfg.output ++ w.take t := by
  intro t
  induction t with
  | zero =>
    intro ht
    exact ⟨hs, by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hout⟩ := ih (by omega)
    have hstep : tm.runFrom cfg (t + 1) =
        (emitAction w e ⟨t, by omega⟩).apply (tm.runFrom cfg t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      exact congrArg (fun a => a.apply (tm.runFrom cfg t)) (htr _ _ _)
    rw [hstep]
    simp only [emitAction, dif_pos (show t < w.length by omega), Action.apply]
    refine ⟨True.intro, ?_⟩
    rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp [List.append_assoc]

/-- One further, nonemitting step halts the fixed-word emission chain. -/
private lemma emit_halts {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    (tm.runFrom cfg (w.length + 1)).state = none ∧
      (tm.runFrom cfg (w.length + 1)).output = cfg.output ++ w := by
  obtain ⟨hstate, hout⟩ := emit_run tm w e htr cfg hs w.length (le_refl _)
  rw [MultiTapeTM.runFrom_succ_eq_step']
  unfold MultiTapeTM.step
  rw [hstate]
  dsimp only
  rw [htr]
  simp [emitAction, Action.apply, hout]

/-- The zero-work-tape machine whose states form the emission chain for `w`. -/
private def constTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm := { q₀ := 0, tr := fun i _ _ => emitAction w id i }

/-- Every constant function is computable in linear time (in fact in time `|w| + 1`,
which the stated bound dominates once `c ≥ |w| + 1`).

**Proof sketch.** A zero-work-tape machine with `|w| + 1` states `s₀, …, s_{|w|}`:
state `sᵢ` emits the `i`-th symbol of `w` and moves to `s_{i+1}`, ignoring the input;
`s_{|w|}` halts. -/
theorem computesFunInTime_const (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) fun n => c * (n + 1) := by
  refine ⟨constTM w, w.length + 1, fun x => ?_⟩
  obtain ⟨hs, ho⟩ := emit_halts (constTM w).tm w id (fun _ _ _ => rfl)
    ((constTM w).tm.initCfg x) rfl
  have hbase : (constTM w).ComputesInTime x w (w.length + 1) := by
    exact ⟨_, hs, by simpa only [MultiTapeTM.initCfg, Cfg.init, List.nil_append] using ho, rfl⟩
  exact hbase.mono (Nat.le_mul_of_pos_right _ (by omega))

/-- An action that only moves the input head and changes the state. -/
private def controlAction {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    Action k Bool S := ⟨m, fun _ => (none, 0), none, q⟩

/-- Read position `i + 1` as the optional `i`-th input symbol, including the
right boundary. -/
private lemma inputSymbol_at {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (i : ℕ) (hi : i ≤ x.length)
    (hp : cfg.inputPos.val = i + 1) : cfg.inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [inputSymbolInner i (by omega) h, List.getElem?_eq_getElem h]
  · have he : i = x.length := by omega
    have hz : cfg.inputPos ≠ 0 := by
      intro hz
      rw [hz] at hp
      simp at hp
    simp only [Cfg.inputSymbol, dif_neg hz, dif_pos (show cfg.inputPos.val = x.length + 1 by omega)]
    simp [he]

/-- The hardcoded comparator, followed by the chosen fixed-word emission chain. -/
private def ifEqTM (w₀ u v : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w₀.length + 1) ⊕ (Fin (u.length + 1) ⊕ Fin (v.length + 1))
  tm :=
    { q₀ := .inl 0
      tr := fun q inp _ => match q with
        | .inl i =>
          if h : i.val < w₀.length then
            if inp = some w₀[i.val] then
              controlAction .pos (some (.inl ⟨i.val + 1, by omega⟩))
            else controlAction 0 (some (.inr (.inr 0)))
          else if inp = none then controlAction 0 (some (.inr (.inl 0)))
            else controlAction 0 (some (.inr (.inr 0)))
        | .inr (.inl i) => emitAction u (fun j => .inr (.inl j)) i
        | .inr (.inr i) => emitAction v (fun j => .inr (.inr j)) i }

/-- Once the comparator has chosen its output chain, that chain emits the selected
word and halts, independently of the input-head position. -/
private lemma ifEq_finish (w₀ u v x : List Bool) (b : Bool)
    (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x)
    (hs : cfg.state = some (.inr (cond b (.inl 0) (.inr 0)))) (ho : cfg.output = []) :
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).state = none ∧
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).output = cond b u v := by
  cases b
  · simpa only [Bool.cond_false, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm v (fun j => .inr (.inr j))
        (fun _ _ _ => rfl) cfg hs
  · simpa only [Bool.cond_true, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm u (fun j => .inr (.inl j))
        (fun _ _ _ => rfl) cfg hs

/-- Comparison invariant: the first `i` symbols match, and the head is at `i + 1`.

**Proof sketch.** Induct on the number of remaining comparison symbols. A matching
symbol advances the invariant. A mismatch selects the second emission chain. With
no symbols remaining, the boundary blank selects the first chain and an extra
symbol selects the second. The emission-chain lemma supplies the remaining time. -/
private lemma ifEq_run (w₀ u v x : List Bool) : ∀ (r i : ℕ) (hlen : w₀.length = i + r), i ≤ x.length → x.take i = w₀.take i →
    ∀ (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x),
      cfg.state = some (.inl ⟨i, by omega⟩) → cfg.inputPos.val = i + 1 → cfg.output = [] →
      ∃ t, t ≤ r + max u.length v.length + 2 ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).state = none ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).output = if x = w₀ then u else v := by
  intro r
  induction r with
  | zero =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : ¬i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases he : x = w₀
    · subst x
      have hb : w₀[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inl 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inl 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v w₀ true _ hs' ho'
      refine ⟨u.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_true, if_pos rfl] using hf
    · have hx : i < x.length := by
        by_contra hh
        have hxt : x.take i = x := List.take_of_length_le (by omega)
        have hwt : w₀.take i = w₀ := List.take_of_length_le (by omega)
        exact he (by rw [← hxt, ← hwt]; exact hprefix)
      have hb : x[i]? = some x[i] := List.getElem?_eq_getElem hx
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, Option.some_ne_none, ite_false]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf
  | succ r ih =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases hm : x[i]? = some w₀[i]
    · obtain ⟨hx, hbit⟩ := List.getElem?_eq_some_iff.mp hm
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction .pos (some (.inl ⟨i + 1, by omega⟩))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, hm, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state =
          some (.inl ⟨i + 1, by omega⟩) := by rw [hstep]; rfl
      have hp' : ((ifEqTM w₀ u v).tm.step cfg).inputPos.val = (i + 1) + 1 := by
        rw [hstep]
        change (moveInputPos cfg.inputPos .pos).val = i + 1 + 1
        rw [moveInputPos_pos_of_ne_right _ (by omega)]
        simp only
        omega
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hprefix' : x.take (i + 1) = w₀.take (i + 1) := by
        rw [List.take_succ, List.take_succ, hprefix, hm, List.getElem?_eq_getElem hi]
      obtain ⟨t, ht, htstate, htout⟩ := ih (i + 1) (by omega) (by omega) hprefix'
        ((ifEqTM w₀ u v).tm.step cfg) hs' hp' ho'
      refine ⟨t + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      exact ⟨htstate, htout⟩
    · have he : x ≠ w₀ := by
        intro he
        subst x
        exact hm (List.getElem?_eq_getElem hi)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, if_neg hm]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf

/-- Testing equality with a fixed string is computable in linear time: for any fixed
`w₀ u v`, the function `w ↦ u` if `w = w₀` and `w ↦ v` otherwise. (Instantiated by
the `HALT` reduction as the postprocessor `w ↦ if w = [true] then [false] else
[true]`; see `TCSlib.Complexity.Uncomputability.Halting`.)

**Proof sketch.** Hardcode `w₀`, `u`, and `v` in the states. The machine walks the
input left to right comparing it against `w₀` symbol by symbol (`|w₀| + 1`
comparison states); on the first mismatch — including the input ending early (blank
read) or running long (a symbol where `w₀` is exhausted) — it switches to an
emission chain for `v`, and after matching all of `w₀` and then reading the boundary
blank it switches to an emission chain for `u` (at most `|u| + |v| + 2` further
states, one emitted symbol per step). Every run halts within
`|w₀| + max |u| |v| + 3` steps — a constant, absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_ifEq (w₀ u v : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun w => if w = w₀ then u else v) fun n => c * (n + 1) := by
  refine ⟨ifEqTM w₀ u v, w₀.length + max u.length v.length + 3, fun x => ?_⟩
  obtain ⟨t, ht, hs, ho⟩ := ifEq_run w₀ u v x w₀.length 0 (by omega) (by omega) rfl
    ((ifEqTM w₀ u v).tm.initCfg x) rfl (by simp) rfl
  have hbase : (ifEqTM w₀ u v).ComputesInTime x (if x = w₀ then u else v) t :=
    ⟨_, hs, ho, rfl⟩
  exact hbase.mono (Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega)))

/-- **Composition.** If `f` is computable within `T₁` and `g` within a monotone `T₂`,
then `g ∘ f` is computable within `c · (T₁ n + T₂ (T₁ n) + 1)`.

The inner bound `T₂ (T₁ n)` is valid because the intermediate string is no longer than
the time that produced it: `|f x| ≤ T₁ |x|` by `Turing.MultiTapeTM.output_length_le`.
Monotonicity of `T₂` is genuinely needed to convert that length bound into a time
bound.

**Proof sketch.** Build `M` with `M₁.k + M₂.k + 1` work tapes over `Bool`. Phase one
simulates `M₁` step for step on the true input, with `M₁`'s emissions written instead
onto the dedicated intermediate tape (constant overhead per step; this is the
append-only-output buffering discussed in the module docstring). Phase two rewinds the
intermediate tape head (at most `T₁ n` steps) and simulates `M₂` step for step, with
`M₂`'s input-head reads served from the intermediate tape and `M₂`'s emissions going to
the real output tape. Phase two costs constant overhead per step of `M₂`, which halts
within `T₂ |f x| ≤ T₂ (T₁ n)` steps. Bookkeeping (phase switching, boundary detection
on the intermediate tape) is absorbed into `c`. -/
theorem computesFunInTime_comp {M₁ M₂ : FinTM Bool} {f g : List Bool → List Bool}
    {T₁ T₂ : ℕ → ℕ}
    (h₁ : M₁.ComputesFunInTime f T₁) (h₂ : M₂.ComputesFunInTime g T₂)
    (hT₂ : Monotone T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (g ∘ f) fun n => c * (T₁ n + T₂ (T₁ n) + 1) := by
  sorry

/-- **Partial (guarded) sequential composition** — the phase-4 API obligation
identified by the phase-3 audit (round 2, finding 10 and Argument F):
`Turing.FinTM.computesFunInTime_comp` requires both components to compute *total*
functions, so it cannot take a partially computing machine — such as the universal
evaluator — as a component. This lemma composes two arbitrary machines at the level
of their halting relations, with **no totality or time hypotheses**: `M` behaves on
`x` exactly as `M₂` behaves on `M₁`'s completed output — halting, completed outputs,
and divergence all correspond.

Statement notes. The intermediate string `y` is existentially quantified, but by
`Turing.FinTM.ComputesInTime.output_unique` at most one `y` satisfies the first
conjunct, so the right-hand side reads "`M₁` halts on `x` (necessarily with a unique
`y`), and then `M₂` halts on `y` with `w`". If `M₁` diverges on `x`, or halts but
`M₂` diverges on its output, both sides are empty — `M` diverges. A time-bounded
refinement is deliberately not stated; it will be added if and when a result needs
it.

**Proof sketch** (buffered intermediate output, per the audit's design). `M` carries
`M₁`'s and `M₂`'s work tapes plus a fresh *buffer* tape. Phase one simulates `M₁` on
the true input step for step, with each emission of `M₁` written to the buffer tape
(write, move right) instead of the output tape; the append-only output discipline
makes the buffer region a verbatim copy of `M₁`'s output, contiguous from the
initial head cell. If `M₁` never halts, neither does `M`. On `M₁`'s halting
transition, `M` rewinds the buffer head to the leftmost written cell — the head
rests on the blank immediately *right* of the written word, so the rewind's first
left move is unconditional (testing the current cell before moving would stop at the
wrong end; phase-4 audit, finding 3), then left while reading a symbol, then one
step right. Phase two simulates `M₂` with its *input-tape
reads served from the buffer*: the buffer holds exactly `y` with blank cells on both
sides, and `M` maintains `M₂`'s virtual input position on it, mirroring the clamped
input-head semantics of `Turing.moveInputPos` at both boundaries — the same
virtual-boundary emulation as the universal machine's sketch
(`TCSlib.Complexity.TuringMachine.Universal`); a blank read identifies a boundary,
and *which* boundary is determined by the direction of arrival, tracked in the
state — for an empty intermediate word the simulation starts with the right-boundary
tag already set, the left boundary one inward move away (phase-4 audit, finding 3).
`M₂`'s work-tape actions go to its own fresh tapes and its emissions to the
real output tape, untouched during phase one. `M` halts exactly when the simulated
`M₂` halts; step-for-step run correspondence in each phase gives both directions of
the iff. -/
theorem exists_comp_partial (M₁ M₂ : FinTM Bool) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ y : List Bool,
          (∃ t, M₁.ComputesInTime x y t) ∧ ∃ t, M₂.ComputesInTime y w t := by
  sorry

/-- Extend an action to the left block of a disjoint tape sum and rename states. -/
private def leftAction {k : ℕ} {S S' : Type} (l : ℕ) (f : S → S')
    (a : Action k Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases a.workTapes (fun _ => (none, 0))
  output := a.output
  state := a.state.map f

/-- Extend an action to the right block, leaving the left block untouched. -/
private def rightAction {l : ℕ} {S S' : Type} (k : ℕ) (f : S → S')
    (a : Action l Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases (fun _ => (none, 0)) a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a configuration in the left tape block, retaining arbitrary inactive
right tapes and head positions. The state renaming preserves halting. -/
private def leftCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes tapes
  workTapePos := Fin.addCases c.workTapePos heads
  output := c.output

/-- Embed in the right block, retaining arbitrary inactive left tapes. This is also
used when the left block contains a completed controller's work. -/
private def rightCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases tapes c.workTapes
  workTapePos := Fin.addCases heads c.workTapePos
  output := c.output

/-- Extending an action commutes with the left configuration embedding. -/
private lemma leftCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action k Bool S) (c : Cfg k Bool S x)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (leftAction l f a).apply (leftCfg f c tapes heads) =
      leftCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]

/-- Extending an action commutes with the right configuration embedding. -/
private lemma rightCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action l Bool S) (c : Cfg l Bool S x)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    (rightAction k f a).apply (rightCfg f c tapes heads) =
      rightCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]

/-- A machine whose renamed transitions use only the left block simulates one
step exactly, including the absorbing halting configuration. -/
private lemma leftCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    tm'.step (leftCfg f c tapes heads) = leftCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [leftCfg, hs]
  | some q =>
    have hs' : (leftCfg f c tapes heads).state = some (f q) := by simp [leftCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (leftCfg f c tapes heads).workTapeSymbols (Fin.castAdd l i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, leftCfg]
    change (leftAction l f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact leftCfg_apply f _ c tapes heads

/-- The right-block version of the one-step correspondence; inactive tapes may
contain arbitrary data from an earlier phase. -/
private lemma rightCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    tm'.step (rightCfg f c tapes heads) = rightCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [rightCfg, hs]
  | some q =>
    have hs' : (rightCfg f c tapes heads).state = some (f q) := by simp [rightCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (rightCfg f c tapes heads).workTapeSymbols (Fin.natAdd k i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, rightCfg]
    change (rightAction k f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact rightCfg_apply f _ c tapes heads

/-- Lift the left-block one-step correspondence to every finite run. -/
private lemma leftCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (t : ℕ) :
    tm'.runFrom (leftCfg f c tapes heads) t = leftCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => leftCfg f c tapes heads)
    (fun c => leftCfg_step tm tm' f htr c tapes heads) c t

/-- Lift the right-block correspondence to every run, preserving arbitrary
inactive left tapes. This is the fresh-branch lockstep gadget. -/
private lemma rightCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (t : ℕ) :
    tm'.runFrom (rightCfg f c tapes heads) t = rightCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => rightCfg f c tapes heads)
    (fun c => rightCfg_step tm tm' f htr c tapes heads) c t

/-- Forget the uniquely determined space witness when reasoning about timed
computations. -/
private lemma computesInTime_iff (M : FinTM Bool) (x w : List Bool) (t : ℕ) :
    M.ComputesInTime x w t ↔
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = w := by
  constructor
  · rintro ⟨s, hs, ho, _⟩
    exact ⟨hs, ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨_, hs, ho, rfl⟩

/-- Put two machines in disjoint tape and state blocks; the Boolean chooses only
the initial state, while the transition table is independent of that choice. -/
private def branchTM (M₁ M₂ : FinTM Bool) (b : Bool) : FinTM Bool where
  k := M₁.k + M₂.k
  State := M₁.State ⊕ M₂.State
  tm :=
    { q₀ := cond b (.inl M₁.tm.q₀) (.inr M₂.tm.q₀)
      tr := fun q inp work => match q with
        | .inl q => leftAction M₂.k Sum.inl
            (M₁.tm.tr q inp (fun i => work (Fin.castAdd M₂.k i)))
        | .inr q => rightAction M₁.k Sum.inr
            (M₂.tm.tr q inp (fun i => work (Fin.natAdd M₁.k i))) }

/-- Each selected branch has exactly its original time and completed output.
The proof embeds its initial blank configuration, then uses lockstep. -/
private lemma branchTM_computes (M₁ M₂ : FinTM Bool) (b : Bool) (x w : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).ComputesInTime x w t ↔ (cond b M₁ M₂).ComputesInTime x w t := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr (fun _ _ _ => rfl)]
    simp only [rightCfg, Option.map_eq_none_iff]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl (fun _ _ _ => rfl)]
    simp only [leftCfg, Option.map_eq_none_iff]

/-- A control action leaves all work tapes, work heads, and output unchanged. -/
private lemma controlAction_apply {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (m : SignType) (q : Option S) :
    (controlAction m q).apply cfg =
      {cfg with state := q, inputPos := moveInputPos cfg.inputPos m} := by
  refine Cfg.ext rfl rfl rfl ?_ ?_
  · funext i
    simp [controlAction, Action.apply]
  · simp [controlAction, Action.apply]

/-- The clamped left move always subtracts one from the natural input position. -/
private lemma moveInputPos_neg_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos .neg).val = pos.val - 1 := by
  by_cases h : pos = 0
  · subst pos
    simp [SignType.neg_eq_neg_one]
  · rw [moveInputPos_neg_of_ne_left pos h]

/-- Starting at or to the left of the last input symbol, scan left to the left
blank, then move right and dispatch. All other configuration fields are preserved.

**Proof sketch.** Induct on the input-head position. At zero the scanned symbol is
blank, so one right move finishes. At a positive position the input symbol exists;
one left move reduces the position and the induction hypothesis finishes the run. -/
private lemma rewind_scan {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (cfg : Cfg k Bool S x), cfg.state = some scan → cfg.inputPos.val ≤ x.length →
      tm.runFrom cfg (cfg.inputPos.val + 1) = {cfg with state := dest, inputPos := 1} := by
  have aux : ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      tm.runFrom cfg (j + 1) = {cfg with state := dest, inputPos := 1} := by
    intro j
    induction j with
    | zero =>
      intro cfg hs hj _
      have hz : cfg.inputPos = 0 := Fin.ext hj
      have hsym : cfg.inputSymbol = none := by
        unfold Cfg.inputSymbol
        rw [dif_pos hz]
      change tm.step cfg = _
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [htr, hsym]
      dsimp only
      rw [controlAction_apply]
      have hm : moveInputPos cfg.inputPos .pos = 1 := by
        apply Fin.ext
        rw [hz, moveInputPos_pos_of_ne_right _ (by simp)]
        simp
      rw [hm]
    | succ j ih =>
      intro cfg hs hj hlen
      have hsym : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have hstep : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        unfold MultiTapeTM.step
        rw [hs]
        dsimp only
        rw [htr, hsym]
        dsimp only
        rw [controlAction_apply]
      have hp : (moveInputPos cfg.inputPos .neg).val = j := by
        rw [moveInputPos_neg_val]
        omega
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ih _ rfl hp (by omega)
  intro cfg hs hp
  exact aux cfg.inputPos.val cfg hs rfl hp

/-- From any valid input position, take the mandatory first left move and then
scan left. This returns to position `1`, even for an empty input or a start at a
boundary. No work tape or output is changed. -/
private lemma rewind_from_any {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t, tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_⟩
  rw [MultiTapeTM.runFrom_add]
  have hfirst : tm.runFrom cfg 1 = c := rfl
  rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
  simp only [c, hstep]

/-- A finite controller runs `D` with its first emission captured in a register,
rewinds, then enters the selected branch on disjoint fresh tapes. A simulated halt
is represented by a live control state so that dispatch occurs only after `D` halts.
An empty register at dispatch halts safely. -/
private def condTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := D.k + (M₁.k + M₂.k)
  State := (Option D.State × Option Bool) ⊕ (Option Bool ⊕ (M₁.State ⊕ M₂.State))
  tm :=
    { q₀ := .inl (some D.tm.q₀, none)
      tr := fun q inp work => match q with
        | .inl (some q, reg) =>
          let a := D.tm.tr q inp (fun i => work (Fin.castAdd (M₁.k + M₂.k) i))
          ⟨a.inputTape, Fin.addCases a.workTapes (fun _ => (none, 0)), none,
            some (.inl (a.state, reg.or a.output))⟩
        | .inl (none, reg) => controlAction .neg (some (.inr (.inl reg)))
        | .inr (.inl reg) => match inp with
          | some _ => controlAction .neg (some (.inr (.inl reg)))
          | none => controlAction .pos
              (reg.map (fun b => .inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
        | .inr (.inr q) => rightAction D.k (fun s => .inr (.inr s))
            ((branchTM M₁ M₂ false).tm.tr q inp (fun i => work (Fin.natAdd D.k i))) }

/-- Embed a controller configuration with its output suppressed and the first
output symbol stored in the finite register. All branch tapes remain blank. -/
private def controlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) : Cfg (condTM D M₁ M₂).k Bool (condTM D M₁ M₂).State x where
  state := some (.inl (c.state, c.output.head?))
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes (fun _ _ => none)
  workTapePos := Fin.addCases c.workTapePos (fun _ => 0)
  output := []

/-- Before the simulated controller halts, one composite step exactly updates its
configuration and the first-emission register. The head-of-append identity makes
this invariant valid even without any assumption on the controller's output. -/
private lemma controlCfg_step (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (hs : c.state ≠ none) :
    (condTM D M₁ M₂).tm.step (controlCfg D M₁ M₂ c) =
      controlCfg D M₁ M₂ (D.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (controlCfg D M₁ M₂ c).state = some (.inl (some q, c.output.head?)) := by
      simp [controlCfg, hq]
    rw [hs']
    dsimp only [condTM]
    have hr : (fun i => (controlCfg D M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (M₁.k + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [controlCfg, Cfg.workTapeSymbols]
    have hi : (controlCfg D M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    refine Cfg.ext ?_ rfl ?_ ?_ ?_
    · simp [controlCfg, Action.apply, List.head?_append, Option.head?_toList]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · simp [controlCfg, Action.apply]

/-- Controller lockstep holds through its first halting step. Subsequent composite
steps perform the rewind, so no claim of lockstep after halting is made. -/
private lemma controlCfg_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (h : ∀ s, s < t → (D.tm.runFrom c s).state ≠ none) :
    (condTM D M₁ M₂).tm.runFrom (controlCfg D M₁ M₂ c) t =
      controlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      controlCfg_step D M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- A completed singleton controller computation reaches the selected branch's
fresh initial configuration after a finite prefix.

**Proof sketch.** Choose the first halting time of `D` and use controller lockstep.
Output uniqueness identifies its completed output with `[b]`, so the register is
`some b`, including when that bit was emitted early. Rewind from the resulting
input position; the branch tapes and real output have remained untouched. -/
private lemma condTM_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool)
    (hD : ∃ t, D.ComputesInTime x [b] t) :
    ∃ (t : ℕ) (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
        rightCfg (fun q => .inr (.inr q)) ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads := by
  classical
  obtain ⟨tD, hDc⟩ := hD
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨tD, ((computesInTime_iff D x [b] tD).mp hDc).1⟩
  let t := Nat.find hh
  let cf := D.tm.runFrom (D.tm.initCfg x) t
  have hstop : cf.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x cf.output t :=
    (computesInTime_iff D x cf.output t).mpr ⟨hstop, rfl⟩
  have hout : cf.output = [b] := hc.output_unique hDc
  have hi : (condTM D M₁ M₂).tm.initCfg x = controlCfg D M₁ M₂ (D.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
  have hrun : (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
      controlCfg D M₁ M₂ cf := by
    rw [hi]
    exact controlCfg_run D M₁ M₂ (D.tm.initCfg x) t (fun s hs => Nat.find_min hh hs)
  obtain ⟨r, hr⟩ := rewind_from_any (condTM D M₁ M₂).tm
    (.inl (none, some b)) (.inr (.inl (some b)))
    (some (.inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (controlCfg D M₁ M₂ cf) (by simp [controlCfg, hstop, hout])
  refine ⟨t + r, cf.workTapes, cf.workTapePos, ?_⟩
  rw [MultiTapeTM.runFrom_add, hrun, hr]
  rfl

/-- **Branching on a decided predicate** — the second phase-4 combinator (phase-3
audit, round 2, Argument F, step 2 of the `HALT → UC` reduction): given a total
decider `D` for `p` and two branch machines, some machine behaves on every input
exactly as the branch selected by `p` does *on that same input*. The input tape is
read-only, so both branches see the original input.

**Proof sketch.** `D` computes the singleton output `[p x]` on every input, and
output is append-only, so along any run `D` emits exactly one symbol; simulate `D`
with that single emission recorded in a state register instead of emitted (no buffer
tape needed). On `D`'s halting transition, rewind the true input head to its initial
position: one step left, then left while reading a symbol, then one step right —
from any position this ends at input position `1`, the initial position, the clamp
at position `0` making the walk safe (including on empty input). Then transfer
control to a disjoint copy of `M₁` or `M₂` according to the register. The branches'
work tapes are fresh tapes `D` never touched, the output tape is untouched by phase
one, and the input head is back at its initial position, so the selected branch's
run is reproduced verbatim; determinism (`Turing.FinTM.ComputesInTime.output_unique`)
identifies `D`'s completed output with `[p x]`, so the selected branch is
`cond (p x) M₁ M₂`.

The implementation retains the first emission, with the exact invariant that the
register is the head of the simulated output. A live administrative state follows
the simulated halt before the first left move. For the forward implication, extend
any completed composite run beyond the verified branch-start prefix using absorbing
halting, then apply branch lockstep; the reverse implication concatenates that
prefix with the selected branch run. -/
theorem exists_cond (D M₁ M₂ : FinTM Bool) (p : List Bool → Bool)
    (hD : D.Computes fun x => [p x]) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ t, (cond (p x) M₁ M₂).ComputesInTime x w t := by
  refine ⟨condTM D M₁ M₂, fun x w => ?_⟩
  obtain ⟨a, tapes, heads, ha⟩ := condTM_start D M₁ M₂ x (p x) (hD x)
  have hr (t : ℕ) :
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) (a + t) =
        rightCfg (fun q => .inr (.inr q))
          ((branchTM M₁ M₂ (p x)).tm.runFrom ((branchTM M₁ M₂ (p x)).tm.initCfg x) t)
          tapes heads := by
    rw [MultiTapeTM.runFrom_add, ha]
    exact rightCfg_run (branchTM M₁ M₂ (p x)).tm (condTM D M₁ M₂).tm
      (fun q => .inr (.inr q)) (fun _ _ _ => rfl) _ tapes heads t
  constructor
  · rintro ⟨t, ht⟩
    have hc := (computesInTime_iff (condTM D M₁ M₂) x w (a + t)).mp
      (ht.mono (by omega))
    rw [hr t] at hc
    have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x w t :=
      (computesInTime_iff _ x w t).mpr
        ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
    exact ⟨t, (branchTM_computes M₁ M₂ (p x) x w t).mp hb⟩
  · rintro ⟨t, ht⟩
    have hb := (computesInTime_iff (branchTM M₁ M₂ (p x)) x w t).mp
      ((branchTM_computes M₁ M₂ (p x) x w t).mpr ht)
    refine ⟨a + t, (computesInTime_iff _ x w (a + t)).mpr ?_⟩
    rw [hr t]
    exact ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hb.1, hb.2⟩

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Encoding.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim).
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
* `Turing.exists_effectiveMachineCode` — a concrete effective scheme exists.
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
private def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The aligned parser recovers both components, by induction on the first word. -/
private lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-- Six-state pairing controller: double-stay, double-move, emit-true,
first-left, rewind, and copy. The double-stay state's blank branch emits `false`. -/
private def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
private def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- Fixed two-bit serialization of an optional bit. -/
private def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
private def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- Self-delimiting unary serialization of a state index. -/
private def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- Serialization of an optional successor state (`none` = halt). -/
private def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- Serialization of one transition record. -/
private def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- A concrete effective representation scheme exists.

**Proof sketch.** Take `encode := CodeTM.serialize` — which records the state count,
the initial state, and the table (finding 5) — and let `decode` run the aligned-pair
parser of `pairEncode_injective` on the doubled-bit region to recover `numStates`,
then parse the unary initial state and the `9 · (numStates + 1)` fixed-format records;
any malformation (including trailing non-`true` junk) yields a canonical trivial
machine, making `decode` total. The parser **short-circuits on the first incomplete
record** (equivalently, rejects up front any state count whose minimum table length
exceeds the remaining input), so a short malformed string declaring a huge binary
state count is rejected in time polynomial in the string, not by enumerating its
missing records (round-2 audit, finding 8). A complete serialization determines its own length,
and the parser ignores a trailing all-`true` suffix, giving `decode_encode_pad`. The
`canonizer` is a machine implementing exactly this parse followed by re-serialization
(on valid codes, the identity up to padding removal; on invalid ones, the trivial
machine's serialization), with a polynomial `canonizerTime`; its construction uses
the composition combinators of `TCSlib.Complexity.TuringMachine.Composition`. -/
theorem exists_effectiveMachineCode : Nonempty EffectiveMachineCode := by
  sorry

/-- Rename the successor state of an action, leaving every tape action unchanged. -/
private def codeMapAction {k : ℕ} {Γ Q Q' : Type*} (e : Q → Q')
    (a : Action k Γ Q) : Action k Γ Q' :=
  { a with state := a.state.map e }

/-- Rename a configuration's optional state, preserving its tapes, heads, and output. -/
private def codeMapCfg {k : ℕ} {Γ Q Q' : Type*} {x : List Γ} (e : Q → Q')
    (cfg : Cfg k Γ Q x) : Cfg k Γ Q' x :=
  { cfg with state := cfg.state.map e }

/-- State renaming commutes with applying an action. -/
private lemma codeMapCfg_apply {k : ℕ} {Γ Q Q' : Type*} {x : List Γ} (e : Q → Q')
    (a : Action k Γ Q) (cfg : Cfg k Γ Q x) :
    (codeMapAction e a).apply (codeMapCfg e cfg) = codeMapCfg e (a.apply cfg) := rfl

/-- Transport a machine's initial state and transition table through a state bijection. -/
private def codeRelabelTM {k : ℕ} {Γ Q Q' : Type*} (e : Q ≃ Q')
    (tm : MultiTapeTM k Γ Q) : MultiTapeTM k Γ Q' where
  q₀ := e tm.q₀
  tr := fun q inp ws => codeMapAction e (tm.tr (e.symm q) inp ws)

/-- Relabeling commutes with each transition, including absorbing halting. -/
private lemma codeRelabel_step {k : ℕ} {Γ Q Q' : Type*} {x : List Γ} (e : Q ≃ Q')
    (tm : MultiTapeTM k Γ Q) (cfg : Cfg k Γ Q x) :
    (codeRelabelTM e tm).step (codeMapCfg e cfg) = codeMapCfg e (tm.step cfg) := by
  have hin : (codeMapCfg e cfg).inputSymbol = cfg.inputSymbol := rfl
  have hwork : (codeMapCfg e cfg).workTapeSymbols = cfg.workTapeSymbols := rfl
  unfold MultiTapeTM.step
  cases hs : cfg.state with
  | none => simp [codeMapCfg, hs]
  | some q =>
    rw [show (codeMapCfg e cfg).state = some (e q) by
      simp only [codeMapCfg, hs, Option.map_some]]
    dsimp only
    rw [hin, hwork]
    simp only [codeRelabelTM, Equiv.symm_apply_apply]
    exact codeMapCfg_apply e _ cfg

/-- The initialized runs correspond at every step by iterating step commutation. -/
private lemma codeRelabel_run {k : ℕ} {Γ Q Q' : Type*} (e : Q ≃ Q')
    (tm : MultiTapeTM k Γ Q) (x : List Γ) (t : ℕ) :
    (codeRelabelTM e tm).runFrom ((codeRelabelTM e tm).initCfg x) t =
      codeMapCfg e (tm.runFrom (tm.initCfg x) t) :=
  MultiTapeTM.runFrom_comm_of_step (codeMapCfg e) (codeRelabel_step e tm) (tm.initCfg x) t

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation uses the private helper `codeMapAction` for state renaming,
eliminates `hk` after destructuring the bundle, and iterates step commutation via
`MultiTapeTM.runFrom_comm_of_step`. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  classical
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨Fintype.card Q - 1, codeRelabelTM e tm⟩, ?_⟩
  intro x output t
  simp only [CodeTM.toFinTM, FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace,
    codeRelabel_run, codeMapCfg, Option.map_eq_none_iff]
  constructor
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Universal.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The universal Turing machine

[AB09, §1.4.1 and Theorem 1.9, relaxed form]: there is a single machine `U` that,
given a code and an input, simulates the machine the code denotes — `U(x, α) =
M_α(x)` — with the simulation overhead depending only on the code, not on the input.

## Design and deviations from [AB09] (all shaped by the phase-3 audit)

* Statements are relative to an `Turing.EffectiveMachineCode`: the purely algebraic
  scheme admits noncomputable-meaning pathologies against which no universal machine
  exists (audit finding 1, Argument A).
* **Input layout is `pairEncode α x` — code first, input second** — deviating from
  [AB09]'s `⟨x, α⟩`: with the input first, the startup cost of reaching the code
  grows with `|x|` and the stated bounds are false (audit finding 2, Argument B).
  With the code first, startup (parsing and canonizing `α`) costs a constant
  depending only on `α`, absorbed into `C`, and the simulated input head walks the
  verbatim `x` region on demand.
* `universal` is the **all-string evaluator** [AB09's `U(x, α) = M_α(x)`, p. 20]:
  it covers every `α` through `c.decode` (padded and fallback representations
  included), and it carries **both directions** — the forward time bound, and the
  converse that any *completed* output of `U` (output on halting; intermediate
  emissions of a non-halting run are unconstrained) is a completed output of the
  simulated machine, so divergence is preserved (round-1 finding 3; round-2
  Argument C).
* The constant `C` depends on the **representation** `α`, a documented weakening of
  [AB09]'s machine-dependent constant that is *necessary* at this generality: an
  effective scheme can reserve arbitrarily long identical-prefix representations of
  two fixed machines, defeating any constant that factors through `c.decode α`
  (round-2 audit, finding 6 and Argument E). Recovering the book's dependence would
  require further representation assumptions.
* **The core bound is linear**, `C · (t + 1)`: coded machines are already in
  one-work-tape binary normal form, so `U` pays a constant per simulated step.
  [AB09]'s relaxed quadratic bound reappears in `universal_quadratic`, where an
  *arbitrary* binary machine is first normal-formed ([AB09, Claims 1.5-1.6]); that
  corollary is stated — and labeled — at the level of **total function computation**
  (audit finding 4), the machine-level partial statement being `universal` itself.
  The `O(T log T)` sharpening ([AB09, §1.7]) is the phase-5 stretch goal.
* `timed_universal` outputs `true :: output` on success and `[false]` on timeout, a
  concrete rendering of [AB09]'s "special failure symbol" (§1.4.1); its budget is
  quadratic (binary clock maintenance). The deadline convention: halting is checked
  after every simulated transition *including the `t`-th*, so a machine first
  halting exactly at the deadline is a success; at budget `0` no initialized machine
  has halted, and the timeout branch applies (audit finding 6).

## Main results

* `Turing.universal` — the all-string evaluator [AB09, Theorem 1.9 core].
* `Turing.universal_quadratic` — the relaxed quadratic form for total functions of
  arbitrary binary machines [AB09, Theorem 1.9 as proved in §1.4.1].
* `Turing.timed_universal` — the time-bounded universal machine [AB09, §1.4.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21; Figure 1.6.)
-/

namespace Turing

/-- **The universal machine as an all-string evaluator** [AB09, Theorem 1.9]: for any
effective scheme there is a single machine `U` such that for every string `α` there
is a constant `C` (depending on `α`, absorbing its decoding) with, for every input
`x`: whenever the machine `α` denotes halts on `x` within `t` steps with `output`,
`U` on `pairEncode α x` halts with the same output within `C · (t + 1)` steps —
and conversely every *completed* output of `U` on `pairEncode α x` (its output on
halting) is a completed output of the denoted machine on `x`, so divergence is
preserved.

**Proof sketch** (after [AB09, Figure 1.6], adapted to the code-first layout).
Startup: `U` runs the scheme's `canonizer` on the doubled-bit `α`-region (via the
composition combinators), leaving the fixed serialization of `M := c.decode α` — the
state count, initial state, and table — on a *table* work tape, and writes the
initial state on a *state* tape; cost `O(canonizerTime |α| + |α| + 1)`, a constant
for fixed `α`, absorbed into `C`. `U`'s input head then parks at the start of the
verbatim `x` region, and a *work* tape mirrors `M`'s work tape. **The simulated
input's left boundary must be emulated explicitly** (round-2 audit, finding 3): the
cell physically left of the `x` region is the pairing delimiter's `true`, not a
blank, so `U` keeps a marker on a spare work tape whose head tracks the virtual
input position — at virtual position zero it supplies a blank read and suppresses
further outward moves (mirroring `moveInputPos`'s clamp), and for empty `x` the
virtual head starts at the right boundary blank adjacent to that marked left
boundary. Each simulated step: read the mirrored work symbol and the input symbol
under the simulated head (the input head moves one cell per simulated move — `x` is
verbatim, no doubling — with the boundary marker moved in lockstep), scan the table
for the record matching (state, input read, work read) — at most the table length,
constant in `t` — and apply it: update the state tape, write/move on the mirrored
tape, emit `M`'s emission verbatim. Forward bound: `C · (t + 1)`. Converse:
`U` emits only what the simulation emits and halts only when the simulation halts,
so any completed output of `U` is an output of `M` on `x`. -/
theorem universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      (∀ output : List Bool,
        (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (c.decode α).toFinTM.ComputesInTime x output t) := by
  sorry

/-- **The relaxed quadratic form, for total functions** [AB09, Theorem 1.9 as proved
in §1.4.1 — labeled per audit finding 4: this is the total-function corollary; the
machine-level, partial-computation statement is `Turing.universal`]: every binary
machine computing a total function `f` within `T` has a code `α` such that the
*same* universal machine computes `f x` from `pairEncode α x` within
`C · (T |x| + 1)²`.

**Proof sketch.** Normal-form the machine with `Turing.FinTM.one_work_tape_binary`
(quadratic, [AB09, Claims 1.5-1.6]), relabel its states with `Turing.exists_codeTM`,
take `α := c.encode` of that coded machine (so `c.decode α` is that machine, by
`MachineCode.decode_encode`), and apply the forward direction of `Turing.universal`;
the constants compose as `C_U · (c₁ · (T n + 1)² + 1) ≤ C · (T n + 1)²`. -/
theorem universal_quadratic (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (M₀ : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ),
      M₀.ComputesFunInTime f T →
      ∃ (α : List Bool) (C : ℕ), ∀ x : List Bool,
        U.ComputesInTime (pairEncode α x) (f x) (C * (T x.length + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := universal c
  refine ⟨U, ?_⟩
  intro M₀ f T hM
  obtain ⟨M₁, c₁, hk, h₁⟩ := FinTM.one_work_tape_binary M₀ f T hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := c.encode N
  obtain ⟨C_U, hCU⟩ := hU α
  refine ⟨α, C_U * (c₁ + 1), fun x => ?_⟩
  have hcoded : (c.decode α).toFinTM.ComputesInTime x (f x)
      (c₁ * (T x.length + 1) ^ 2) := by
    rw [show c.decode α = N from c.toMachineCode.decode_encode N]
    exact (hN x (f x) _).2 (h₁ x)
  apply ((hCU x).1 (f x) _ hcoded).mono
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc C_U * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ C_U * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl C_U) (Nat.add_le_add_left hpow _)
    _ = C_U * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

/-- **The time-bounded universal machine** [AB09, §1.4.1, "Universal TM with time
bound"]: a single machine that, given `⟨⟨⌞t⌟, α⟩, x⟩` (clock and code first, input
last), simulates the machine `α` denotes on `x` for at most `t` steps, reporting
success (`true :: output`) or timeout (`[false]`).

**Proof sketch.** Extend the simulation of `Turing.universal` with a binary
countdown clock on a further work tape, initialized from `⌞t⌟ = Nat.bits t` (parsed
from the doubled-bit region; cost `O(t + 1)`, within budget). Each simulated step
costs an additional `O((Nat.bits t).length + 1)` for the decrement, whence the
quadratic budget; `M`'s emissions are buffered on a work tape rather than emitted
(their total length is at most `t`, by `Turing.MultiTapeTM.output_length_le`).
Halting is checked after each simulated transition, **including the `t`-th**: if the
simulated machine has halted by the time the clock expires — deadline included —
`U` emits `true` and flushes the buffer; otherwise it emits `false`. At `t = 0` no
initialized machine has halted (`Turing.FinTM.not_computesInTime_zero`), and the
timeout branch applies (audit finding 6). The two cases below are exhaustive:
either some output witnesses halting within `t`, or every output fails to. -/
theorem timed_universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output) (C * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false] (C * (t + 1) ^ 2)) := by
  sorry

end Turing
```

## ===== TCSlib/Complexity/Uncomputability/Computable.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Vector
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computable functions

A total string function is *computable* if some finite binary machine computes it,
with no time constraint [AB09, §1.4, p. 20]. This is the notion the uncomputability
results of [AB09, §1.5] refute for `UC` and `HALT`. The machine-level predicate is
`Turing.FinTM.Computes` (in `TCSlib.Complexity.TuringMachine.Finite`); this file
provides the machine-independent class and the bridge back to the time-bounded
notion `Turing.FinTM.ComputesFunInTime`.

## Design and deviations from [AB09]

* Computability is defined for **total** functions `List Bool → List Bool` only, as
  in [AB09]; partial computation is handled at the machine level, by the halting
  relation of a machine (see the two clauses of `Turing.universal`). No time bound,
  and no property of any bound, is part of the definition.
* The name clash with Mathlib's `_root_.Computable` (the `Nat.Partrec`-based notion)
  is deliberate and harmless: ours lives in the `Complexity` namespace, and the
  planned `MathlibBridge` module will relate the two.

## Main definitions

* `Complexity.Computable` — some finite binary machine computes `f`.
  [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.Computes.exists_computesFunInTime` — a machine computing `f` with no
  stated time bound admits *some* time bound, by finiteness of the inputs of each
  length. This is the bridge the diagonalization uses to reach the total-function
  normal-form theorems, which are stated with bounds.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, p. 20; §1.5.)
-/

namespace Turing.FinTM

/-- A machine computing `f` with no stated time bound admits some time bound: there
are only finitely many inputs of each length, so the maximum halting time over them
is a bound. (Anticipated by the phase-3 audit, round 2, Argument F: "take the finite
maximum of those times at each input length".)

**Proof sketch.** By choice pick, for each input `x`, a halting time `t x`
witnessing `h x`. The inputs of length `n` form a finite type (`List.Vector Symbol
n`, whose `Fintype` instance transports from `Fintype (Fin n → Symbol)`), so
`T n := Finset.univ.sup` of `t` over it is well defined, and
`Turing.FinTM.ComputesInTime.mono` lifts each witness to the bound `T x.length`.
No monotonicity, positivity, or constructibility of `T` is claimed — none is needed
downstream. -/
theorem Computes.exists_computesFunInTime {Symbol : Type} [Fintype Symbol]
    {M : FinTM Symbol} {f : List Symbol → List Symbol} (h : M.Computes f) :
    ∃ T : ℕ → ℕ, M.ComputesFunInTime f T := by
  classical
  choose t ht using h
  let T : ℕ → ℕ := fun n =>
    (Finset.univ : Finset (List.Vector Symbol n)).sup fun x => t x.val
  refine ⟨T, fun x => (ht x).mono ?_⟩
  exact Finset.le_sup (f := fun y : List.Vector Symbol x.length => t y.val)
    (Finset.mem_univ (α := List.Vector Symbol x.length) ⟨x, rfl⟩)

end Turing.FinTM

namespace Complexity

open Turing

/-- A total string function is *computable* if some finite binary machine computes
it — halts on every input with the value on the output tape — with no time
constraint. [AB09, §1.4, p. 20] -/
def Computable (f : List Bool → List Bool) : Prop :=
  ∃ M : FinTM Bool, M.Computes f

end Complexity
```

## ===== TCSlib/Complexity/Uncomputability/Diagonalization.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.Uncomputability.Computable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uncomputability by diagonalization

[AB09, §1.5, Theorem 1.10]: the diagonal function `UC` is not computable. This is
the theorem the whole encoding layer (`TCSlib.Complexity.TuringMachine.Encoding`)
has been building toward: it needs machines-as-strings and nothing else — not even
the universal machine.

## Design and deviations from [AB09]

* `UC` is defined relative to an **arbitrary** representation scheme
  `Turing.MachineCode`, and Theorem 1.10 is stated at that generality: the
  diagonalization *chooses* one fixed code — `c.encode` of the hypothetical
  decider's normal form — inside a mathematical contradiction, and no machine ever
  computes `encode` or `decode` (phase-3 audit, round 2, Argument F). Effectivity
  (`Turing.EffectiveMachineCode`) is needed only where a machine must *run* codes:
  the universal machine, and the `HALT` reduction of
  `TCSlib.Complexity.Uncomputability.Halting`.
* Output convention: [AB09] writes `M_α(α) = 1`; in this model that is the completed
  singleton output `[true]`. Accordingly `UC c α = true` covers divergence *and*
  every completed output other than `[true]` — exactly the complement of the book's
  acceptance condition (Argument F's reading).
* [AB09] fixes one standing representation once and for all; here the scheme is a
  parameter, so `UC` is a family of functions and Theorem 1.10 a family of
  theorems, each an instance of the book's.

## Main definitions

* `Complexity.UC` — the diagonal function. [AB09, §1.5]

## Main results

* `Complexity.UC_not_computable` — [AB09, Theorem 1.10].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.5, Theorem 1.10, pp. 21-22.)
-/

namespace Complexity

open Turing

open Classical in
/-- The diagonal function `UC` of a representation scheme [AB09, §1.5]: `UC c α` is
`false` iff the machine `α` denotes *accepts its own representation* — that is,
`(c.decode α).toFinTM` halts on input `α` with completed output `[true]`. On
divergence, and on any completed output other than `[true]`, the value is `true`.
([AB09] writes: `UC(α) = 0` if `M_α(α) = 1`, and `UC(α) = 1` otherwise.) -/
noncomputable def UC (c : MachineCode) (α : List Bool) : Bool :=
  if ∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t then false else true

/-- Unfolding lemma: `UC c α = false` iff the denoted machine accepts its own
representation. -/
theorem UC_eq_false_iff (c : MachineCode) (α : List Bool) :
    UC c α = false ↔ ∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t := by
  unfold UC
  split <;> simp_all

/-- Unfolding lemma: `UC c α = true` iff the denoted machine does not accept its own
representation — it diverges on it, or completes with an output other than
`[true]`. -/
theorem UC_eq_true_iff (c : MachineCode) (α : List Bool) :
    UC c α = true ↔ ¬∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t := by
  unfold UC
  split <;> simp_all

/-- **`UC` is not computable** [AB09, Theorem 1.10] — for every representation
scheme, effective or not.

**Proof sketch** (diagonalization, [AB09, proof of Theorem 1.10]; blueprint:
phase-3 audit round 2, Argument F). Suppose some machine computes
`fun α => [UC c α]`. `Turing.FinTM.Computes.exists_computesFunInTime` supplies a
time bound; `Turing.FinTM.one_work_tape_binary` normal-forms the machine into a
one-work-tape binary machine computing the same function; `Turing.exists_codeTM`
relabels that into a coded machine `N` with the same input-by-input `ComputesInTime`
relation. Set `α₀ := c.encode N`, so `c.decode α₀ = N` by
`Turing.MachineCode.decode_encode`, and `N.toFinTM` halts on `α₀` with completed
output `[UC c α₀]`. If `UC c α₀ = false`, then `Complexity.UC_eq_false_iff` (read
through `decode_encode`) says `N.toFinTM` also halts on `α₀` with `[true]`, and
`Turing.FinTM.ComputesInTime.output_unique` forces `[false] = [true]` — absurd. If
`UC c α₀ = true`, then `N.toFinTM` halts on `α₀` with `[true]`, so
`UC_eq_false_iff` gives `UC c α₀ = false` — absurd. No step computes `encode` or
`decode`: the code `α₀` is chosen inside the contradiction. -/
theorem UC_not_computable (c : MachineCode) : ¬Computable fun α => [UC c α] := by
  rintro ⟨M, hM⟩
  obtain ⟨T, hT⟩ := hM.exists_computesFunInTime
  obtain ⟨M', C, hk, hM'⟩ := FinTM.one_work_tape_binary M _ T hT
  obtain ⟨N, hN⟩ := exists_codeTM M' hk
  let α := c.encode N
  have hrun : (c.decode α).toFinTM.ComputesInTime α [UC c α]
      (C * (T α.length + 1) ^ 2) := by
    rw [show c.decode α = N from c.decode_encode N]
    exact (hN α [UC c α] _).2 (hM' α)
  cases hu : UC c α with
  | false =>
    obtain ⟨t, ht⟩ := (UC_eq_false_iff c α).1 hu
    have hcontra := hrun.output_unique ht
    simp only [hu, List.cons.injEq, Bool.false_eq_true, false_and] at hcontra
  | true =>
    have hfalse : UC c α = false :=
      (UC_eq_false_iff c α).2 ⟨_, by simpa only [hu] using hrun⟩
    simp only [hu, Bool.true_eq_false] at hfalse

end Complexity
```

## ===== TCSlib/Complexity/Uncomputability/Halting.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.Uncomputability.Diagonalization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uncomputability of the halting problem

[AB09, §1.5.1, Theorem 1.11]: `HALT` is not computable — proved, as in the book, by
*reduction*: if `HALT` were computable then so would be `UC`, contradicting
[AB09, Theorem 1.10]. This is the chapter's (and history's) first reduction, and the
first consumer of the universal machine `Turing.universal` and of the guarded
composition combinators of `TCSlib.Complexity.TuringMachine.Composition`.

## Design and deviations from [AB09]

* `HALT` takes the pair `⟨α, x⟩` in exactly the universal machine's input format
  `Turing.pairEncode α x` (code first — the phase-3 layout), so the reduction can
  feed pairs it builds straight into the evaluator without re-encoding.
* [AB09] leaves the pairing convention implicit and does not say what `HALT` does on
  strings that are not pairs (the pairing is not surjective); we **totalize by
  `false`** off the image of `pairEncode` — "does not halt".
  `Turing.pairEncode_injective` makes the value on genuine pairs unambiguous
  (`Complexity.HALT_pairEncode_eq_true_iff`), and the reduction only ever evaluates
  `HALT` on genuine pairs, so the off-image convention is immaterial to
  Theorem 1.11. It is *not* immaterial in general — `HALT c [] = false` is a
  convention-dependent equality — so a downstream client evaluating `HALT` on
  arbitrary strings must keep the convention or prove its inputs are genuine pairs
  (phase-4 audit, finding 6).
* "Halts" is rendered as *has a completed output*: `∃ output t, ComputesInTime`.
  This is equivalent to reaching the halting state (every halted configuration has
  some finite output).
* Theorem 1.11 is stated relative to an **effective** scheme
  (`Turing.EffectiveMachineCode`): the reduction runs the universal evaluator,
  which exists only for effective schemes — in contrast to Theorem 1.10, which
  holds for every `Turing.MachineCode`. The reduction itself is a separate lemma
  (`Complexity.UC_computable_of_HALT_computable`), the book's "if `HALT` were
  computable, `UC` would be".

## Main definitions

* `Complexity.HALT` — the halting function. [AB09, §1.5.1]

## Main results

* `Complexity.UC_computable_of_HALT_computable` — the reduction
  [AB09, proof of Theorem 1.11].
* `Complexity.HALT_not_computable` — [AB09, Theorem 1.11].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.5.1, Theorem 1.11, pp. 22-23.)
-/

namespace Complexity

open Turing

open Classical in
/-- The halting function [AB09, §1.5.1]: `HALT c s = true` iff `s` is a pair
`Turing.pairEncode α x` — the universal machine's input format, code first — such
that the machine `α` denotes halts on `x`, i.e. completes *some* output in *some*
number of steps. Strings not of that form (the pairing is not surjective) map to
`false`. -/
noncomputable def HALT (c : MachineCode) (s : List Bool) : Bool :=
  if ∃ α x : List Bool, s = pairEncode α x ∧
      ∃ (output : List Bool) (t : ℕ), (c.decode α).toFinTM.ComputesInTime x output t
  then true else false

/-- Unfolding lemma for `HALT`. -/
theorem HALT_eq_true_iff (c : MachineCode) (s : List Bool) :
    HALT c s = true ↔
      ∃ α x : List Bool, s = pairEncode α x ∧
        ∃ (output : List Bool) (t : ℕ),
          (c.decode α).toFinTM.ComputesInTime x output t := by
  unfold HALT
  split <;> simp_all

/-- On a genuine pair, `HALT` says exactly whether the denoted machine halts:
injectivity of the pairing (`Turing.pairEncode_injective`) identifies the
components. -/
theorem HALT_pairEncode_eq_true_iff (c : MachineCode) (α x : List Bool) :
    HALT c (pairEncode α x) = true ↔
      ∃ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t := by
  rw [HALT_eq_true_iff]
  constructor
  · rintro ⟨α', x', heq, hhalt⟩
    have hp : (α, x) = (α', x') := pairEncode_injective heq
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact hhalt
  · intro hhalt
    exact ⟨α, x, rfl, hhalt⟩

/-- A total machine's completed outputs are exactly its prescribed values, by
existence of a computation and uniqueness of completed output. -/
private theorem halts_iff_eq_of_computes {Symbol : Type} {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x := by
  obtain ⟨t, ht⟩ := hM x
  constructor
  · rintro ⟨s, hs⟩
    exact hs.output_unique ht
  · rintro rfl
    exact ⟨t, ht⟩

/-- **The reduction** [AB09, proof of Theorem 1.11]: if `HALT` were computable,
`UC` would be. Stated for an effective scheme, whose universal evaluator the
reduction runs.

**Proof sketch** (blueprint: phase-3 audit round 2, Argument F; every ingredient
below is a stated result of this development — the fill is assembly, not new
mathematics). Let `D` compute `fun s => [HALT c.toMachineCode s]`, let `U` be the
evaluator of `Turing.universal c`, and write
`p α := HALT c.toMachineCode (pairEncode α α)`.

1. `Turing.computesFunInTime_pairEncode_diag` gives a machine for the diagonal
   pairing `α ↦ pairEncode α α`; `Turing.FinTM.exists_comp_partial` composes it
   with `D`, and determinism (`Turing.FinTM.ComputesInTime.output_unique`)
   collapses the intermediate string, yielding a machine `D'` computing
   `fun α => [p α]`.
2. `Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]` gives the
   postprocessor `w ↦ if w = [true] then [false] else [true]`; two applications of
   `exists_comp_partial` chain the diagonal pairing, `U`, and the postprocessor
   into a machine `Mt` such that `Mt` halts on `α` with `w'` iff `U` halts on
   `pairEncode α α` with some `w` and `w'` is the postprocessed `w`.
3. `Turing.FinTM.computesFunInTime_const [true]` gives `Mf`, computing the constant
   `[true]`; `Turing.FinTM.exists_cond D' Mt Mf p` assembles the branch machine
   `R`.
4. Correctness of `R` at each `α`: if `p α = false`, then by
   `Complexity.HALT_pairEncode_eq_true_iff` the denoted machine never halts on `α`,
   so `Complexity.UC_eq_true_iff` gives `UC = true`, and the selected branch `Mf`
   outputs exactly `[true]`. If `p α = true`, the same lemma yields a completed
   output `w₀` within some `t₀`; the **forward clause** of `Turing.universal` makes
   `U` halt on `pairEncode α α` with `w₀` (the converse clause is not needed — the
   positive `HALT` answer already guarantees halting), so `Mt` halts on `α` with
   the postprocessed value, and `output_unique` identifies the condition
   `w₀ = [true]` with `Complexity.UC_eq_false_iff`'s, making that value
   `[UC c.toMachineCode α]` in both subcases. Hence `R` computes
   `fun α => [UC c.toMachineCode α]`. -/
theorem UC_computable_of_HALT_computable (c : EffectiveMachineCode)
    (h : Computable fun s => [HALT c.toMachineCode s]) :
    Computable fun α => [UC c.toMachineCode α] := by
  classical
  obtain ⟨D, hD⟩ := h
  obtain ⟨U, hU⟩ := universal c
  obtain ⟨P, _, hP⟩ := computesFunInTime_pairEncode_diag
  obtain ⟨Q, _, hQ⟩ := FinTM.computesFunInTime_ifEq [true] [false] [true]
  obtain ⟨Mf, _, hMf⟩ := FinTM.computesFunInTime_const [true]
  let p : List Bool → Bool := fun α => HALT c.toMachineCode (pairEncode α α)
  let r : List Bool → List Bool := fun w => if w = [true] then [false] else [true]
  -- First decide whether the decoded machine halts on its own code.
  obtain ⟨D', hD'⟩ := FinTM.exists_comp_partial P D
  have hDp : D'.Computes fun α => [p α] := by
    intro α
    exact (hD' α [p α]).2 ⟨pairEncode α α, hP.computes α, hD _⟩
  -- The positive branch evaluates the self-pair and postprocesses its output.
  obtain ⟨PU, hPU⟩ := FinTM.exists_comp_partial P U
  obtain ⟨Mt, hMt⟩ := FinTM.exists_comp_partial PU Q
  have hMt' (α z : List Bool) :
      (∃ t, Mt.ComputesInTime α z t) ↔
        ∃ w, (∃ t, U.ComputesInTime (pairEncode α α) w t) ∧ z = r w := by
    simp only [r, hMt, hPU, halts_iff_eq_of_computes hP.computes,
      halts_iff_eq_of_computes hQ.computes, exists_eq_left]
  obtain ⟨R, hR⟩ := FinTM.exists_cond D' Mt Mf p hDp
  refine ⟨R, fun α => (hR α _).2 ?_⟩
  cases hp : p α with
  | false =>
    have huc : UC c.toMachineCode α = true := (UC_eq_true_iff _ _).2 (by
      rintro ⟨t, ht⟩
      have htrue : p α = true :=
        (HALT_pairEncode_eq_true_iff _ _ _).2 ⟨[true], t, ht⟩
      simp only [hp, Bool.false_eq_true] at htrue)
    simpa only [hp, Bool.cond_false, huc] using hMf.computes α
  | true =>
    obtain ⟨w, t, hw⟩ := (HALT_pairEncode_eq_true_iff _ _ _).1 hp
    obtain ⟨C, hC⟩ := hU α
    have huw : ∃ s, U.ComputesInTime (pairEncode α α) w s :=
      ⟨C * (t + 1), (hC α).1 w t hw⟩
    have hr : r w = [UC c.toMachineCode α] := by
      by_cases hwtrue : w = [true]
      · have huc : UC c.toMachineCode α = false :=
          (UC_eq_false_iff _ _).2 ⟨t, hwtrue ▸ hw⟩
        simp only [r, if_pos hwtrue, huc]
      · have huc : UC c.toMachineCode α = true := (UC_eq_true_iff _ _).2 (by
          rintro ⟨t', ht'⟩
          exact hwtrue (hw.output_unique ht'))
        simp only [r, if_neg hwtrue, huc]
    have hMtuc := (hMt' α [UC c.toMachineCode α]).2 ⟨w, huw, hr.symm⟩
    simpa only [hp, Bool.cond_true] using hMtuc

/-- **`HALT` is not computable** [AB09, Theorem 1.11]: immediate from the reduction
`Complexity.UC_computable_of_HALT_computable` and the diagonal theorem
`Complexity.UC_not_computable`. -/
theorem HALT_not_computable (c : EffectiveMachineCode) :
    ¬Computable fun s => [HALT c.toMachineCode s] :=
  fun h => UC_not_computable c.toMachineCode (UC_computable_of_HALT_computable c h)

end Complexity
```

## ===== TCSlib/Complexity/ClassP/Examples.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Example: palindromes are decidable in linear time

The language `PAL` of binary palindromes is decidable in linear time, hence in `P`.
[AB09, Examples 1.1 and 1.4] This is the phase-1 sanity check that the model and class
definitions are *usable*: proving it requires constructing a concrete machine and running
the definitional semantics on it end to end.

## Deviations from [AB09]

* [AB09, Example 1.1] states "within `3n` steps". We state `PAL ∈ DTIME (n + 1)`: the
  `∃ c` in `DTIME` absorbs the leading constant, and the `+ 1` covers the empty input, on
  which every machine needs at least one step to halt (`3 · 0 = 0` is unachievable — the
  book ignores this degenerate case).

## Main definitions

* `Complexity.PAL` — the palindrome language. [AB09, Example 1.1]

## Main results

* `Complexity.PAL_mem_DTIME_linear` — `PAL ∈ DTIME (n + 1)`. [AB09, Example 1.4]
* `Complexity.PAL_mem_P` — `PAL ∈ P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Examples 1.1, 1.4.)
-/

namespace Complexity

open Turing

/-- The language of binary palindromes. [AB09, Example 1.1] -/
def PAL : Language Bool := {x | x.reverse = x}

/-- The audited copy/rewind/test transition table; states are numbered 0, 1, 2.
[AB09, Example 1.1], with the boundary transitions from the phase-1 audit. -/
private def palTM : FinTM Bool where
  k := 1
  State := Fin 3
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
          | none => ⟨.neg, fun _ => (none, .zero), none, some 1⟩
        else if q = 1 then
          match inp with
          | some _ => ⟨.neg, fun _ => (none, .zero), none, some 1⟩
          | none => ⟨.pos, fun _ => (none, .neg), none, some 2⟩
        else
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), some true, none⟩
          | some b =>
            if work 0 = some b then
              ⟨.pos, fun _ => (none, .neg), none, some 2⟩
            else ⟨.zero, fun _ => (none, .zero), some false, none⟩ }

/-- The input word restricted to nonnegative cells below `t`. -/
private def palTape (x : List Bool) (t : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < (t : ℤ) then x[z.toNat]? else none

/-- Canonical live configurations used in the three phase invariants. -/
private def palCfg (x : List Bool) (q : Fin 3) (p : Fin (x.length + 2))
    (w : ℤ) (t : ℕ) : Cfg 1 Bool (Fin 3) x :=
  ⟨some q, p, fun _ => palTape x t, fun _ => w, []⟩

/-- Writing the next input bit extends the copied prefix by one cell. -/
private lemma palTape_write (x : List Bool) (t : ℕ) (ht : t < x.length) :
    Function.update (palTape x t) (t : ℤ) (some x[t]) = palTape x (t + 1) := by
  funext z
  by_cases hz : z = (t : ℤ)
  · subst z
    simp [palTape, ht]
  · rw [Function.update_of_ne hz]
    simp only [palTape]
    by_cases hlt : 0 ≤ z ∧ z < (t : ℤ)
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- A copy transition writes at the old head, then advances both heads. -/
private lemma pal_copy_step (x : List Bool) (t : ℕ) (ht : t < x.length) :
    palTM.tm.step (palCfg x 0 ⟨t + 1, by omega⟩ t t) =
      palCfg x 0 ⟨t + 2, by omega⟩ (t + 1) (t + 1) := by
  have hs : (palCfg x 0 ⟨t + 1, by omega⟩ t t).inputSymbol = some x[t] :=
    inputSymbolInner t (by simp only [palCfg]; omega) ht
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    simp only [palTM, Action.apply, ↓reduceIte]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    simpa [palTM, Action.apply] using palTape_write x t ht
  · funext j
    simp [palTM, Action.apply]
  · simp [palTM, Action.apply]

/-- Copy invariant, including the untouched blank cells outside the prefix.
**Proof sketch.** At time zero the prefix is empty. Each subsequent transition
extends it by the next input bit, using `pal_copy_step`. -/
private lemma pal_copy (x : List Bool) : ∀ t (ht : t ≤ x.length),
    palTM.tm.runFrom (palTM.tm.initCfg x) t =
      palCfg x 0 ⟨t + 1, by omega⟩ t t := by
  intro t
  induction t with
  | zero =>
    intro ht
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp only [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg, Cfg.init, palCfg, palTape]
      rw [if_neg (by omega)]
    · rfl
    · rfl
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact pal_copy_step x t (by omega)

/-- The right blank starts the rewind with the input head at position `n`. -/
private lemma pal_copy_end (x : List Bool) :
    palTM.tm.step (palCfg x 0 ⟨x.length + 1, by omega⟩ x.length x.length) =
      palCfg x 1 ⟨x.length, by omega⟩ x.length x.length := by
  have hs : (palCfg x 0 ⟨x.length + 1, by omega⟩ x.length x.length).inputSymbol =
      none := by simp [Cfg.inputSymbol, palCfg]
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    simp only [palTM, Action.apply, ↓reduceIte]
    rw [moveInputPos_neg_of_ne_left _ (by simp)]
    simp
  · rfl
  · funext j; simp [palTM, Action.apply]
  · rfl

/-- Rewinding does not move or change the copied work tape. -/
private lemma pal_rewind_step (x : List Bool) (i : ℕ) (hi : i < x.length) :
    palTM.tm.step (palCfg x 1 ⟨i + 1, by omega⟩ x.length x.length) =
      palCfg x 1 ⟨i, by omega⟩ x.length x.length := by
  have hs : (palCfg x 1 ⟨i + 1, by omega⟩ x.length x.length).inputSymbol =
      some x[i] := inputSymbolInner i (by simp only [palCfg]; omega) hi
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = i
    rw [moveInputPos_neg_of_ne_left _ (by simp)]
    simp
  · rfl
  · funext j; simp [palTM, Action.apply]
  · rfl

/-- The input head reaches the left blank in exactly its current position's steps.
**Proof sketch.** Induct on the input position; each interior transition decreases
it by one and preserves every other field. -/
private lemma pal_rewind (x : List Bool) : ∀ i (hi : i ≤ x.length),
    palTM.tm.runFrom (palCfg x 1 ⟨i, by omega⟩ x.length x.length) i =
      palCfg x 1 0 x.length x.length := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step, pal_rewind_step x i (by omega)]
    exact ih (by omega)

/-- The left boundary transition aligns the input and reversed work-tape scans,
including work position `-1` on empty input. -/
private lemma pal_test_start (x : List Bool) :
    palTM.tm.step (palCfg x 1 0 x.length x.length) =
      palCfg x 2 1 ((x.length : ℤ) - 1) x.length := by
  have hs : (palCfg x 1 0 x.length x.length).inputSymbol = none := by
    simp [Cfg.inputSymbol, palCfg]
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    change (moveInputPos (0 : Fin (x.length + 2)) .pos).val = (1 : Fin (x.length + 2)).val
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    rfl
  · rfl
  · funext j; simp [palTM, Action.apply, sub_eq_add_neg]
  · rfl

/-- In the comparison phase, the work read is the corresponding bit of `reverse`. -/
private lemma pal_test_read (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length).workTapeSymbols 0 =
      some (x.reverse[i]'(by simpa using hi)) := by
  have hz : (x.length : ℤ) - 1 - i = ((x.length - 1 - i : ℕ) : ℤ) := by omega
  simp only [palCfg, Cfg.workTapeSymbols, palTape, hz, Int.toNat_natCast]
  rw [if_pos (by omega), List.getElem?_eq_getElem (by omega), List.getElem_reverse]

/-- A matched pair advances the opposing comparison heads. -/
private lemma pal_test_step (x : List Bool) (i : ℕ) (hi : i < x.length)
    (heq : x.reverse[i]'(by simpa using hi) = x[i]) :
    palTM.tm.step (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length) =
      palCfg x 2 ⟨i + 2, by omega⟩ ((x.length : ℤ) - 1 - (i + 1)) x.length := by
  have hs : (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length).inputSymbol =
      some x[i] := inputSymbolInner i (by simp only [palCfg]; omega) hi
  have hw := pal_test_read x i hi
  rw [heq] at hw
  unfold MultiTapeTM.step
  change (palTM.tm.tr (2 : Fin 3) _ _).apply _ = _
  rw [hs]
  simp only [palTM, show (2 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, hw]
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 2
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · rfl
  · funext j
    simp only [Action.apply, palCfg, SignType.neg_eq_neg_one, SignType.coe_neg_one]
    omega
  · rfl

/-- All opposing pairs at or after position `i` agree. -/
private def palMatches (x : List Bool) (i : ℕ) : Prop :=
  ∀ j (hj : j < x.length), i ≤ j → x.reverse[j]'(by simpa using hj) = x[j]

/-- After a matching comparison, the remaining condition starts at the next bit. -/
private lemma palMatches_succ (x : List Bool) (i : ℕ) (hi : i < x.length)
    (heq : x.reverse[i]'(by simpa using hi) = x[i]) :
    palMatches x i ↔ palMatches x (i + 1) := by
  constructor
  · intro h j hj hij; exact h j hj (by omega)
  · intro h j hj hij
    by_cases hji : j = i
    · subst j; exact heq
    · exact h j hj (by omega)

open Classical in
/-- The comparison phase decides the remaining pointwise equalities in at most
one step per pair plus the final blank transition.
**Proof sketch.** Induct on the number of pairs left. A matching pair reduces to
the induction hypothesis. A mismatch emits false immediately, and halting absorbs
the unused steps. At zero remaining pairs, the right blank emits true. -/
private lemma pal_test (x : List Bool) : ∀ r i (hi : i ≤ x.length)
    (hr : x.length = i + r),
    let c := palTM.tm.runFrom
      (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length) (r + 1)
    c.state = none ∧ c.output = [if palMatches x i then true else false] := by
  intro r
  induction r with
  | zero =>
    intro i hi hr
    have he : i = x.length := by omega
    subst i
    have hm : palMatches x x.length := by intro j hj hij; omega
    have hs : (palCfg x 2 ⟨x.length + 1, by omega⟩
        ((x.length : ℤ) - 1 - x.length) x.length).inputSymbol = none := by
      simp [Cfg.inputSymbol, palCfg]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((palTM.tm.tr (2 : Fin 3) _ _).apply _).state = none ∧ _
    rw [hs]
    simp [palTM, Action.apply, palCfg, hm]
  | succ r ih =>
    intro i hi hr
    have hi' : i < x.length := by omega
    by_cases heq : x.reverse[i]'(by simpa using hi') = x[i]
    · simp only [MultiTapeTM.runFrom_succ_eq_step,
        pal_test_step x i hi' heq]
      simpa only [palMatches_succ x i hi' heq] using
        ih (i + 1) (by omega) (by omega)
    · have hs : (palCfg x 2 ⟨i + 1, by omega⟩
          ((x.length : ℤ) - 1 - i) x.length).inputSymbol = some x[i] :=
        inputSymbolInner i (by simp only [palCfg]; omega) hi'
      have hw := pal_test_read x i hi'
      have hm : ¬palMatches x i := fun h => heq (h i hi' (le_refl _))
      let c := palTM.tm.step
        (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length)
      have hc : c.state = none ∧ c.output = [false] := by
        dsimp only [c]
        unfold MultiTapeTM.step
        change ((palTM.tm.tr (2 : Fin 3) _ _).apply _).state = none ∧ _
        rw [hs]
        simp only [palTM, show (2 : Fin 3) ≠ 0 from by decide,
          show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, hw]
        rw [if_neg (by simpa only [Option.some.injEq] using heq)]
        exact ⟨rfl, rfl⟩
      change (palTM.tm.runFrom c (r + 1)).state = none ∧
        (palTM.tm.runFrom c (r + 1)).output = [if palMatches x i then true else false]
      rw [MultiTapeTM.runFrom_of_halt _ hc.1]
      simpa only [if_neg hm] using hc

/-- Palindromes are decidable in linear time. [AB09, Examples 1.1 and 1.4]

**Proof sketch.** Adapt the machine of [AB09, Example 1.1] to our model (bidirectional
tapes, no start symbol, blank = `none`): a one-work-tape machine with states
`{copy, rewind, test}`.

1. *Copy* (`n + 1` steps): move the input head and the work head right in unison, copying
   each input symbol to the work tape, until the input head reads blank (one cell past the
   input). The work head now sits one cell right of the copied string.
2. *Rewind* (`n + 1` steps): move the input head left back to the left boundary cell while
   the work head stays put; then step the work head one cell left onto the last symbol.
3. *Test* (`n + 1` steps): move the input head right and the work head left in unison,
   comparing the input symbol against the work symbol. On a mismatch, emit `false` and
   halt. When the input head reads blank again (all positions matched), emit `true` and
   halt.

Each phase takes at most `n + 1` steps, so some constant `c` (e.g. `c = 4`) gives
`c · (n + 1) ≥ 3n + 3` total steps, witnessing the `DTIME (n + 1)` bound. The formal
proof constructs the machine's transition function explicitly and establishes the
three-phase invariants by induction on the step count. -/
theorem PAL_mem_DTIME_linear : PAL ∈ DTIME fun n => n + 1 := by
  classical
  refine ⟨3, palTM, fun x => ?_⟩
  have hstart : palTM.tm.runFrom (palTM.tm.initCfg x)
      (x.length + 1 + x.length + 1) =
      palCfg x 2 1 ((x.length : ℤ) - 1) x.length := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step', pal_copy x x.length (le_refl _),
      pal_copy_end, pal_rewind x x.length (le_refl _), pal_test_start]
  have hm : palMatches x 0 ↔ x ∈ PAL := by
    constructor
    · intro h
      apply List.ext_getElem List.length_reverse
      intro j hj hj'
      exact h j hj' (Nat.zero_le _)
    · intro h j hj _
      change x.reverse = x at h
      simp only [h]
  have htest := pal_test x x.length 0 (Nat.zero_le _) (by omega)
  have ht : 3 * (x.length + 1) = (x.length + 1 + x.length + 1) + (x.length + 1) := by
    omega
  refine ⟨_, ?_, ?_, rfl⟩
  · dsimp only
    rw [ht, MultiTapeTM.runFrom_add, hstart]
    simpa only [Nat.cast_zero, sub_zero] using htest.1
  · dsimp only
    rw [ht, MultiTapeTM.runFrom_add, hstart]
    simpa only [Nat.cast_zero, sub_zero, MultiTapeTM.indicator, hm] using htest.2

/-- Palindromes are decidable in polynomial time. -/
theorem PAL_mem_P : PAL ∈ P :=
  mem_P_of_dtime_le PAL_mem_DTIME_linear 1 1 fun n => by simp [pow_one]

end Complexity
```

## ===== TCSlib/Complexity/ClassP/TimeConstructible.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time-constructible functions

A function `T : ℕ → ℕ` is *time constructible* if `T n ≥ n` and some machine computes,
on every input `x`, the binary representation of `T |x|` within at most
`c · (T |x| + 1)` steps for a positive constant `c`. [AB09, §1.3, with the audit-mandated
budget repair below.] Time constructibility rules out pathological time bounds. It is
needed when a machine must *generate* a step budget from its input length, as in the
hierarchy theorems; note that the timed universal machine of [AB09, p. 21] receives its
budget as an explicit extra input and needs no constructibility hypothesis.

## Design and deviations from [AB09]

* Binary representation is `Nat.bits` (least-significant-bit first, with no redundant
  most-significant zeros; `Nat.bits 0 = []`), where [AB09] writes `⌞T(|x|)⌟` without
  fixing endianness. Nothing in Chapter 1 depends on the choice.
* **Deviation (audit-mandated).** [AB09] demands the computation run within exactly
  `T n` steps and then asserts that `n`, `n log n`, `n²`, `2ⁿ` are time constructible.
  The phase-1 external audit (`audits/phase1-findings.md`, finding 1, adversarial cases
  5-6) *proved the literal reading false in this model*: under the exact bound, the
  identity function — [AB09]'s own first example — is not time constructible (on the
  budget `T n = n`, the first transition on `[false]` and `[false, false]` is the same
  function call, and the length-1 budget forces it to halt with output `[true]`, which
  absorption then freezes at length 2), and even `T n = n + 1` fails by an append-only
  prefix argument. We therefore allow a positive constant factor on `T n + 1`, which
  suffices for every downstream use and restores the book's examples *after small-input
  normalization*: the literal `n · ⌈log₂ n⌉`, for instance, still violates `T n ≥ n` at
  `n = 1`, so such examples are stated with a `max`-with-`n` or `+ 1` normalization.
  Exact constants in downstream results must be derived from this form, not inherited
  from the strict reading.

## Main definitions

* `Complexity.TimeConstructible` — [AB09, §1.3], with the constant-slack repair above.

## Main results

* `Complexity.timeConstructible_id` — the identity function is time constructible,
  restoring [AB09]'s example under the repaired definition.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, "Time-constructible functions".)
-/

namespace Complexity

open Turing

/-- `T` is time constructible: `T n ≥ n`, and some finite binary machine computes
`x ↦ ⌞T |x|⌟` (binary via `Nat.bits`) within `c · (T |x| + 1)` steps for a positive
constant `c`. [AB09, §1.3], with the constant-slack deviation documented in the module
docstring (the literal exact-`T n` bound is refuted in this model by
`audits/phase1-findings.md`, finding 1). -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
    M.ComputesInTime x (T x.length).bits (c * (T x.length + 1))

/-- Increment a little-endian binary word, extending it on overflow. -/
private def counterInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: counterInc bs

/-- The number of initial true bits cleared by an increment. -/
private def counterCarry : List Bool → ℕ
  | true :: bs => counterCarry bs + 1
  | _ => 0

/-- Each cleared true bit decreases the potential by one; the final write adds one.
This is the local accounting identity behind the amortized bound. -/
private lemma counterInc_potential (bs : List Bool) :
    (counterInc bs).count true + counterCarry bs = bs.count true + 1 := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b with
    | false => simp [counterInc, counterCarry]
    | true => simp [counterInc, counterCarry]; omega

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma counterInc_bits (n : ℕ) : counterInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [counterInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [counterInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma counterInc_length (bs : List Bool) :
    (counterInc bs).length ≤ bs.length + 1 ∧
      counterCarry bs ≤ (counterInc bs).length := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b <;> simp only [counterInc, counterCarry, List.length_cons] <;> omega

/-- The final emission uses at most `n` symbol-writing steps. -/
private lemma counter_bits_length (n : ℕ) : n.bits.length ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← counterInc_bits]
    have := (counterInc_length n.bits).1
    omega

/-- One carry transition, with the first transition also advancing the input. -/
private def counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- The audit's four-state counter: count = 0, carry = 1, rewind = 2, emit = 3.
[AB09, §1.3 examples], implemented by the phase-1 reaudit's transition table. -/
private def counterTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), none, some 3⟩
          | some _ => counterBump .pos (work 0)
        else if q = 1 then counterBump .zero (work 0)
        else if q = 2 then
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .pos), none, some 0⟩
          | some _ => ⟨.zero, fun _ => (none, .neg), none, some 2⟩
        else
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .zero), none, none⟩
          | some b => ⟨.zero, fun _ => (none, .pos), some b, some 3⟩ }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def counterTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, count, and emission invariants. -/
private def counterCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => counterTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma counterTape_read (pre bs : List Bool) :
    counterTape (pre ++ bs) pre.length = bs.head? := by
  simp only [counterTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma counterTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (counterTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      counterTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [counterTape_read]
  · rw [Function.update_of_ne hz]
    unfold counterTape
    by_cases hn : z < 0
    · simp only [if_pos hn]
    · simp only [if_neg hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_cons, if_neg (by omega), List.getElem?_tail]
        congr 1
        omega

/-- One carry transition updates exactly the currently scanned cell. -/
private lemma counter_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    counterTM.tm.step (counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (counterTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .zero (counterTape (pre ++ bs) pre.length)).apply _ = _
  rw [counterTape_read]
  unfold counterBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact counterTape_write pre bs _
    · funext j; simp [Action.apply, counterCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma counter_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    counterTM.tm.runFrom (counterCfg x 1 p pre.length (pre ++ bs) [])
        (counterCarry bs + 1) =
      counterCfg x 2 p ((pre.length : ℤ) + counterCarry bs - 1)
        (pre ++ counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, counter_carry_step]
    simp [counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, counter_carry_step]
      simp [counterInc]
    | true =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step, counter_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [counterInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the count state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma counter_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    counterTM.tm.runFrom (counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, counterTM, counterCfg, Cfg.workTapeSymbols,
        counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : counterTM.tm.step (counterCfg x 2 p (j : ℤ) bs []) =
        counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (counterTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [counterTM, show (2 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, counterCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The first carry transition also consumes exactly one input symbol. -/
private lemma counter_start (x : List Bool) (i : ℕ) (hi : i < x.length) (bs : List Bool) :
    counterTM.tm.step (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      counterTM.tm.step (counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (counterTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (counterTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .pos (counterTape bs 0)).apply _ =
    (counterBump .zero (counterTape bs 0)).apply _
  unfold counterBump
  by_cases h : counterTape bs 0 = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val =
        (moveInputPos (⟨i + 2, by omega⟩ : Fin (x.length + 2)) 0).val
      rw [moveInputPos_zero, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rfl
    · rfl
    · rfl

/-- One complete increment takes twice the carry length plus two transitions.
**Proof sketch.** The count transition is the first carry transition, with the
input advanced once. The carry uses `r + 1` steps and leaves the head at `r - 1`;
the rewind uses another `r + 1` steps and leaves the incremented word intact. -/
private lemma counter_increment (x : List Bool) (i : ℕ) (hi : i < x.length)
    (bs : List Bool) :
    counterTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * counterCarry bs + 2) =
      counterCfg x 0 ⟨i + 2, by omega⟩ 0 (counterInc bs) [] := by
  have hc : counterTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
      (counterCarry bs + 1) =
      counterCfg x 2 ⟨i + 2, by omega⟩ ((counterCarry bs : ℤ) - 1) (counterInc bs) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step, counter_start x i hi,
      ← MultiTapeTM.runFrom_succ_eq_step]
    simpa only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] using
      counter_carry x ⟨i + 2, by omega⟩ bs []
  rw [show 2 * counterCarry bs + 2 = (counterCarry bs + 1) + (counterCarry bs + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact counter_rewind x ⟨i + 2, by omega⟩ (counterInc bs) (counterCarry bs)
    (counterInc_length bs).2

/-- The counting invariant carries a nonnegative potential of twice the popcount.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions. -/
private lemma counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      counterTM.tm.runFrom (counterTM.tm.initCfg x) t =
        counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_⟩
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp [MultiTapeTM.initCfg, counterCfg, counterTape]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc⟩ := ih (by omega)
    refine ⟨t + 2 * counterCarry i.bits + 2, ?_, ?_⟩
    · have hp := counterInc_potential i.bits
      rw [counterInc_bits] at hp
      omega
    · rw [show t + 2 * counterCarry i.bits + 2 = t + (2 * counterCarry i.bits + 2) by omega,
        MultiTapeTM.runFrom_add, hc, counter_increment x i (by omega), counterInc_bits]

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    counterTM.tm.runFrom (counterCfg x 3 p 0 bs []) i =
      counterCfg x 3 p i bs (bs.take i) := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (counterCfg x 3 p i bs (bs.take i)).workTapeSymbols 0 = some bs[i] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(i : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    unfold MultiTapeTM.step
    change (counterTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [counterTM, show (3 : Fin 4) ≠ 0 from by decide,
      show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      ↓reduceIte, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · rfl
    · funext j; simp [Action.apply, counterCfg]
    · simp only [Action.apply, counterCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- At the first blank after the stored word, emission halts without extra output. -/
private lemma counter_emit (x : List Bool) (p : Fin (x.length + 2)) (bs : List Bool) :
    let c := counterTM.tm.runFrom (counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((counterTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [counterTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, counterCfg]

/-- The identity function is time constructible. [AB09, §1.3 examples]

**Proof sketch.** A one-work-tape machine maintains a little-endian binary counter on
its work tape while scanning the input left to right: for each input symbol it
increments the counter (walking right over `true` cells turning them `false` until the
first `false`/blank cell, which becomes `true`, then returning to cell 0). Incrementing
`n` times costs amortized `O(1)` per increment, `O(n)` in total. When the input head
reads the blank past the input, the machine walks the counter left to right emitting
each bit to the output tape (`O(log n)` steps) and halts. The total is at most
`c · (n + 1)` steps for an absolute constant `c`, and the emitted string is `n.bits`
(for `n = 0` the counter region is empty and nothing is emitted, matching
`Nat.bits 0 = []`). The formal proof uses twice the number of true counter bits as
potential: elapsed time plus potential is at most `4n` after `n` increments.
Entering emission and its final halting transition add two steps; the output length
is at most `n`, so `c = 5` suffices. -/
theorem timeConstructible_id : TimeConstructible id := by
  refine ⟨fun n => le_refl n, 5, by decide, counterTM, fun x => ?_⟩
  obtain ⟨t, ht, hc⟩ := counter_count x x.length (le_refl _)
  have hs : counterTM.tm.step
      (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    have hin : (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, counterCfg]
    unfold MultiTapeTM.step
    change (counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [counterTM, Action.apply, counterCfg]
  have hstart : counterTM.tm.runFrom (counterTM.tm.initCfg x) (t + 1) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  have he := counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  have hbase : counterTM.ComputesInTime x x.length.bits
      ((t + 1) + (x.length.bits.length + 1)) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.1
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.2
  apply hbase.mono
  have hl := counter_bits_length x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

end Complexity
```

## ===== TCSlib/Complexity/TuringMachine/Finite.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Basic
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite Turing machines

The raw model `Turing.MultiTapeTM k Symbol State` deliberately does not require `Symbol` or
`State` to be finite: semantics, simulations, and resource counting do not need it, and
compound state types arise freely in constructions. Finiteness is nevertheless
mathematically essential for complexity theory — with infinitely many states a machine can
memorize its whole input in the state and decide any language in linear time, and an
infinite transition table has no string encoding.

This file provides the bundled layer `Turing.FinTM`: a machine together with `Fintype` and
`DecidableEq` instances for its state type. All headline definitions of the Chapter 1
development (`DTIME`, `P`, machine encodings, the universal machine) are stated exclusively
over `FinTM`, so the finiteness hypothesis can never be dropped by accident. The instances
are carried as *data* (not `Finite` propositions) because the machine-encoding function
`⌞M⌟` must enumerate the transition table.

The alphabet parameter `Symbol` stays explicit and unbundled: the Chapter 1 headline
definitions fix `Symbol := Bool` (see `TCSlib.Complexity.ClassP.DTIME`), and results that
need a finite alphabet for a general `Symbol` take `[Fintype Symbol]` hypotheses at use
sites.

## Main definitions

* `Turing.FinTM Symbol` — a multi-tape TM over alphabet `Option Symbol` with a bundled
  finite state type. [AB09, §1.2]
* `Turing.FinTM.ComputesInTime` — the machine halts on `input` within `t` steps with
  `output` on the output tape (time-only variant of
  `Turing.MultiTapeTM.ComputesInTimeAndSpace`). [AB09, Definition 1.3]
* `Turing.FinTM.ComputesFunInTime` — the machine computes `f` in time `T`.
  [AB09, Definition 1.3]
* `Turing.FinTM.Computes` — the machine computes `f` with no time constraint; the
  notion of computability underlying the uncomputability results. [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.ComputesInTime.mono` — halting is absorbing, so the time bound can be
  weakened.
* `Turing.FinTM.ComputesInTime.output_unique` — determinism: a machine has at most one
  completed output on a given input.
* `Turing.FinTM.not_computesInTime_zero` — no machine computes anything in zero steps
  (the initial state is not the halting state).
* `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.output_prefix` — raw-layer
  output lemmas (at most one symbol is emitted per step, and output only grows), stated
  here rather than in the vendored `Deterministic.lean` to keep the vendored files
  unmodified.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.3.)
-/

namespace Turing

/-!
### Raw-layer output lemmas

Additions on top of the vendored files (kept here so the vendored `Deterministic.lean`
stays byte-comparable with upstream).
-/

namespace MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The output of an initialized run after `t` steps has length at most `t`: each step
appends at most one symbol.

**Proof sketch.** Induction on `t` with `Turing.MultiTapeTM.runFrom_succ_eq_step'` and
`Turing.MultiTapeTM.step_output` (`Option.toList` has length at most one); the initial
output is `[]`. -/
theorem output_length_le (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    ((tm.runFrom (tm.initCfg input) t).output).length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    have hone : (tm.outputSymbol (tm.runFrom (tm.initCfg input) t)).toList.length ≤ 1 := by
      cases tm.outputSymbol (tm.runFrom (tm.initCfg input) t) <;> simp
    simp only [List.length_append]
    omega

/-- Output is monotone along a run: the output at an earlier time is a prefix of the
output at any later time.

**Proof sketch.** It suffices to treat one step (`Turing.MultiTapeTM.step_output`: a
step appends), then induct on the difference using
`Turing.MultiTapeTM.runFrom_add` and transitivity of `List.IsPrefix`. -/
theorem output_prefix (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t t' : ℕ} (h : t ≤ t') :
    (tm.runFrom cfg t).output <+: (tm.runFrom cfg t').output := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [MultiTapeTM.runFrom_add]
  generalize tm.runFrom cfg t = c
  induction d with
  | zero => simp
  | succ d ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    exact ih.trans (List.prefix_append _ _)

end MultiTapeTM

/-- A multi-tape Turing machine over the alphabet `Option Symbol` bundled with a finite
state type. This is the machine of [AB09, §1.2] up to the declared model variations
(append-only output tape, start-marker-free initialization — see the deviations list in
`TCSlib.Complexity.ClassP.DTIME`): the raw `MultiTapeTM` is internal plumbing, and
every headline complexity-theoretic definition is stated over `FinTM`.

The instances are data (`Fintype`/`DecidableEq`, not `Finite`) because encoding a machine
as a string requires enumerating its transition table. -/
structure FinTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible, needed to tabulate the transition function -/
  [decEqState : DecidableEq State]
  /-- the underlying machine -/
  tm : MultiTapeTM k Symbol State

namespace FinTM

attribute [instance] FinTM.fintypeState FinTM.decEqState

variable {Symbol : Type}

/-- The machine `M` halts on `input` within `t` steps with `output` written on its output
tape. Time-only variant of `Turing.MultiTapeTM.ComputesInTimeAndSpace` (the space used is
existentially discarded). [AB09, Definition 1.3] -/
def ComputesInTime (M : FinTM Symbol) (input output : List Symbol) (t : ℕ) : Prop :=
  ∃ s, M.tm.ComputesInTimeAndSpace input output t s

/-- The machine `M` computes the string function `f`, halting within `T |input|` steps on
every input. [AB09, Definition 1.3: "M computes f in T(n)-time"] -/
def ComputesFunInTime (M : FinTM Symbol) (f : List Symbol → List Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ input : List Symbol, M.ComputesInTime input (f input) (T input.length)

/-- The machine `M`, over alphabet `Γ`, computes the string function `f` on `α`-strings
*via* the symbol embedding `e : α ↪ Γ`: on every input `x.map e` it halts within
`T |x|` steps with `(f x).map e` on its output tape. This is how a machine over a
larger alphabet is said to compute a function on a smaller one; it is the interface of
the alphabet-robustness results [AB09, §1.3.1]. -/
def ComputesFunInTimeVia {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) : Prop :=
  ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length)

/-- The machine `M` *computes* the string function `f`, with no time constraint: on
every input it eventually halts with `f input` on the output tape. This is the notion
of computability underlying the uncomputability results [AB09, §1.4, p. 20; §1.5];
`Turing.FinTM.ComputesFunInTime` is the time-bounded refinement, and the two are
related by `Turing.FinTM.ComputesFunInTime.computes` (below) and
`Turing.FinTM.Computes.exists_computesFunInTime`
(in `TCSlib.Complexity.Uncomputability.Computable`). -/
def Computes (M : FinTM Symbol) (f : List Symbol → List Symbol) : Prop :=
  ∀ input : List Symbol, ∃ t, M.ComputesInTime input (f input) t

/-- Halting is absorbing, so a time bound can be weakened: if `M` produces `output`
within `t` steps it also does so within any `t' ≥ t` steps.

**Proof sketch.** By `Turing.MultiTapeTM.runFrom_add` the run to step `t'` factors through
step `t`; the state there is `none`, so `Turing.MultiTapeTM.runFrom_of_halt` shows the
configuration no longer changes, and in particular state and output at step `t'` agree with
step `t`. The space used up to step `t'` exists (it is whatever `spaceUsed` evaluates to),
which discharges the existential. -/
theorem ComputesInTime.mono {M : FinTM Symbol} {input output : List Symbol} {t t' : ℕ}
    (h : M.ComputesInTime input output t) (hle : t ≤ t') :
    M.ComputesInTime input output t' := by
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h ⊢
  obtain ⟨s, hhalt, hout, -⟩ := h
  have hrun : M.tm.runFrom (M.tm.initCfg input) t' = M.tm.runFrom (M.tm.initCfg input) t := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  exact ⟨_, by rw [hrun]; exact hhalt, by rw [hrun]; exact hout, rfl⟩

/-- No machine computes anything in zero steps: the initial configuration is in the
initial state, which is not the halting state. In particular a time budget of `0`
(e.g. from a vanishing time bound) is never satisfiable. -/
theorem not_computesInTime_zero (M : FinTM Symbol) (input output : List Symbol) :
    ¬M.ComputesInTime input output 0 := by
  rintro ⟨s, hhalt, -⟩
  simp [MultiTapeTM.runFrom_zero] at hhalt

/-- Determinism of completed outputs: a machine has at most one completed output on a
given input — if `M` halts on `input` with `w` within `t` steps and with `w'` within
`t'` steps, then `w = w'`. Together with `Turing.FinTM.ComputesInTime.mono` this
makes the halting relation of a machine a partial function.

**Proof.** Absorb both computations to time `max t t'`
(`Turing.FinTM.ComputesInTime.mono`); both then name the output of one and the same
run. -/
theorem ComputesInTime.output_unique {M : FinTM Symbol} {input w w' : List Symbol}
    {t t' : ℕ} (h : M.ComputesInTime input w t) (h' : M.ComputesInTime input w' t') :
    w = w' := by
  have h₁ := h.mono (Nat.le_max_left t t')
  have h₂ := h'.mono (Nat.le_max_right t t')
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h₁ h₂
  obtain ⟨s, -, hout, -⟩ := h₁
  obtain ⟨s', -, hout', -⟩ := h₂
  rw [← hout, ← hout']

/-- A time-bounded computation is in particular a computation. -/
theorem ComputesFunInTime.computes {M : FinTM Symbol} {f : List Symbol → List Symbol}
    {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) : M.Computes f :=
  fun input => ⟨T input.length, h input⟩

end FinTM

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Configuration.lean =====

```lean
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to its location at our mathlib pin,
  `Mathlib.Data.Sign.Defs`; dropped the cslib-internal `Cslib.Init` import;
* added the repository-standard `set_option` header.
The mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Sign.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to one and the space measure
read off a list of them.

## Design

Nothing here mentions a machine. A step is described in two parts: an `Action`, recording
which way the input head moves, what is written and where the work heads move, which symbol is
emitted and which state follows; and `Action.apply`, which carries it out on a
configuration.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in.

## Main definitions

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
* `spaceUsedOfCfgs`: work tape cells touched along a list of configurations

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape Turing machine.)
* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
  (§2.3, §2.5: the machine model and the space measure.)
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations of a machine without work tapes are equal if their states, input head
positions and outputs are equal. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  -- ported proof: `dite_eq_right` does not exist at our mathlib pin
  apply Fin.ext
  simp only [moveInputPos, SignType.coe_one]
  split <;> simp <;> omega

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg_one]
  split <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.pos_eq_one, SignType.coe_one]
  split <;> simp <;> omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by
    -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
    have h0 : (cfg.inputPos : ℕ) ≠ 0 := fun hv => h₁ (Fin.val_eq_zero_iff.mp hv)
    have hlt := cfg.inputPos.isLt
    omega)

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
  have h0 : ¬cfg.inputPos = 0 := fun hz => by
    rw [hz] at h₁
    simp at h₁
    omega
  have hL : ¬(cfg.inputPos : ℕ) = input.length + 1 := by omega
  simp only [Cfg.inputSymbol, dif_neg h0, dif_neg hL]
  simp only [show (cfg.inputPos : ℕ) - 1 = p from by omega]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simp]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

/-- The work tape cells visited by the head of tape `i` along a list of configurations. -/
def visitedOfCfgs (cfgs : List (Cfg k Symbol State input)) (i : Fin k) : Finset ℤ :=
  (cfgs.map (·.workTapePos i)).toFinset

/-- The number of work tape cells touched by the heads along a list of configurations. -/
def spaceUsedOfCfgs (cfgs : List (Cfg k Symbol State input)) : ℕ :=
  ∑ i, (visitedOfCfgs cfgs i).card

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Deterministic.lean =====

```lean
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to `Mathlib.Data.Sign.Defs` (its location at our mathlib
  pin); dropped the cslib-internal `Cslib.Init` import; added
  `Mathlib.Logic.Embedding.Basic` explicitly (upstream receives it transitively);
* dropped the relational semantics (`TransitionRelation`,
  `relatesInSteps_iff_runFrom_eq`) because it depends on the cslib-internal
  `Cslib.Foundations.Data.RelatesInSteps`; the iterated-step semantics `runFrom` is
  self-contained and suffices for the Chapter 1 development. Re-add it (or migrate to
  upstream cslib) when the step-indexed relational view is needed, e.g. for
  nondeterministic machines;
* added the repository-standard `set_option` header.
The remaining mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Embedding.Basic
import TCSlib.Complexity.TuringMachine.Configuration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AB09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Pap94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AB09], Claim 1.8). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Main definitions

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step,
    our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a machine computes a function between specified encodings,
    respecting time and space bounds on each actual input.
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

## References

* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013.
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM

variable {input : List Symbol} {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `TCSlib.Complexity.TuringMachine.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} :
    tm.runFrom cfg 0 = cfg := by
  simp [runFrom]

lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  simp [runFrom, Function.iterate_succ_apply]

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp [runFrom, Function.iterate_succ_apply']

/-- Running `a + b` steps equals running `b` steps from the configuration reached after `a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  unfold runFrom
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- If a function `f` that maps the configurations of one TM to those of another one commutes with
their `step` function, then it also commutes with their `runFrom` function. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input input' : List Symbol}
    {tm : MultiTapeTM k Symbol State} {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- Running from a halting configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.runFrom cfg t').workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := by
  unfold spaceUsed spaceUsedByTape spaceUsedOfCfgs
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card ?_
  ext z
  simp [visitedByTapeHead, visitedOfCfgs]

end Space

open Cfg

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- The output does not change after the machine has halted. -/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses exactly `s` space.
Note that this does not require the alphabet or state set to be finite. -/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧
  (tm.runFrom (tm.initCfg input) t).output = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A machine computes `f` between the supplied encodings, with bounds depending on the input.
The machine's alphabet and state type need not be finite. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ComputesInTimeAndSpace tm (encIn a) (encOut (f a)) t' s'

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunInTimeAndSpace tm encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunInTimeAndSpace tm encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

open Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
def haltsAtStep (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) : Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol State}
    {input : List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.runFrom (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.runFrom (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, runFrom]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, runFrom_add, tm.runFrom_of_halt _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.runFrom_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.runFrom_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Oracle.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle Turing machines

An oracle Turing machine [AB09, §3.4, Definition 3.4; pulled forward to Chapter 1 to
validate the model architecture] is a multi-tape machine with one additional designated
*query tape* and three designated states `qQuery`, `qYes`, `qNo`. Whenever the machine
enters `qQuery`, the string currently written on the query tape is submitted to the oracle
`O`: in a single step the machine moves to `qYes` if the query is in `O` and to `qNo`
otherwise, with all tapes and heads unchanged.

## Design

This file is the architectural test of the `Action`/`Action.apply` split: an oracle machine
reuses the configurations `Turing.Cfg (k + 1)` (the query tape is the extra work tape, at
index `Fin.last k`) and the action application of the plain model, and differs *only* in how
the next action is chosen — the step function is parametrized by the oracle
`O : Language Symbol`. Time and space measures therefore transfer unchanged.

Definitional choices worth auditing:

* **The query string** (`OracleTM.queryString`) is read from cell `0` of the query tape
  rightward up to (excluding) the first blank cell; if the whole nonnegative half-tape is
  blank-free (possible for an arbitrary configuration, though not for one reachable from an
  initial configuration), the query is defined to be `[]`. [AB09] leaves the extraction
  convention implicit; this is one concrete faithful reading.
* **The answer step** changes only the state; heads and tapes stay put. Some texts
  instead erase the query tape on each answer. The two conventions are equivalent up to
  *polynomial* overhead, but **not** constant overhead: computing the parity of `n`
  distinct length-`n` queries takes `O(n)` steps with a persistent tape and `Ω(n²)`
  steps with auto-erasure (`audits/phase1-findings.md`, finding 3, case 12).
  Consequently, exact `DTIME`-level bounds must never be transferred across this
  convention; class-level results (`Pᴼ` etc.) are unaffected.
* `qYes`/`qNo` are ordinary states from the machine's point of view (its transition
  function handles them); only `qQuery` triggers special behavior. The machine may query
  repeatedly. This reading presumes the three special states are pairwise distinct,
  which the raw structure does not enforce (e.g. with `qYes = qQuery` the machine
  re-queries forever after a positive answer): results at the faithful interface assume
  `OracleTM.WellFormed`. Note that
  `q₀ = qQuery` is legitimate and deliberately allowed (the machine then submits the
  empty query on its first step).

## Main definitions

* `Turing.OracleTM` — the oracle machine. [AB09, Definition 3.4]
* `Turing.OracleTM.WellFormed` — the three special states are pairwise distinct; the
  standing hypothesis of the faithful interface (oracle complexity classes will require
  it).
* `Turing.OracleTM.step`, `Turing.OracleTM.runFrom` — semantics relative to an oracle.
* `Turing.OracleTM.ComputesInTime` — output and time bound relative to an oracle.
* `Turing.Action.extend`, `Turing.Action.mapState`, `Turing.Cfg.embedOracle`,
  `Turing.OracleTM.ofMultiTapeTM` — the embedding of plain machines as oracle machines
  that never query.
* `Turing.OracleTM.plainEmptyOracle` — the converse direction: an oracle machine run
  with the empty oracle, as a plain `k + 1`-tape machine in exact lockstep.

## Main results (sanity checks for the architecture)

* `Turing.OracleTM.step_eq_of_ne_qQuery` — away from `qQuery`, the step does not depend
  on the oracle.
* `Turing.OracleTM.ofMultiTapeTM_wellFormed` — the embedding produces well-formed
  machines.
* `Turing.OracleTM.runFrom_ofMultiTapeTM` — an embedded plain machine runs in lockstep
  with the original, under every oracle.
* `Turing.OracleTM.computesInTime_ofMultiTapeTM` — hence its input/output behavior and
  time bounds are oracle-independent and agree with the plain machine's.
* `Turing.OracleTM.runFrom_plainEmptyOracle` — the empty-oracle elimination runs in
  exact lockstep.
* `Turing.OracleTM.queryString_length_le` — in an initialized run, the query after `t`
  steps has length at most `t`.
* `Turing.OracleTM.runFrom_workTapes_blank` — in an initialized run, cells at distance
  `≥ t` are still blank after `t` steps; the certificate that the no-blank fallback in
  `queryString` is unreachable from initialization.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4: oracle machines; Definition 3.4.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- An oracle Turing machine with `k` ordinary work tapes, one query tape (the work tape
of index `Fin.last k` in its configurations `Cfg (k + 1)`), and designated query and
answer states. Finiteness of `State` is deferred exactly as for `MultiTapeTM`, and so is
distinctness of the three special states: the raw structure allows them to coincide
(with degenerate behavior, e.g. `qYes = qQuery` re-queries forever after a positive
answer), and the faithful interface imposes `OracleTM.WellFormed`.
[AB09, Definition 3.4] -/
structure OracleTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- entering this state submits the query tape's contents to the oracle -/
  qQuery : State
  /-- the state the oracle answer step moves to on a positive answer -/
  qYes : State
  /-- the state the oracle answer step moves to on a negative answer -/
  qNo : State
  /-- transition function on the `k + 1` work tapes (the last being the query tape);
  consulted in every state except `qQuery` -/
  tr (q : State) (input : Option Symbol) (work : Fin (k + 1) → Option Symbol) :
    Action (k + 1) Symbol State

namespace OracleTM

variable {M : OracleTM k Symbol State}

/-- Well-formedness of an oracle machine: the query state and the two answer states are
pairwise distinct. Without this, the advertised semantics degenerates: with
`qYes = qQuery` a positive answer re-queries the unchanged tape forever (a negative
answer may still reach a distinct `qNo` and halt normally), and with all three states
collapsed the machine loops once the common query state is reached (an initial state
elsewhere can still halt via the table without ever querying). Moreover `qYes = qNo`
alone makes the step function — hence every run — oblivious to the oracle. This is the
standing hypothesis of the faithful oracle interface —
oracle complexity classes will require it. `q₀ = qQuery` is deliberately allowed: such a
machine simply submits the empty query on its first step.
(`audits/phase1-findings.md`, finding 2.) -/
structure WellFormed (M : OracleTM k Symbol State) : Prop where
  /-- the query state is not the positive-answer state -/
  qQuery_ne_qYes : M.qQuery ≠ M.qYes
  /-- the query state is not the negative-answer state -/
  qQuery_ne_qNo : M.qQuery ≠ M.qNo
  /-- the two answer states are distinct -/
  qYes_ne_qNo : M.qYes ≠ M.qNo

/-- The index of the query tape among the `k + 1` work tapes. -/
def queryTapeIdx (k : ℕ) : Fin (k + 1) := Fin.last k

open Classical in
/-- The query string of a configuration: the contents of the query tape from cell `0`
rightward, up to (excluding) the first blank cell. If no blank cell exists on the
nonnegative half-tape — impossible in configurations reachable from an initial
configuration, but possible for an arbitrary one — the query is `[]`. -/
noncomputable def queryString (cfg : Cfg (k + 1) Symbol State input) : List Symbol :=
  if h : ∃ n : ℕ, cfg.workTapes (queryTapeIdx k) (n : ℤ) = none then
    (List.range (Nat.find h)).filterMap fun n => cfg.workTapes (queryTapeIdx k) (n : ℤ)
  else []

open Classical in
/-- One step of the oracle machine `M` relative to the oracle `O`. In state `qQuery` the
machine moves to `qYes` or `qNo` according to whether the current query string is in `O`,
leaving tapes, head positions and output unchanged; in every other state it steps by its
transition function exactly like a plain machine. [AB09, §3.4] -/
noncomputable def step (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) : Cfg (k + 1) Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q =>
    if q = M.qQuery then
      { cfg with state := some (if queryString cfg ∈ O then M.qYes else M.qNo) }
    else
      (M.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration of an oracle machine: all `k + 1` work tapes (including the
query tape) blank. -/
@[simp]
def initCfg (M : OracleTM k Symbol State) (input : List Symbol) :
    Cfg (k + 1) Symbol State input :=
  Cfg.init M.q₀ input

/-- The configuration reached by running `M` with oracle `O` for `t` steps from `cfg`. -/
noncomputable def runFrom (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) : Cfg (k + 1) Symbol State input :=
  (M.step O)^[t] cfg

/-- `M` with oracle `O` halts on `input` within `t` steps with `output` on its output
tape. Time-only, mirroring `Turing.FinTM.ComputesInTime`. -/
def ComputesInTime (M : OracleTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) : Prop :=
  (M.runFrom O (M.initCfg input) t).state = none ∧
  (M.runFrom O (M.initCfg input) t).output = output

/-- Away from the query state, a step of an oracle machine does not depend on the oracle. -/
theorem step_eq_of_ne_qQuery (O₁ O₂ : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state ≠ some M.qQuery) :
    M.step O₁ cfg = M.step O₂ cfg := by
  unfold step
  cases hs : cfg.state with
  | none => rfl
  | some q =>
    have hne : q ≠ M.qQuery := fun hq => h (by rw [hs, hq])
    dsimp only
    rw [if_neg hne, if_neg hne]

/-- Applying any action changes a work-tape cell only at the old head position. -/
private lemma apply_workTapes_eq_of_ne {k' : ℕ} (a : Action k' Symbol State)
    (cfg : Cfg k' Symbol State input) (i : Fin k') {z : ℤ}
    (hz : z ≠ cfg.workTapePos i) :
    (a.apply cfg).workTapes i z = cfg.workTapes i z := by
  dsimp only [Action.apply]
  rcases h : (a.workTapes i).1 with _ | s
  · rfl
  · exact Function.update_of_ne hz _ _

/-- A work-tape head moves by at most one cell in a single oracle step. -/
lemma workTapePos_step_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (i : Fin (k + 1)) :
    |(M.step O cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  unfold step
  split
  · simp
  · split
    · simp
    · exact workTapePos_apply_le _ cfg i

/-- An oracle step writes only at the old head position. -/
lemma workTapes_step_eq_of_ne (M : OracleTM k Symbol State) (O : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (i : Fin (k + 1)) {z : ℤ}
    (hz : z ≠ cfg.workTapePos i) :
    (M.step O cfg).workTapes i z = cfg.workTapes i z := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · exact apply_workTapes_eq_of_ne _ cfg i hz

/-- The two run invariants of an initialized oracle run: after `t` steps every work
head is within distance `t` of the origin, and every cell at distance at least `t` is
still blank. -/
private lemma runFrom_workTapes_invariant (M : OracleTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) : ∀ t : ℕ,
    (∀ i, |(M.runFrom O (M.initCfg x) t).workTapePos i| ≤ (t : ℤ)) ∧
    (∀ i (z : ℤ), (t : ℤ) ≤ |z| → (M.runFrom O (M.initCfg x) t).workTapes i z = none) := by
  intro t
  induction t with
  | zero =>
    constructor
    · intro i
      simp [runFrom]
    · intro i z _
      simp [runFrom]
  | succ t ih =>
    obtain ⟨hpos, hblank⟩ := ih
    have hstep : M.runFrom O (M.initCfg x) (t + 1) =
        M.step O (M.runFrom O (M.initCfg x) t) :=
      Function.iterate_succ_apply' _ _ _
    constructor
    · intro i
      rw [hstep]
      have h1 := M.workTapePos_step_le O (M.runFrom O (M.initCfg x) t) i
      have h2 := hpos i
      rw [abs_le] at h1 h2 ⊢
      omega
    · intro i z hz
      rw [hstep]
      have hz' : (t : ℤ) ≤ |z| := le_trans (by omega) hz
      have hne : z ≠ (M.runFrom O (M.initCfg x) t).workTapePos i := by
        intro hzeq
        have h2 := hpos i
        rw [← hzeq] at h2
        have h3 : ((t : ℤ) + 1) ≤ |z| := by exact_mod_cast hz
        have h4 := le_trans h3 h2
        omega
      rw [M.workTapes_step_eq_of_ne O i hne]
      exact hblank i z hz'

/-- In an initialized run, the query after `t` steps has length at most `t`. In
particular the no-blank fallback branch of `queryString` is unreachable from an initial
configuration.

**Proof sketch.** By induction on `t`, every write performed in the first `t` steps
happened at a head position of absolute value at most `t - 1` (heads start at `0` and
move at most one cell per step, `Turing.workTapePos_apply_le`). Hence cell `t` of the
query tape is still blank at time `t`, so the least-blank search in `queryString`
terminates at an index `≤ t`. -/
theorem queryString_length_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) :
    (queryString (M.runFrom O (M.initCfg x) t)).length ≤ t := by
  have hblank : (M.runFrom O (M.initCfg x) t).workTapes (queryTapeIdx k) ((t : ℕ) : ℤ) =
      none :=
    (runFrom_workTapes_invariant M O x t).2 _ _ (le_abs_self _)
  classical
  simp only [queryString]
  rw [dif_pos ⟨t, hblank⟩]
  refine le_trans (List.length_filterMap_le _ _) ?_
  simpa using Nat.find_min'
    (p := fun n : ℕ =>
      (M.runFrom O (M.initCfg x) t).workTapes (queryTapeIdx k) (n : ℤ) = none)
    ⟨t, hblank⟩ hblank

/-- In an initialized run, every work-tape cell at distance at least `t` from the
origin is still blank after `t` steps. This is the certificate that the no-blank
fallback branch of `queryString` is unreachable from initialization (the length bound
`queryString_length_le` alone does not certify this, since the fallback also returns a
short list).

**Proof sketch.** Simultaneous induction on `t` with the head-position bound
`|workTapePos i| ≤ t`: at `t = 0` all tapes are blank and heads are at `0`; an ordinary
step writes only at the *old* head position (of absolute value `≤ t`, hence `< t + 1`;
`Action.apply` writes before moving) and moves each head by at most one cell
(`Turing.workTapePos_apply_le`); oracle-answer and halted steps change no tape. -/
theorem runFrom_workTapes_blank (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) (i : Fin (k + 1)) (z : ℤ) (hz : (t : ℤ) ≤ |z|) :
    (M.runFrom O (M.initCfg x) t).workTapes i z = none :=
  (runFrom_workTapes_invariant M O x t).2 i z hz

end OracleTM

/-- Extend an action on `k` work tapes to `k + 1` work tapes: the extra (last) tape is
neither written nor moved. -/
def Action.extend (a : Action k Symbol State) : Action (k + 1) Symbol State where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < k then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := a.state

/-- Rename the states of an action along a function. -/
def Action.mapState {State' : Type*} (f : State → State') (a : Action k Symbol State) :
    Action k Symbol State' where
  inputTape := a.inputTape
  workTapes := a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a `k`-tape configuration into a `k + 1`-tape configuration over the extended
state type `State ⊕ Fin 3`: the extra work tape is blank with its head at `0`, and the
state is renamed along `Sum.inl`. -/
def Cfg.embedOracle (cfg : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol (State ⊕ Fin 3) input where
  state := cfg.state.map Sum.inl
  inputPos := cfg.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < k then cfg.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i => if h : (i : ℕ) < k then cfg.workTapePos ⟨i, h⟩ else 0
  output := cfg.output

/-- The embedding preserves the scanned input symbol. -/
lemma Cfg.embedOracle_inputSymbol (cfg : Cfg k Symbol State input) :
    cfg.embedOracle.inputSymbol = cfg.inputSymbol := rfl

/-- The embedding preserves the scanned work symbols on the original tapes. -/
lemma Cfg.embedOracle_workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) :
    cfg.embedOracle.workTapeSymbols i.castSucc = cfg.workTapeSymbols i := by
  simp [Cfg.workTapeSymbols, Cfg.embedOracle]

/-- The embedding preserves haltedness. -/
lemma Cfg.embedOracle_state_eq_none {cfg : Cfg k Symbol State input} :
    cfg.embedOracle.state = none ↔ cfg.state = none := by
  simp [Cfg.embedOracle, Option.map_eq_none_iff]

/-- The embedding preserves the output tape. -/
lemma Cfg.embedOracle_output (cfg : Cfg k Symbol State input) :
    cfg.embedOracle.output = cfg.output := rfl

/-- Applying an extended, state-renamed action to an embedded configuration is the
embedding of applying the original action. -/
lemma Cfg.embedOracle_apply (a : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    ((a.mapState (Sum.inl : State → State ⊕ Fin 3)).extend).apply cfg.embedOracle =
      (a.apply cfg).embedOracle := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_pos hi]
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_neg hi]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_pos hi]
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_neg hi]
      simp
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]

/-- The embedding sends initial configurations to initial configurations. -/
lemma Cfg.embedOracle_init (q₀ : State) (input : List Symbol) :
    (Cfg.init q₀ input : Cfg k Symbol State input).embedOracle =
      Cfg.init (Sum.inl q₀ : State ⊕ Fin 3) input := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Cfg.embedOracle]

namespace OracleTM

/-- Embed a plain machine as an oracle machine that never queries: the state type is
extended by three fresh states serving as `qQuery`, `qYes`, `qNo`, and the transition
function acts as before on original states (never moving into the fresh states, and
ignoring the query tape). The fresh states are unreachable from the initial
configuration. The *transition table* halts immediately from all three fresh states;
note that from `qQuery` itself the query override fires first (one answer step into
`qYes`/`qNo`, whose table entries then halt) — the table's `qQuery` row is dead code. -/
def ofMultiTapeTM (tm : MultiTapeTM k Symbol State) : OracleTM k Symbol (State ⊕ Fin 3) where
  q₀ := .inl tm.q₀
  qQuery := .inr 0
  qYes := .inr 1
  qNo := .inr 2
  tr q inp work :=
    match q with
    | .inl q => ((tm.tr q inp fun i => work i.castSucc).mapState Sum.inl).extend
    | .inr _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- The embedding of a plain machine is well-formed: its three fresh special states are
pairwise distinct by construction. -/
theorem ofMultiTapeTM_wellFormed (tm : MultiTapeTM k Symbol State) :
    (ofMultiTapeTM tm).WellFormed := by
  constructor <;> simp [ofMultiTapeTM]

/-- One step of an embedded plain machine, under any oracle, is the embedding of one
step of the original machine: the embedded state is never `qQuery = Sum.inr 0`, so the
oracle step reduces to applying the extended action, and `Cfg.embedOracle_apply` turns
that into the embedding of the original step. -/
lemma step_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) :
    (ofMultiTapeTM tm).step O cfg.embedOracle = (tm.step cfg).embedOracle := by
  unfold OracleTM.step MultiTapeTM.step
  cases hs : cfg.state with
  | none =>
    have h : cfg.embedOracle.state = none := by simp [Cfg.embedOracle, hs]
    rw [h]
  | some q =>
    have h : cfg.embedOracle.state = some (Sum.inl q) := by simp [Cfg.embedOracle, hs]
    rw [h]
    dsimp only
    have hne : (Sum.inl q : State ⊕ Fin 3) ≠ (ofMultiTapeTM tm).qQuery := by
      simp [ofMultiTapeTM]
    rw [if_neg hne]
    have hw : (fun i => cfg.embedOracle.workTapeSymbols i.castSucc) =
        cfg.workTapeSymbols :=
      funext fun i => Cfg.embedOracle_workTapeSymbols cfg i
    have htr : (ofMultiTapeTM tm).tr (Sum.inl q) cfg.embedOracle.inputSymbol
        cfg.embedOracle.workTapeSymbols =
        ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).mapState Sum.inl).extend := by
      show ((tm.tr q cfg.embedOracle.inputSymbol
        fun i => cfg.embedOracle.workTapeSymbols i.castSucc).mapState Sum.inl).extend = _
      rw [Cfg.embedOracle_inputSymbol, hw]
    rw [htr, Cfg.embedOracle_apply]

/-- **Sanity check for the oracle architecture** (plan §3.1): an embedded plain machine
runs in lockstep with the original under every oracle — `step_ofMultiTapeTM` pointwise,
then induction on `t`. -/
theorem runFrom_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (ofMultiTapeTM tm).runFrom O cfg.embedOracle t = (tm.runFrom cfg t).embedOracle := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : (ofMultiTapeTM tm).runFrom O cfg.embedOracle (t + 1) =
        (ofMultiTapeTM tm).step O ((ofMultiTapeTM tm).runFrom O cfg.embedOracle t) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1, ih, MultiTapeTM.runFrom_succ_eq_step', step_ofMultiTapeTM]

/-- An embedded plain machine has the same input/output behavior and time bounds as the
original, relative to every oracle. In particular its behavior is oracle-independent.

**Proof sketch.** `Cfg.embedOracle` sends the initial configuration of `tm` to the initial
configuration of the embedded machine (both have blank work tapes and heads at `0`); by
`runFrom_ofMultiTapeTM` the runs correspond, and `Cfg.embedOracle` preserves haltedness
and the output tape. -/
theorem computesInTime_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) :
    (ofMultiTapeTM tm).ComputesInTime O input output t ↔
      ((tm.runFrom (tm.initCfg input) t).state = none ∧
        (tm.runFrom (tm.initCfg input) t).output = output) := by
  have hinit : (ofMultiTapeTM tm).initCfg input = (tm.initCfg input).embedOracle := by
    simp only [OracleTM.initCfg, MultiTapeTM.initCfg, ofMultiTapeTM]
    exact (Cfg.embedOracle_init tm.q₀ input).symm
  simp only [OracleTM.ComputesInTime, hinit, runFrom_ofMultiTapeTM,
    Cfg.embedOracle_state_eq_none, Cfg.embedOracle_output]

open Classical in
/-- The converse of `ofMultiTapeTM` for the empty oracle: an oracle machine run with the
empty oracle is eliminated into a plain `k + 1`-tape machine over the *same* state type,
by replacing the query behavior with a stationary transition into `qNo` (the empty
oracle always answers no). (`audits/phase1-findings.md`, finding 8.) -/
noncomputable def plainEmptyOracle (M : OracleTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State where
  q₀ := M.q₀
  tr q inp work :=
    if q = M.qQuery then ⟨0, fun _ => (none, 0), none, some M.qNo⟩
    else M.tr q inp work

/-- One step of the empty-oracle elimination coincides with one step of the oracle
machine on the empty oracle: on a halted configuration both sides are fixed; in state
`qQuery` the empty oracle answers `qNo` and the stationary action's `Action.apply`
changes only the state; elsewhere both sides apply the same transition-table action. -/
lemma step_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) :
    M.plainEmptyOracle.step cfg = M.step (0 : Language Symbol) cfg := by
  unfold MultiTapeTM.step OracleTM.step plainEmptyOracle
  cases hs : cfg.state with
  | none => rfl
  | some q =>
    dsimp only
    by_cases hq : q = M.qQuery
    · rw [if_pos hq, if_pos hq, if_neg (Language.notMem_zero _)]
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Action.apply]
    · rw [if_neg hq, if_neg hq]

/-- **Sanity check, converse direction**: the empty-oracle elimination runs in exact
lockstep with the oracle machine on the empty oracle — same configurations at every
step, from every starting configuration (`step_plainEmptyOracle` pointwise, then
induction on `t`). -/
theorem runFrom_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) :
    -- `0` is the empty language (`Language`'s `Zero` instance)
    M.plainEmptyOracle.runFrom cfg t = M.runFrom (0 : Language Symbol) cfg t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : M.runFrom (0 : Language Symbol) cfg (t + 1) =
        M.step 0 (M.runFrom (0 : Language Symbol) cfg t) :=
      Function.iterate_succ_apply' _ _ _
    rw [MultiTapeTM.runFrom_succ_eq_step', h1, ih, step_plainEmptyOracle]

end OracleTM

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Alphabet reduction

[AB09, Claim 1.5]: a machine over any finite alphabet `Γ` is simulated by a machine
over the binary alphabet with only a constant-factor slowdown (the constant depending
on `|Γ|`), and with the same number of work tapes. This is the theorem that justifies
defining `DTIME` over binary-alphabet machines (see
`TCSlib.Complexity.ClassP.DTIME`).

## Deviations from [AB09]

* [AB09] states the slowdown as `4 log |Γ| · T(n)`; we existentialize the constant and
  pad with `+ 1` (empty input), consistently with the rest of the development.
* [AB09]'s statement fixes input and output over `{0,1}` with only the *work* alphabet
  reduced. In our model a machine has one alphabet for all tapes, so "computing a
  binary function" for a `Γ`-machine is expressed via a symbol embedding `e : Bool ↪ Γ`
  (`Turing.FinTM.ComputesFunInTimeVia`): the simulator reads genuine binary input
  directly (its table composes with `e`), block-encodes work-tape symbols in
  `⌈log₂ |Γ|⌉` bits, and decodes each emitted symbol `e b` back to the bit `b`.
  Emitted symbols are always in the range of `e` because the append-only output equals
  the final output string, which is `(f x).map e` — early emissions included, since an
  irrevocable emission remains a prefix of the final output.
* [AB09]'s Claim 1.5 hypothesizes a time-constructible `T`; the simulation does not
  need it, so we drop the hypothesis. The statement also generalizes Boolean output to
  string output.

## Main results

* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16.)
-/

namespace Turing.FinTM

/-- **Alphabet reduction** [AB09, Claim 1.5]: if a machine over a finite alphabet `Γ`
computes the binary string function `f` via `e : Bool ↪ Γ` within time `T`, then a
binary-alphabet machine with the *same number of work tapes* computes `f` within
`c · (T n + 1)` for some constant `c` (depending on the original machine).

**Proof sketch.** Fix a binary block code of length `L = ⌈log₂ |Γ|⌉` for `Option Γ`'s
non-blank symbols. `M'` keeps each of `M`'s work tapes as a block-encoded tape. One
step of `M` is simulated by: reading the `L` bits under each work head into the state
(`L` steps per tape, walking right), reading the input bit directly (its `e`-image is
determined by the table), computing `M`'s transition inside the finite state, writing
back the `L`-bit codes while returning left (`L` steps per tape), moving each head `L`
cells in the simulated direction, and emitting the decoded bit whenever `M` emits.
Total: at most `c` steps of `M'` per step of `M` with `c = O((k + 1) · L)` — the
`+ 1` covering the input-read, state-update, and emission work that remains even for
`k = 0` — plus a constant start-up. Logical blank is represented by the all-blank (`none`-cell) block — never-
visited blocks already have this shape, so no binary code needs reserving and no
initialization pass is required (phase-2 audit, finding 8). The invariant
relating block-encoded configurations to `M`'s configurations is preserved by each
simulated step, and `M`'s halting transfers. -/
theorem alphabet_reduction {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f fun n => c * (T n + 1) := by
  sorry

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to one work tape

[AB09, Claim 1.6]: `k` work tapes are simulated by a single work tape with a quadratic
slowdown.

## Deviations from [AB09]

* [AB09]'s Claim 1.6 merges input, work, *and output* into one single tape (the
  standard model of Sipser's text). Our model structurally always has a separate
  read-only input tape and write-only output tape, so the faithful in-model rendering
  is **one work tape**: the interesting content — interleaving `k` tapes on one, with
  marked head positions and full sweeps — is identical, while the merged-single-tape
  model itself is out of scope (it is a different structure, not an instance of
  `MultiTapeTM`).
* [AB09] states the slowdown as `5k T(n)²`; we existentialize the constant and use
  `(T n + 1)²`.
* The retained structure is a genuinely different model from [AB09]'s merged one, not
  a notational variant: with a separate input tape, palindromes are decidable in
  linear time (`TCSlib.Complexity.ClassP.Examples`), while the merged single-tape
  model has an `Ω(n²)` lower bound for them ([AB09], chapter notes, citing Maass).
  Accordingly, the theorems below are *in-model analogues* of Claim 1.6, and no
  identification with the merged model is claimed anywhere in this development
  (phase-2 audit, finding 5).

## Main results

* `Turing.FinTM.one_work_tape` — [AB09, Claim 1.6] over an enlarged alphabet.
* `Turing.FinTM.one_work_tape_binary` — combined with alphabet reduction
  ([AB09, Claim 1.5]): one work tape *and* binary alphabet, still quadratic.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.6, p. 17; Remark 1.7.)
-/

namespace Turing.FinTM

/-- **One work tape suffices** [AB09, Claim 1.6]: a `Γ`-machine computing `f` within
`T` is simulated by a machine with a single work tape, over an enlarged finite
alphabet, within `c · (T n + 1)²`.

**Proof sketch.** For `k = 0`, simulate `M` directly with one unused work tape.
For `k ≥ 1`, the single work tape of `M'` stores the `k` tapes of `M` interleaved:
cell `j·k + i` of the simulated layout holds cell `j` of tape `i` (centered at `0` in
both directions). The alphabet is enlarged to cells carrying a *tagged payload*
`Option Γ` — so a marked blank is representable, which a bare `Γ × flag` product
would miss — together with a "head here" flag and zone-boundary tags; `Γ` embeds via
`e` as an unmarked non-blank payload. To simulate one step of `M`, `M'` sweeps its work tape once
left-to-right across the visited zone recording the `k` marked symbols in its state,
computes `M`'s transition, and sweeps back right-to-left updating the marked cells and
moving the marks. After `t` steps of `M` the visited zone spans `O(k · (t + 1))`
cells, so each simulated step costs `O(k · (T n + 1))` and the total is
`c · (T n + 1)²`. Input reads and output emissions pass through unchanged. -/
theorem one_work_tape {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) ^ 2 := by
  sorry

/-- One work tape and the binary alphabet suffice simultaneously: the composition of
[AB09, Claim 1.6] with [AB09, Claim 1.5], possible because alphabet reduction
preserves the number of work tapes.

**Proof sketch.** Apply `Turing.FinTM.one_work_tape` to `M` with `Γ = Bool`,
obtaining a one-work-tape machine over some `Γ'` that computes `f` via an embedding
`Bool ↪ Γ'` within `c₁ · (T n + 1)²` — exactly the hypothesis of
`Turing.FinTM.alphabet_reduction`, which keeps `k = 1` and returns to the binary
alphabet within `c₂ · (c₁ · (T n + 1)² + 1) ≤ c · (T n + 1)²`. -/
theorem one_work_tape_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTime f fun n => c * (T n + 1) ^ 2 := by
  obtain ⟨Γ', instF, instD, e, M₁, c₁, hk₁, h₁⟩ := one_work_tape M f T hM
  haveI := instF
  haveI := instD
  obtain ⟨c₂, M₂, hk₂, h₂⟩ :=
    alphabet_reduction e M₁ f (fun n => c₁ * (T n + 1) ^ 2) h₁
  refine ⟨M₂, c₂ * (c₁ + 1), by rw [hk₂, hk₁], fun x => (h₂ x).mono ?_⟩
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc c₂ * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ c₂ * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl c₂) (Nat.add_le_add_left hpow _)
    _ = c₂ * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bidirectional versus unidirectional tapes

[AB09, Claim 1.8]: tapes that are infinite in both directions are simulated by tapes
infinite in one direction only, with constant-factor slowdown.

## Deviations from [AB09]

Our vendored model's tapes are *already* bidirectional (`ℤ`-indexed) — that choice is
what lets initialization dispense with start markers. So the faithful in-model
rendering of Claim 1.8 runs in the only meaningful direction: every machine is
simulated, with constant-factor slowdown and the same number of work tapes, by one
whose work heads **never visit a negative cell** (`Turing.FinTM.NonnegativeHeads`),
i.e. by a machine that uses its tapes unidirectionally. The simulating machine "folds"
each tape at the origin, following [AB09]'s proof, over the enlarged non-blank
alphabet `Bool × Option Γ × Option Γ` — an origin flag plus two *independent*,
possibly blank, payloads. (A bare `Γ × Γ` cannot represent a symbol paired with a
blank neighbor; phase-2 re-audit, finding 1.)

## Main results

* `Turing.FinTM.NonnegativeHeads` — the unidirectional-use predicate.
* `Turing.FinTM.nonnegative_heads` — [AB09, Claim 1.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.8, p. 18.)
-/

namespace Turing.FinTM

/-- A machine uses its work tapes unidirectionally: in every initialized run, no work
head ever visits a negative cell. -/
def NonnegativeHeads {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (input : List Γ) (t : ℕ) (i : Fin M.k),
    0 ≤ (M.tm.runFrom (M.tm.initCfg input) t).workTapePos i

/-- **Unidirectional tapes suffice** [AB09, Claim 1.8]: a `Γ`-machine computing `f`
within `T` is simulated, with the same number of work tapes and constant-factor
slowdown, by a machine over an enlarged alphabet whose work heads never visit negative
cells.

**Proof sketch.** Fold each tape at the origin along the coordinate
`φ z = if 0 ≤ z then z else -z - 1` (note `φ 0 = φ (-1) = 0`; this is *not* the
absolute value): physical cell `p ≥ 0` holds the two *independent* payloads —
simulated cell `p` and simulated cell `-p - 1`, each possibly blank — over the
enlarged non-blank alphabet `Γ' = Bool × Option Γ × Option Γ`, whose Boolean
component is an origin flag; `e γ = (false, some γ, none)` (injective via its first
payload), and an untouched physical blank decodes as two blanks with no flag. The
simulator's state tracks, per tape, which component the simulated head is in. Because
a transition cannot read a head coordinate, the origin is made *detectable* by a
fresh initialization state whose single action writes `(true, none, none)` at cell
`0` of every work tape simultaneously (one transition, length-independent); every
later write updates only the active payload, preserving the other payload and the
flag. Moves translate directly except at the fold: crossing between simulated cells `0`
and `-1` flips the component *without* issuing a physical move (the physical
coordinate stays `0`); each simulated step costs a constant number of physical steps,
giving `c · (T n + 1)` — [AB09] gets `4T`. Physical head positions are values of `φ`,
hence nonnegative; on enlarged-alphabet inputs containing symbols outside the range
of `e` — where no functional behavior is promised but `NonnegativeHeads` still
quantifies — the simulator halts safely on first contact, preserving nonnegativity
(phase-2 audit, finding 10 and case A14). The folding invariant transfers computation
and halting on embedded inputs. -/
theorem nonnegative_heads {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.NonnegativeHeads ∧ M'.k = M.k ∧
        M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) := by
  sorry

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines

A machine is *oblivious* if its head movements depend only on the input length, not on
the input itself [AB09, Remark 1.7 and Exercise 1.5]. Obliviousness will matter for
the Cook-Levin theorem (Chapter 2), where the tableau of an oblivious computation has
input-independent structure.

## Design

* Configurations are indexed by their input, so head positions of runs on different
  inputs live in different types only for the input head; obliviousness compares
  `Fin`-valued input positions through `ℕ` and work positions (in `ℤ`) directly.
* `Oblivious` constrains *represented* head trajectories only — the input head and
  the work heads. Our model has no output-head position (output is an append-only
  stream), so emission schedules are deliberately unconstrained; [AB09]'s read-write
  output head is covered by this reading only via a bridge, e.g. a machine that emits
  once at a fixed final time, as the decider produced below does.
* `Oblivious` does **not** imply that the halting time is determined by the input
  length: heads freeze on halting, but frozen positions can coincidentally agree — a
  stationary-head machine can halt after one or two steps depending on its first
  input bit while satisfying `Oblivious` (phase-2 audit, finding 1, with an explicit
  counterexample in `audits/phase2-findings.md`). The `TimeConstructible` hypothesis
  below is required by the *construction* (the simulator derives a length-determined
  step budget and pads its schedule to it), not forced by the definition. If a
  downstream use (the Cook-Levin tableau, Ch. 2) needs length-determined halting or a
  simultaneous one-work-tape oblivious normal form (`M.k = 1 ∧ M.Oblivious`), those
  are separate conjuncts for that normal-form theorem.
* We state the quadratic version — Exercise 1.5's *first assertion*, adapted to this
  model; the exercise's final two-tape normal form is **not** included here. The
  `O(T log T)` sharpening (Exercise 1.6) is a stretch goal alongside §1.7, off the
  critical path.

## Main definitions

* `Turing.FinTM.Oblivious` — [AB09, Remark 1.7].

## Main results

* `Complexity.oblivious_of_mem_DTIME` — [AB09, Exercise 1.5]: every language decidable
  in time-constructible time `T` is decided by an oblivious machine in `O((T + 1)²)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, p. 17; Exercise 1.5, p. 34.)
-/

namespace Turing.FinTM

/-- A machine is *oblivious* if, at every step, its head positions on two inputs of
the same length agree: they are a function of the input length and the time only.
[AB09, Remark 1.7] -/
def Oblivious {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (x y : List Γ), x.length = y.length → ∀ t : ℕ,
    (((M.tm.runFrom (M.tm.initCfg x) t).inputPos : ℕ) =
      ((M.tm.runFrom (M.tm.initCfg y) t).inputPos : ℕ)) ∧
    (M.tm.runFrom (M.tm.initCfg x) t).workTapePos =
      (M.tm.runFrom (M.tm.initCfg y) t).workTapePos

end Turing.FinTM

namespace Complexity

open Turing

/-- **Oblivious simulation** — the first assertion of [AB09, Exercise 1.5], adapted
to this model: for time-constructible `T`, every language in `DTIME T` is decided by
an *oblivious* machine within `c · (T n + 1)²`. (The exercise's additional two-tape
normal form is not part of this statement.)

**Proof sketch** (corrected per the phase-2 audit, finding 2: the construction must
not invoke `one_work_tape_binary` per simulated step — that composes quadratics into
a quartic — must not run the constructibility witness verbatim, which need not be
oblivious, and must park the real input head). Take a decider for `L` within
`a · T n` and a constructibility witness within `b · (T n + 1)`.

1. Run the witness with every non-blank input symbol *read as `false`* (substituted
   in its transition table): its entire run — trajectories, emissions, halting time —
   then coincides with its run on the all-`false` input of length `n`, hence depends
   only on `n`, and it still computes `⌞T n⌟`; store the budget on a work tape.
2. Copy the real input to a work tape in one fixed scan and rewind (cost
   `O(n + 1)`, absorbed since `n ≤ T n`), then park the real input head for good.
3. Set `B n = (a + 1) · (T n + 1)` macrosteps and prepare a marked layout of size
   `O(B n)` holding the decider's work tapes, the virtual input copy, virtual head
   markers, and a step counter.
4. Each macrostep simulates one step of the decider by a fixed number of full sweeps
   of the layout — tape data affects writes, simulated state, and markers, never the
   sweep path or its duration — idling identically once the simulated machine halts,
   for exactly `B n` macrosteps (counter maintenance within the per-macrostep linear
   allowance; fixed-duration binary block coding throughout, so no appeal to the
   existential `alphabet_reduction` is needed to stay binary and oblivious).
5. Emit the stored answer bit at a fixed final time and halt.

Every head trajectory and the halting time are then functions of `n` and `t` alone,
and the total cost is `O(b · (T n + 1) + (B n)²) = O((T n + 1)²)`. -/
theorem oblivious_of_mem_DTIME {L : Language Bool} {T : ℕ → ℕ}
    (hT : TimeConstructible T) (hL : L ∈ DTIME T) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.Oblivious ∧ M.DecidesInTime L fun n => c * (T n + 1) ^ 2 := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity
```

## ===== TCSlib/Complexity/ClassP/P.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class P

`P` is the class of languages decidable in polynomial time: the union over `c` of
`DTIME (n^c + 1)`. [AB09, Definition 1.13, with the `+ 1` padding explained below —
every *positive*-degree component of the literal unpadded union is empty in this model,
since `n^c` vanishes at `n = 0` and no machine halts in zero steps; [AB09]'s union
ranges over `c ≥ 1`, so its literal reading is empty, while including degree `0` would
give exactly `DTIME 1` (in Lean `0 ^ 0 = 1`).]

## Design and deviations from [AB09]

* We take the union of `DTIME (fun n => n ^ c + 1)` over all `c : ℕ` where [AB09] writes
  `⋃_{c ≥ 1} DTIME(n^c)`. The `+ 1` repairs the empty-input degeneracy: a machine needs
  at least one step to halt, so for the degrees `d ≥ 1` of [AB09]'s union no language
  whatsoever is decided within `c · 0^d = 0` steps on the empty input, and the literal
  [AB09] definition would (vacuously) exclude even constant-time machines on that input. For `n ≥ 1` the bounds `c · (n^d + 1)` and
  `c' · n^d` sandwich each other, so this is the standard reading of the same class.
  Ranging over `c = 0` too is harmless: `n^0 + 1 = 2` is a constant bound, subsumed by
  larger `c`.

## Main definitions

* `Complexity.P` — [AB09, Definition 1.13].

## Main results

* `Complexity.dtime_poly_subset_P` — each `DTIME (n^c + 1)` is contained in `P`.
* `Complexity.mem_P_iff` — `P` is exactly the class decidable within `C · (n + 1) ^ d`
  for some constants, certifying that the `+ 1` padding has the conventional
  polynomial-time content.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definition 1.13.)
-/

namespace Complexity

open Turing

/-- The class of polynomial-time decidable languages:
`P = ⋃ c, DTIME (n^c + 1)`. [AB09, Definition 1.13] -/
def P : Set (Language Bool) := ⋃ c : ℕ, DTIME fun n => n ^ c + 1

/-- Every fixed-degree polynomial time class is contained in `P`. -/
theorem dtime_poly_subset_P (c : ℕ) : DTIME (fun n => n ^ c + 1) ⊆ P :=
  Set.subset_iUnion (fun c : ℕ => DTIME fun n => n ^ c + 1) c

/-- Membership in `P` from a concrete polynomial bound: if `L` is decidable within any
time bound that is pointwise dominated by a polynomial, then `L ∈ P`. (Pointwise, not
eventual, domination: an eventual-bound variant follows with the *same machine* by
absorbing the finitely many exceptional bounds into the constant, and is deferred.)

**Proof sketch.** Pick `c` and `d` with `T n ≤ c * (n ^ d + 1)` for all `n`. By
`Complexity.DTIME.mono`, `DTIME T ⊆ DTIME (fun n => c * (n ^ d + 1))`; the latter equals
a subclass of `DTIME (fun n => n ^ d + 1)` because the constant `c` is absorbed by the
existential constant in the definition of `DTIME` (the two constants multiply). Conclude
with `Complexity.dtime_poly_subset_P`. -/
theorem mem_P_of_dtime_le {L : Language Bool} {T : ℕ → ℕ}
    (hL : L ∈ DTIME T) (c d : ℕ) (hT : ∀ n, T n ≤ c * (n ^ d + 1)) : L ∈ P := by
  obtain ⟨a, M, hM⟩ := hL
  refine dtime_poly_subset_P d ⟨a * c, M, fun x => (hM x).mono ?_⟩
  calc a * T x.length ≤ a * (c * (x.length ^ d + 1)) :=
        Nat.mul_le_mul (le_refl a) (hT x.length)
    _ = a * c * (x.length ^ d + 1) := by ring

/-- The key pointwise inequality behind the padding normalization:
`(n + 1) ^ d ≤ 2 ^ d · (n ^ d + 1)` for every `n` and `d`. -/
lemma succ_pow_le (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ d * (n ^ d + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _)
  · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ d * n ^ d := Nat.mul_pow 2 n d
      _ ≤ 2 ^ d * (n ^ d + 1) := Nat.mul_le_mul (le_refl _) (Nat.le_succ _)

/-- `P` is exactly the class of languages decidable within `C · (n + 1) ^ d` steps for
some constants `C` and `d`. This certifies that the `+ 1` padding in the definition of
`P` has the conventional polynomial-time content: forward, a witness for the degree-`c`
component gives a bound `a · (n ^ c + 1) ≤ 2a · (n + 1) ^ c`; backward, `succ_pow_le`
turns a `C · (n + 1) ^ d` decider into a `(C · 2 ^ d) · (n ^ d + 1)` decider, landing
in the degree-`d` component. (`audits/phase1-findings.md`, "Polynomial-time
normalization".) -/
theorem mem_P_iff {L : Language Bool} :
    L ∈ P ↔ ∃ (C d : ℕ) (M : FinTM Bool),
      M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨c, hs⟩ := Set.mem_iUnion.mp hL
    obtain ⟨a, M, hM⟩ := hs
    refine ⟨2 * a, c, M, fun x => (hM x).mono ?_⟩
    have h1 : x.length ^ c ≤ (x.length + 1) ^ c :=
      Nat.pow_le_pow_left (Nat.le_succ _) c
    have h2 : 0 < (x.length + 1) ^ c := Nat.pow_pos (Nat.succ_pos _)
    calc a * (x.length ^ c + 1)
        ≤ a * ((x.length + 1) ^ c + (x.length + 1) ^ c) :=
          Nat.mul_le_mul (le_refl a) (Nat.add_le_add h1 h2)
      _ = 2 * a * (x.length + 1) ^ c := by ring
  · rintro ⟨C, d, M, hM⟩
    refine Set.mem_iUnion.mpr ⟨d, C * 2 ^ d, M, fun x => (hM x).mono ?_⟩
    calc C * (x.length + 1) ^ d
        ≤ C * (2 ^ d * (x.length ^ d + 1)) :=
          Nat.mul_le_mul (le_refl C) (succ_pow_le x.length d)
      _ = C * 2 ^ d * (x.length ^ d + 1) := by ring

/-- Constant time is polynomial time.

**Proof sketch.** `Complexity.mem_P_of_dtime_le` with `T = fun _ => 1`, `c = 1`,
`d = 1`, since `1 ≤ 1 * (n ^ 1 + 1)`. -/
theorem dtime_one_subset_P : DTIME (fun _ => 1) ⊆ P := fun _ hL =>
  mem_P_of_dtime_le hL 1 1 fun n => by
    rw [one_mul]
    exact Nat.le_add_left 1 (n ^ 1)

end Complexity
```

## ===== TCSlib/Complexity/ClassP/ModelInvariance.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# "And why it doesn't matter": model invariance of DTIME and P

The payoff of the robustness theorems ([AB09, §1.3.1], formalized in
`TCSlib.Complexity.TuringMachine.Robustness`), stated at the strength the theorems
actually deliver (phase-2 audit, finding 4): **alphabet size** never matters —
`DTIME` is alphabet-invariant, the alphabet-dependent constant being absorbed by
`DTIME`'s own existential — while **the number of work tapes** does not matter *for
`P`*, where the quadratic overhead of tape reduction is harmless. No invariance of a
fixed class `DTIME T` under tape reduction is claimed, and [AB09, §1.6.1] likewise
draws only the polynomial-time conclusion. This is the formal content of the
chapter's title at class level.

## Main definitions

* `Turing.FinTM.DecidesInTimeVia` — a machine over a larger alphabet decides a binary
  language via a symbol embedding.

## Main results

* `Complexity.mem_DTIME_of_decidesInTimeVia` — deciding over any finite alphabet lands
  in binary `DTIME` (constant absorbed). [AB09, Claim 1.5 for languages]
* `Complexity.mem_P_of_decidesInTimeVia_poly` — `P` is alphabet-invariant.
* `Complexity.mem_P_iff_one_work_tape` — `P` is exactly what one-work-tape binary
  machines decide in polynomial time. [AB09, Claims 1.5-1.6 for `P`]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3.1; §1.6.1 "Why the model may not matter".)
-/

namespace Turing.FinTM

/-- The machine `M`, over alphabet `Γ`, decides the binary language `L` via the symbol
embedding `e : Bool ↪ Γ` within time `T`: on every input `x.map e` it halts within
`T |x|` steps with output `[e b]` where `b` is the membership bit of `x` in `L`. -/
def DecidesInTimeVia {Γ : Type} (M : FinTM Γ) (e : Bool ↪ Γ) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime (x.map e)
      [e (MultiTapeTM.indicator (L : Set (List Bool)) x)] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- Deciding a language over *any* finite alphabet puts it in the binary-machine class
`DTIME` (with the alphabet-dependent constant absorbed by `DTIME`'s existential).

**Proof sketch.** `DecidesInTimeVia` is `ComputesFunInTimeVia` for the function
`x ↦ [indicator L x]` (note `[b].map e = [e b]`); apply
`Turing.FinTM.alphabet_reduction` and absorb its constant `c` into `DTIME`'s. -/
theorem mem_DTIME_of_decidesInTimeVia {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} {T : ℕ → ℕ}
    (h : M.DecidesInTimeVia e L T) :
    L ∈ DTIME fun n => T n + 1 := by
  obtain ⟨c, M', -, hM'⟩ := FinTM.alphabet_reduction e M
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) T
    (fun x => by simpa using h x)
  exact ⟨c, M', fun x => hM' x⟩

/-- **`P` is alphabet-invariant**: a language decided in polynomial time by a machine
over any finite alphabet is in `P`.

**Proof sketch.** `Complexity.mem_DTIME_of_decidesInTimeVia` gives
`L ∈ DTIME (C · (n + 1) ^ d + 1)`; conclude with `Complexity.mem_P_of_dtime_le`
(pointwise bound `C · (n + 1) ^ d + 1 ≤ (C + 1) · 2 ^ d · (n ^ d + 1)`, using
`(n + 1) ^ d ≤ 2 ^ d (n ^ d + 1)` from the `mem_P_iff` arithmetic). -/
theorem mem_P_of_decidesInTimeVia_poly {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} (C d : ℕ)
    (h : M.DecidesInTimeVia e L fun n => C * (n + 1) ^ d) :
    L ∈ P := by
  have h1 := mem_DTIME_of_decidesInTimeVia e h
  refine mem_P_of_dtime_le h1 ((C + 1) * 2 ^ d) d fun n => ?_
  have h2 : 0 < (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos _)
  calc C * (n + 1) ^ d + 1
      ≤ C * (n + 1) ^ d + (n + 1) ^ d := Nat.add_le_add_left h2 _
    _ = (C + 1) * (n + 1) ^ d := by ring
    _ ≤ (C + 1) * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul (le_refl _) (succ_pow_le n d)
    _ = (C + 1) * 2 ^ d * (n ^ d + 1) := by ring

/-- **`P` is tape-count-invariant**: `P` is exactly the class of languages decided by
binary machines with a *single* work tape in polynomial time. [AB09, Claim 1.6 at the
level of `P`; quadratic slowdown preserves polynomiality]

**Proof sketch.** Backward: a one-work-tape polynomial decider is in particular a
polynomial decider (`Complexity.mem_P_iff`). Forward: from `mem_P_iff` take a decider
within `C · (n + 1) ^ d`; `DecidesInTime` is `ComputesFunInTime` for
`x ↦ [indicator L x]`, so `Turing.FinTM.one_work_tape_binary` yields a one-work-tape
binary machine within `c · (C · (n + 1) ^ d + 1)² ≤ C' · (n + 1) ^ (2d)`, again of the
`mem_P_iff` shape. -/
theorem mem_P_iff_one_work_tape {L : Language Bool} :
    L ∈ P ↔ ∃ (M : FinTM Bool) (C d : ℕ),
      M.k = 1 ∧ M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp hL
    obtain ⟨M', c, hk, hM'⟩ := FinTM.one_work_tape_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
      (fun n => C * (n + 1) ^ d) hM
    refine ⟨M', c * (C + 1) ^ 2, d * 2, hk, fun x => (hM' x).mono ?_⟩
    have h2 : 0 < (x.length + 1) ^ d := Nat.pow_pos (Nat.succ_pos _)
    calc c * (C * (x.length + 1) ^ d + 1) ^ 2
        ≤ c * ((C + 1) * (x.length + 1) ^ d) ^ 2 := by
          refine Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left ?_ 2)
          calc C * (x.length + 1) ^ d + 1
              ≤ C * (x.length + 1) ^ d + (x.length + 1) ^ d :=
                Nat.add_le_add_left h2 _
            _ = (C + 1) * (x.length + 1) ^ d := by ring
      _ = c * (C + 1) ^ 2 * ((x.length + 1) ^ d) ^ 2 := by ring
      _ = c * (C + 1) ^ 2 * (x.length + 1) ^ (d * 2) := by rw [pow_mul]
  · rintro ⟨M, C, d, -, hM⟩
    exact mem_P_iff.mpr ⟨C, d, M, hM⟩

end Complexity
```
