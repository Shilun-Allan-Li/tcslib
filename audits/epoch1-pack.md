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
