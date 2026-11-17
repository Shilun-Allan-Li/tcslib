# GSW 6a · in-house fill U1 + U2 (draft) · REPORT

Maintainer sub-agent, 2026-11-17, under Seyoon's overnight ruling (in-house small fills, drafts only). Filed by the
maintainer from the sub-agent's returned report: its own write of this file was refused by the harness, which returns
sub-agent reports as text.

## Head
- Branch `fill/gsw-6a-u1-u2` (pushed; **no PR**), head `27948c39bedbea7e7ae2472ea708cc5b4f345069` on the statements
  head `73aedcdaaaffef7e69ab012d9b9195f150bae68d` (#359).
- Commits, each `git commit -S` with the two trailers: `ba5035b5` (U1), `7c9ccae9` (U2), `27948c39` (three private
  inductions replaced by core lemmas). Signature verification is not possible on this host (no `ssh-keygen`).

## Targets: C1–C8, all 16 admitted declarations proved, no `sorry` left
| Target | Declarations (file:line at head) |
|---|---|
| C1 | `yield_append` (Defs:224), `yield_nil` (Defs:236) |
| C2 | `yield_conj` (Defs:256), `length_conj` (Defs:278), `length_append` (Defs:286) |
| C3 | `yield_complementLast` (Defs:299), `length_complementLast` (Defs:317) |
| C4 | `IsPermutation.append` (Defs:335), `.conj` (Defs:347), `.complementLast` (Defs:364), `.bijective_yield` (Defs:399) |
| C5 | `evalWith_nil` (Eval:99), `evalWith_append` (Eval:108) |
| C6 | `Instr.stepWith_of_isPermutation` (Eval:125) |
| C7 | `evalWith_rel` (Eval:155) |
| C8 | `evalWith_single` (Eval:221) |

C4's `isPermutation_iff` was already proved at the base (`Iff.rfl`).

## Helpers (all `private`, no `@[simp]`, each with a formula docstring and a glue note)
| Helper | File:line | Content |
|---|---|---|
| `eval_conjInstr` | Defs:242 | a conjugated instruction yields `θ ∘ ι.eval x ∘ θ.symm` (C2's step) |
| `Instr.bijective_eval` | Defs:385 | an instruction with two bijective maps yields a bijection (C4's step) |
| `sum_filter_single` | Eval:184 | `∑ j ∈ univ.filter (f · = i), Pi.single s 1 j = Pi.single (f s) 1 i` (C8) |
| `stepWith_single` | Eval:200 | one Boolean-host step keeps a one-hot vector one-hot (C8) |

Duplicate search covered `TCSlib/`, Mathlib, Batteries and core `List`. Three private fold inductions were replaced by
`List.foldl_hom`, `List.foldl_map` and `List.foldlRecOn` (commit `27948c39`); C7 keeps its own induction (core's
`List.foldl_rel` is not step-indexed). `sum_filter_single` is a short derivation from Mathlib's `Finset.sum_pi_single'`,
which lives in `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`, not imported by Eval (see Maintainer notes).

No new imports, no heartbeat raise, no `sorry`/`admit`/`native_decide`/new axiom, no `unfold`/`delta`/`show` reads.

## Reader requests
None. Eval reads Defs only through `yield_eq`, `Instr.eval_eq`, `append_instrs`, `length_eq`,
`Instr.isPermutation_iff`, its own `evalWith_eq`/`Instr.stepWith_apply`, and the structure fields.

## Deviations from the frozen sketches (mathematics unchanged; docstrings frozen, so not edited)
- C1, C2, C8 and C4 `bijective_yield`: the sketches' inductions are done by core fold lemmas (in-proof comments say so).
- C3 and C4 `complementLast`: Mathlib's `List.eq_nil_or_concat'` instead of core's `List.eq_nil_or_concat`.
- C6: `Finset.mem_filter`, `Finset.mem_singleton`, `Equiv.apply_eq_iff_eq_symm_apply` instead of `Finset.filter_eq'`.
- C8: `Finset.sum_eq_single_of_mem`/`Finset.sum_eq_zero` instead of `Finset.sum_ite_eq'` (in `Piecewise`).

## Checks (evidence in `$SP/fill12/`)
- **Build** on `$SP/olean-replay-6a-fill12` (`cp -al` of `olean-replay-6a-stmt`), one Lean process at a time, slot
  checked: Defs, Eval, Barrington, BarringtonConverse, NC1, the `BranchingPrograms` and `ComputationalModels` facades and
  root `TCSlib`, all rc 0 with 0 errors; `sorry` warnings 0/0/11/11/5/0/0/0. The 8 rebuilt oleans have link count 1;
  `olean-replay-6a-stmt` unchanged.
- **Admissions:** 98 → 82 over the series (Defs 11 → 0, Eval 5 → 0; others unchanged).
- **Freeze:** the diff `73aedcda..27948c39` touches 2 files (+153/−16); every deleted line is `  sorry`.
- **Axioms:** the 17 C1–C8 declarations and 4 helpers use only `propext`/`Classical.choice`/`Quot.sound`; no `sorryAx`.
- **Rule 10, canonical coe-A:** Defs 0 requests (imports only Mathlib), Eval 25 requests; 0 errors at base and head,
  identical request counts.
- **Lint:** `style_lint` 0 findings; `campaign_style_lint --check8b` 0 FAIL / 0 WARN at base and head.
- **Sizes:** Defs 412 → 489, Eval 172 → 232 lines; no line over 100 characters.

## Notes for Gate 45 (report only)
1. Defs:32 and Eval:34 module docstrings still say the targets are "admitted with `sorry`" (outside proof bodies).
2. Sketch wording is out of step with the proofs, as listed above.
3. No statement problem: all 16 provable as stated. C3's `0 < B.length` is needed (on the empty program the yield is
   `id`, not `σ.symm`, unless `σ = 1`); C7's `hstep` form was easy to use; C8 holds for general maps as claimed.

## Maintainer notes (review pending)
- Given Gate 48's G48-01 (an inline re-derivation of a Mathlib lemma graded major), `sum_filter_single` is being
  replaced by the Mathlib lemma with the needed Mathlib import, and the other three helpers are re-checked against
  Mathlib, before any PR.
