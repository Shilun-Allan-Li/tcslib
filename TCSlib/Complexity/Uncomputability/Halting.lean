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
    simp only [r, hMt, hPU, hP.computes.exists_computesInTime_iff,
      hQ.computes.exists_computesInTime_iff, exists_eq_left]
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
