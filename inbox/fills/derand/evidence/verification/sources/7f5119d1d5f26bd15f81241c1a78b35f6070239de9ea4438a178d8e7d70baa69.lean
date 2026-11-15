/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyTableauCorrect
import TCSlib.Complexity.CircuitComplexity.UHaltMachine
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.TMSAT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `P ⊆ P/poly`

[AB09, Thm 6.6]: every language decidable in polynomial time has polynomial-size
circuits.  Following the book, a polynomial-time machine is first made oblivious
([AB09, Remark 1.7]; here `Complexity.oblivious_of_mem_DTIME`, quadratic overhead), and the
oblivious machine is then simulated by its tableau circuit
(`Complexity.tableauCircuit`, `CircuitComplexity/PSubsetPPolyTableau.lean`), one
constant-size gadget per time step.

## Main results

* `Complexity.P_subset_PPoly` — `P ⊆ P/poly`.  [AB09, Thm 6.6]
* `Complexity.P_ssubset_PPoly` — `P ⊊ P/poly`.  [AB09, p. 110]
* `Complexity.P_ne_NP_of_not_NP_subset_PPoly` — if `NP ⊄ P/poly` then `P ≠ NP`.
  [AB09, §6.5, p. 115]

## Divergences from [AB09, Thm 6.6]

* **No divergence in the route.** The book's proof (p. 109) makes `M` oblivious in time
  `O(T(n)²)` by Remark 1.7, remarking that `O(T(n) log T(n))` is possible "if we are more
  careful", and then builds an `O(T')`-size circuit for the oblivious `T'`-time machine —
  so its circuits have size `O(T(n)²)`.  The library follows exactly this route: the
  oblivious simulation `Complexity.oblivious_of_mem_DTIME` is quadratic, and the circuits
  here have size `O((T(n) + 1)²)`.  The sharper `O(T log T)` simulation (a Chapter 1
  parenthetical) is not formalized; for `P ⊆ P/poly` only polynomiality matters.
* `P` is `⋃_c DTIME(n^c + 1)` and `P/poly` uses size bounds `a (n + 1)^k` (see
  `Complexity.P` and `Language.InPPoly` for these two `n = 0` repairs).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6, pp. 109–110; §6.5, p. 115.)
-/

namespace Complexity

open Turing BoolCircuit

/-- The size arithmetic of `P ⊆ P/poly`: for `R = (n + 1)^(d + 1)`, a tableau of width `W`
run for `c (T n + 1)²` steps with `T n = (C + 1) R` has
`n + 2 + (c ((C + 1) R + 1)² + 1) W ≤ (2 + W + c (C + 2)² W) R²` vertices, using
`(C + 1) R + 1 ≤ (C + 2) R` and `n + 2 ≤ 2 R²`. -/
private theorem tableau_size_le (W c C d n : ℕ) :
    n + 2 + (c * ((C + 1) * (n + 1) ^ (d + 1) + 1) ^ 2 + 1) * W ≤
      (2 + W + c * (C + 2) ^ 2 * W) * (n + 1) ^ (2 * (d + 1)) := by
  set P := (n + 1) ^ (d + 1) with hP
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hnP : n + 1 ≤ P := Nat.le_self_pow (Nat.succ_ne_zero d) (n + 1)
  have hT1 : (C + 1) * P + 1 ≤ (C + 2) * P := by nlinarith
  have hsq : ((C + 1) * P + 1) ^ 2 ≤ (C + 2) ^ 2 * P ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hT1 2
  have hPP : P ≤ P ^ 2 := by nlinarith
  have hpow : (n + 1) ^ (2 * (d + 1)) = P ^ 2 := by rw [hP, ← pow_mul, Nat.mul_comm]
  rw [hpow]
  have h1 : c * ((C + 1) * P + 1) ^ 2 ≤ c * (C + 2) ^ 2 * P ^ 2 := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left c hsq
  have h2 : (c * ((C + 1) * P + 1) ^ 2 + 1) * W ≤ (c * (C + 2) ^ 2 * P ^ 2 + P ^ 2) * W :=
    Nat.mul_le_mul_right W (by omega)
  nlinarith

/-- **`P ⊆ P/poly`** [AB09, Thm 6.6]: every language decidable in polynomial time is
decided by a polynomial-size family of fan-in-two circuits.

**Proof sketch.** Let `L` be decided within `C (n + 1)^d` steps.  The bound
`T n = (C + 1)(n + 1)^(d + 1)` dominates it and is time constructible
(`Complexity.timeConstructible_poly`), so `L ∈ DTIME(T)` is decided by an *oblivious*
machine `M` within `T' n = c (T n + 1)²` steps (`Complexity.oblivious_of_mem_DTIME`).
The tableau circuit of `M` for length `n` and budget `T' n` decides `L` on length-`n`
inputs (`Complexity.tableauCircuit_eval_of_decidesInTime`), has fan-in two, and has
`n + 2 + (T' n + 1) · W_M` vertices, which is at most a constant times
`(n + 1)^(2(d + 1))`. -/
theorem P_subset_PPoly : P ⊆ BoolCircuit.PPoly := by
  intro L hL
  obtain ⟨C, d, M₀, hM₀⟩ := mem_P_iff.mp hL
  have hTC := timeConstructible_poly (C + 1) d (Nat.succ_pos C)
  have hLT : L ∈ DTIME fun n => (C + 1) * (n + 1) ^ (d + 1) := by
    refine ⟨1, M₀, fun x => (hM₀ x).mono ?_⟩
    have : (x.length + 1) ^ d ≤ (x.length + 1) ^ (d + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ d)
    show C * (x.length + 1) ^ d ≤ 1 * ((C + 1) * (x.length + 1) ^ (d + 1))
    rw [Nat.one_mul]
    exact Nat.mul_le_mul (Nat.le_succ C) this
  obtain ⟨M, c, hobl, hdec⟩ := oblivious_of_mem_DTIME hTC hLT
  set T' : ℕ → ℕ := fun n => c * ((C + 1) * (n + 1) ^ (d + 1) + 1) ^ 2
  refine ⟨2 + tableauWidth M + c * (C + 2) ^ 2 * tableauWidth M, 2 * (d + 1),
    ⟨fun n => tableauCircuit M n (T' n)⟩, fun n => tableauCircuit_isFaninTwo M n (T' n),
    fun n => ?_, ?_⟩
  · rw [tableauCircuit_size]
    exact tableau_size_le _ _ _ _ n
  · ext w
    simp only [DAGCircuitFamily.mem_language_iff]
    rw [tableauCircuit_eval_of_decidesInTime hobl hdec, List.ofFn_get]
    unfold MultiTapeTM.indicator
    split_ifs with h <;> simp [h]

/-- **`NP ⊄ P/poly` implies `P ≠ NP`** [AB09, §6.5, p. 115: "Since P ⊆ P/poly, if we ever
prove NP ⊄ P/poly, then we will have shown P ≠ NP"]: immediate from `P ⊆ P/poly`. -/
theorem P_ne_NP_of_not_NP_subset_PPoly (h : ¬ (NP ⊆ BoolCircuit.PPoly)) : P ≠ NP :=
  fun hPNP => h (hPNP ▸ P_subset_PPoly)

/-- **`P ⊊ P/poly`** [AB09, p. 110]: `P ⊆ P/poly` (Thm 6.6), and the inclusion is strict,
`P/poly` containing the undecidable unary language `UHALT`
(`Complexity.P_ssubset_PPoly_of_subset`, `CircuitComplexity/UHaltMachine.lean`). -/
theorem P_ssubset_PPoly : P ⊂ BoolCircuit.PPoly :=
  P_ssubset_PPoly_of_subset P_subset_PPoly

end Complexity
