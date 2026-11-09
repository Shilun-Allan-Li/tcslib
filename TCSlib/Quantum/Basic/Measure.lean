/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Quantum.Basic.ApplyOn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Measurement in the computational basis

The Born rule [dW26, §1.2.2]: measuring a state `ψ` in its basis gives outcome `x` with
probability `‖ψ x‖²`. Measuring one wire `i` of a register gives `b` with the total probability
of the basis states whose wire `i` holds `b`.

## Main definitions

* `Quantum.Ket.prob ψ x` — the probability of outcome `x` when `ψ` is measured.
* `Quantum.Ket.probQubit ψ i b` — the probability that measuring wire `i` gives `b`.

## Main results

* `Quantum.Ket.sum_prob` — outcome probabilities sum to `1`.
* `Quantum.Ket.probQubit_zero_add_one` — the two outcomes of a one-wire measurement have total
  probability `1`.
* `Quantum.Ket.probQubit_basis` — measuring a wire of a basis state is deterministic.
* `Quantum.Ket.probQubit_evolve_applyOnU_of_forall_ne` — a gate on other wires does not change
  the statistics of wire `i`.

## References

* [dW26] R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415, version 6 (2026).
* [NC10] M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, 10th
  anniversary edition, Cambridge University Press, 2010.
-/

noncomputable section

namespace Quantum

open Matrix

namespace Ket

variable {d : Type*} [Fintype d] {k n : ℕ}

/-- The Born rule: measuring `ψ` in its basis gives outcome `x` with probability `‖ψ x‖²`.
[dW26, §1.2.2] -/
def prob (ψ : Ket d) (x : d) : ℝ := ‖ψ.vec x‖ ^ 2

/-- `ψ.prob x = ‖ψ.vec x‖²`. -/
theorem prob_eq (ψ : Ket d) (x : d) : ψ.prob x = ‖ψ.vec x‖ ^ 2 := rfl

/-- Outcome probabilities are nonnegative.

**Proof sketch.** A square of a real number is nonnegative (`sq_nonneg`). -/
theorem prob_nonneg (ψ : Ket d) (x : d) : 0 ≤ ψ.prob x := by
  rw [prob_eq]
  positivity

/-- Outcome probabilities sum to `1`: this is the normalization of `ψ`. [dW26, §1.2.2] -/
theorem sum_prob (ψ : Ket d) : ∑ x, ψ.prob x = 1 := ψ.normalized'

/-- Each outcome probability is at most `1`.

**Proof sketch.** It is one nonnegative term of a sum equal to `1` (`sum_prob`,
`prob_nonneg`). -/
theorem prob_le_one (ψ : Ket d) (x : d) : ψ.prob x ≤ 1 := by
  rw [← ψ.sum_prob]
  exact Finset.single_le_sum (fun y _ => prob_nonneg ψ y) (Finset.mem_univ x)

/-- The probability that measuring wire `i` of the register state `ψ` gives `b`: the total
probability of the basis states `x` with `x i = b`. [dW26, §1.2.2] -/
def probQubit (ψ : Ket (Reg n)) (i : Fin n) (b : Qubit) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Reg n => x i = b), ψ.prob x

/-- `ψ.probQubit i b` is the sum of `ψ.prob x` over the `x` with `x i = b`. -/
theorem probQubit_eq (ψ : Ket (Reg n)) (i : Fin n) (b : Qubit) :
    ψ.probQubit i b = ∑ x ∈ Finset.univ.filter (fun x : Reg n => x i = b), ψ.prob x := rfl

/-- One-wire measurement probabilities are nonnegative.

**Proof sketch.** A sum of nonnegative terms (`Finset.sum_nonneg`, `prob_nonneg`). -/
theorem probQubit_nonneg (ψ : Ket (Reg n)) (i : Fin n) (b : Qubit) : 0 ≤ ψ.probQubit i b := by
  rw [probQubit_eq]
  exact Finset.sum_nonneg fun y _ => prob_nonneg ψ y

/-- The two outcomes of measuring wire `i` have total probability `1`.

**Proof sketch.** The filters `x i = 0` and `x i = 1` partition `Reg n`
(`Finset.sum_filter_add_sum_filter_not`, with `x i ≠ 0 ↔ x i = 1` in `Fin 2`), and the full
sum is `1` (`sum_prob`). -/
theorem probQubit_zero_add_one (ψ : Ket (Reg n)) (i : Fin n) :
    ψ.probQubit i 0 + ψ.probQubit i 1 = 1 := by
  rw [probQubit_eq, probQubit_eq, ← ψ.sum_prob]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Reg n => x i = 0)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  generalize x i = a
  revert a; decide
example (x : Reg n) (i : Fin n) (b : Qubit) :
    (basis x).probQubit i b = if x i = b then 1 else 0 := by
  rw [probQubit_eq]
  simp [prob_eq, basis_vec, apply_ite, Finset.sum_ite_eq]

/-- Measuring wire `i` of the basis state `|x⟩` gives `x i` with certainty.

**Proof sketch.** `(basis x).prob y` is `1` at `y = x` and `0` elsewhere, so the filtered sum
is `1` if `x i = b` and `0` otherwise. -/
theorem probQubit_basis (x : Reg n) (i : Fin n) (b : Qubit) :
    (basis x).probQubit i b = if x i = b then 1 else 0 := by
  rw [probQubit_eq]
  simp [prob_eq, basis_vec, apply_ite, Finset.sum_ite_eq]

/-- The probability that wire `i` reads `b` is the squared norm of `ψ` projected onto the basis
states with `x i = b`. -/
private theorem probQubit_eq_sum_norm_sq (ψ : Ket (Reg n)) (i : Fin n) (b : Qubit) :
    ψ.probQubit i b = ∑ x, ‖(if x i = b then ψ.vec x else 0)‖ ^ 2 := by
  rw [probQubit_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp [prob_eq]

/-- A gate on wires avoiding `i` commutes with the projection onto "wire `i` reads `b`": it never
changes wire `i`. -/
private theorem applyOn_mulVec_proj (w : Fin k ↪ Fin n) (U : Matrix (Reg k) (Reg k) ℂ) {i : Fin n}
    (hi : ∀ j, w j ≠ i) (b : Qubit) (v : Reg n → ℂ) :
    (fun x => if x i = b then (applyOn w U *ᵥ v) x else 0) =
      applyOn w U *ᵥ (fun x => if x i = b then v x else 0) := by
  funext x
  simp only [mulVec, dotProduct]
  split_ifs with hx
  · refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hA : AgreeOff w x z
    · rw [if_pos (by rw [← hA i hi, hx])]
    · rw [applyOn_apply, if_neg hA, zero_mul, zero_mul]
  · symm
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hA : AgreeOff w x z
    · rw [if_neg (by rw [← hA i hi]; exact hx), mul_zero]
    · rw [applyOn_apply, if_neg hA, zero_mul]

/-- A gate placed on wires that avoid `i` does not change the statistics of measuring wire `i`.
This is what makes measurements of separate registers independent of the gates applied to
the others.

**Proof sketch.** Partition `Reg n` into the classes of `AgreeOff w`: registers equal off the
range of `w`. Wire `i` is off that range, so `x i` is constant on each class, and the event
`x i = b` is a union of classes. `applyOn w U` maps vectors supported on a class into that
same class (`applyOn_mulVec_basis`), where it acts as `U` under the bijection `x ↦ x ∘ w` of
`applyOn_mul`'s sketch. Unitaries preserve squared norms
(`sum_norm_sq_mulVec_of_mem_unitaryGroup`), so each class keeps its total probability. -/
theorem probQubit_evolve_applyOnU_of_forall_ne (ψ : Ket (Reg n)) (w : Fin k ↪ Fin n)
    (U : Gate k) {i : Fin n} (hi : ∀ j, w j ≠ i) (b : Qubit) :
    (ψ.evolve (applyOnU w U)).probQubit i b = ψ.probQubit i b := by
  rw [probQubit_eq_sum_norm_sq, probQubit_eq_sum_norm_sq, evolve_vec, applyOnU_coe]
  calc ∑ x, ‖(if x i = b then (applyOn w (U : Matrix (Reg k) (Reg k) ℂ) *ᵥ ψ.vec) x else 0)‖ ^ 2
      = ∑ x, ‖(applyOn w (U : Matrix (Reg k) (Reg k) ℂ) *ᵥ
          fun x => if x i = b then ψ.vec x else 0) x‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← congrFun (applyOn_mulVec_proj w U hi b ψ.vec) x]
    _ = ∑ x, ‖(if x i = b then ψ.vec x else 0)‖ ^ 2 :=
        sum_norm_sq_mulVec_of_mem_unitaryGroup (applyOn_mem_unitaryGroup w U.2) _

end Ket

end Quantum
