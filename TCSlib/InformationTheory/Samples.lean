/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expectations and independent samples

Two operations on finite distributions that sampling arguments need: the expectation of a
real-valued function, and the distribution of `m` independent samples. With them, a probability
`probTrue` is the expectation of an indicator, and an expectation over a product distribution is
an iterated expectation.

## Main definitions

* `FinDist.expect p f`: the expectation `E_{a ← p}[f a] = ∑ a, p a · f a`.
* `FinDist.iid p m`: `m` independent samples of `p`, a distribution on `Fin m → α`.

## Main results

* `FinDist.probTrue_eq_expect`: a probability is the expectation of an indicator.
* `FinDist.expect_prod`: an expectation over a product distribution is an iterated expectation.
* `FinDist.expect_le_expect`, `FinDist.expect_const`, `FinDist.expect_add`,
  `FinDist.expect_const_mul`, `FinDist.expect_one_sub`: linearity and monotonicity.
* `FinDist.probTrue_not`: the complement rule `Pr[¬D] = 1 − Pr[D]`.
* `FinDist.expect_le_add_of_le_one`: a function with values at most `1` has expectation at most
  `ε + Pr[f > ε]`, for `ε ≥ 0`.

## References

* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, §2.3.1 (product sampling) and §3.1,
  Definition 3.1 (i.i.d. examples).
-/

namespace TCSlib.InformationTheory

open Finset

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Expectation -/

/-- The **expectation** `E_{a ← p}[f a] = ∑ a, p a · f a`. -/
noncomputable def expect (p : FinDist α) (f : α → ℝ) : ℝ := ∑ a, p.prob a * f a

/-- The expectation as a weighted sum: `E_{a ← p}[f a] = ∑ a, p a · f a`. -/
theorem expect_eq (p : FinDist α) (f : α → ℝ) : p.expect f = ∑ a, p.prob a * f a := rfl

/-- The expectation of a constant is the constant: `E_p[c] = c`. -/
theorem expect_const (p : FinDist α) (c : ℝ) : p.expect (fun _ => c) = c := by
  rw [expect_eq, ← Finset.sum_mul, p.sum_prob, one_mul]

/-- The expectation is additive: `E_p[f + g] = E_p[f] + E_p[g]`. -/
theorem expect_add (p : FinDist α) (f g : α → ℝ) :
    p.expect (fun a => f a + g a) = p.expect f + p.expect g := by
  simp only [expect_eq, mul_add, Finset.sum_add_distrib]

/-- The expectation commutes with scaling: `E_p[c · f] = c · E_p[f]`. -/
theorem expect_const_mul (p : FinDist α) (c : ℝ) (f : α → ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  simp only [expect_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The expectation of `1 − f` is `1 − E_p[f]`. -/
theorem expect_one_sub (p : FinDist α) (f : α → ℝ) :
    p.expect (fun a => 1 - f a) = 1 - p.expect f := by
  simp only [expect_eq, mul_sub, mul_one, Finset.sum_sub_distrib, p.sum_prob]

/-- The expectation is monotone: `f ≤ g` pointwise gives `E_p[f] ≤ E_p[g]`. -/
theorem expect_le_expect (p : FinDist α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (p : FinDist α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ p.expect f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (h a)

/-- **A probability is the expectation of an indicator**:
`Pr_{a ← p}[D a] = E_{a ← p}[1_{D a}]`. -/
theorem probTrue_eq_expect (p : FinDist α) (D : α → Bool) :
    p.probTrue D = p.expect (fun a => if D a = true then 1 else 0) := by
  rw [probTrue_eq, expect_eq, Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp

/-- **The complement rule**: `Pr_p[¬D] = 1 − Pr_p[D]`. -/
theorem probTrue_not (p : FinDist α) (D : α → Bool) :
    p.probTrue (fun a => !D a) = 1 - p.probTrue D := by
  rw [probTrue_eq_expect, probTrue_eq_expect, ← expect_one_sub]
  congr 1
  funext a
  cases D a <;> simp

/-- The probability of the always-accepting test is `1`. -/
theorem probTrue_true (p : FinDist α) : p.probTrue (fun _ => true) = 1 := by
  rw [probTrue_eq_expect]
  simpa using p.expect_const 1

/-- **Iterated expectation over a product**:
`E_{(a, b) ← p × q}[f (a, b)] = E_{a ← p}[E_{b ← q}[f (a, b)]]`. -/
theorem expect_prod (p : FinDist α) (q : FinDist β) (f : α × β → ℝ) :
    (p.prod q).expect f = p.expect (fun a => q.expect (fun b => f (a, b))) := by
  simp only [expect_eq, Fintype.sum_prod_type, prod_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **A function with values at most `1` has expectation at most `ε + Pr[f > ε]`**, for
`ε ≥ 0`: on the event `f ≤ ε` it contributes at most `ε`, elsewhere at most `1`. No lower bound
on `f` is needed.

**Proof sketch.** Pointwise `f a ≤ ε + 1_{f a > ε}`, since `f a ≤ 1` and `ε ≥ 0`; take expectations
(`expect_le_expect`, `expect_add`, `expect_const`, `probTrue_eq_expect`). -/
theorem expect_le_add_of_le_one (p : FinDist α) {f : α → ℝ} (hf : ∀ a, f a ≤ 1) {ε : ℝ}
    (hε : 0 ≤ ε) :
    p.expect f ≤ ε + p.probTrue (fun a => !decide (f a ≤ ε)) := by
  have key : ∀ a, f a ≤ ε + (if (!decide (f a ≤ ε)) = true then 1 else 0) := by
    intro a
    by_cases h : f a ≤ ε
    · simp [h]
    · simp [h]
      linarith [hf a]
  calc p.expect f
      ≤ p.expect (fun a => ε + (if (!decide (f a ≤ ε)) = true then 1 else 0)) :=
        p.expect_le_expect key
    _ = ε + p.probTrue (fun a => !decide (f a ≤ ε)) := by
        rw [expect_add p (fun _ => ε), expect_const, probTrue_eq_expect]

/-! ### Independent samples -/

/-- **`m` independent samples** of `p`: the distribution on `Fin m → α` with
`Pr[s] = ∏ j, p (s j)`: the product sampling of [SSBD14, §2.3.1], used for the i.i.d. examples
of [SSBD14, §3.1, Def 3.1]. -/
def iid (p : FinDist α) (m : ℕ) : FinDist (Fin m → α) where
  prob s := ∏ j, p.prob (s j)
  nonneg s := Finset.prod_nonneg fun j _ => p.nonneg (s j)
  sum_prob := by
    have h := Finset.prod_univ_sum (fun _ : Fin m => (univ : Finset α)) (fun _ a => p.prob a)
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    simp only [p.sum_prob, Finset.prod_const_one]

/-- The probability of a sample is the product of the probabilities of its entries:
`Pr_{p^m}[s] = ∏ j, p (s j)`. -/
theorem iid_apply (p : FinDist α) (m : ℕ) (s : Fin m → α) :
    (p.iid m).prob s = ∏ j, p.prob (s j) := rfl

end FinDist

end TCSlib.InformationTheory
