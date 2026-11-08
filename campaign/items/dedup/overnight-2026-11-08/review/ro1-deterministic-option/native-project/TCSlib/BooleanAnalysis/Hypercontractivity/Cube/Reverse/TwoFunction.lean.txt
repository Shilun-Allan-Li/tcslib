/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Extension

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two-function reverse hypercontractivity

One stage of Borell's reverse Bonami–Beckner argument, retaining the extended-mean conventions.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `reverse_bonami_beckner_two_function`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercises 10.6–10.9.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

attribute [local simp] BooleanAnalysis.Hypercontractivity.cubeLpNorm

/-- Extended power means of a nonnegative function are nondecreasing in their exponent
up to one. [OD14, Exs. 10.6--10.9, extended-mean calculus]

**Proof sketch.** Jensen's inequality for powers compares exponents of the same sign.
Concavity of the logarithm compares either side with the geometric mean at zero.
If a function has a zero, use the stipulated zero value of its nonpositive means. -/
private lemma lpMean_exponent_mono (a b : ℝ) (hab : a ≤ b) (hb : b ≤ 1)
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean a f ≤ lpMean b f := by
  have lpMean_nonneg_all (p : ℝ) (f : BooleanFunc n) : 0 ≤ lpMean p f := by
    unfold lpMean
    split_ifs
    · exact le_rfl
    · positivity
    · exact Real.rpow_nonneg (by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg (f x)) p) _
  have expect_pos_of_pos (f : BooleanFunc n) (hf : ∀ x, 0 < f x) : 0 < expect f := by
    unfold expect uniformWeight
    exact mul_pos (pow_pos (by norm_num) _)
      (Finset.sum_pos (fun x _ ↦ hf x) Finset.univ_nonempty)
  have expect_rpow_jensen (t : ℝ) (ht : 1 ≤ t)
      (f : BooleanFunc n) (hf : ∀ x, 0 ≤ f x) :
      (expect f) ^ t ≤ expect (fun x ↦ f x ^ t) := by
    unfold expect
    have hw : ∑ _x : BoolCube n, uniformWeight n = 1 := by
      unfold uniformWeight
      simp [Finset.card_univ]
    have h := Real.rpow_arith_mean_le_arith_mean_rpow
      (Finset.univ : Finset (BoolCube n)) (fun _ ↦ uniformWeight n) f
      (fun _ _ ↦ pow_nonneg (by norm_num) _) hw (fun x _ ↦ hf x) ht
    simpa only [← Finset.mul_sum] using h
  have expect_log_le_log_expect (f : BooleanFunc n) (hf : ∀ x, 0 < f x) :
      expect (fun x ↦ Real.log (f x)) ≤ Real.log (expect f) := by
    unfold expect
    have hw : ∑ _x : BoolCube n, uniformWeight n = 1 := by
      unfold uniformWeight
      simp [Finset.card_univ]
    have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := (Finset.univ : Finset (BoolCube n))) (w := fun _ ↦ uniformWeight n) (p := f)
      (fun _ _ ↦ pow_nonneg (by norm_num) _) hw (fun x _ ↦ hf x)
    simpa only [smul_eq_mul, ← Finset.mul_sum] using h
  have lpMean_mono_pos_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
      (f : BooleanFunc n) (hf : IsNonnegative f) : lpMean a f ≤ lpMean b f := by
    have hb : 0 < b := lt_of_lt_of_le ha hab
    rw [lpMean_of_pos a ha, lpMean_of_pos b hb]
    simp_rw [abs_of_nonneg (hf _)]
    have hA : 0 ≤ expect (fun x ↦ f x ^ a) :=
      by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hf x) a
    have hB : 0 ≤ expect (fun x ↦ f x ^ b) :=
      by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hf x) b
    have hratio : 1 ≤ b / a := by
      apply (le_div_iff₀ ha).2
      simpa using hab
    have hJ := expect_rpow_jensen (b / a) hratio (fun x ↦ f x ^ a)
      (fun x ↦ Real.rpow_nonneg (hf x) a)
    simp_rw [← Real.rpow_mul (hf _)] at hJ
    have hab' : a * (b / a) = b := by field_simp
    rw [hab'] at hJ
    rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _) hb]
    rw [← Real.rpow_mul hA, ← Real.rpow_mul hB]
    have hleft : 1 / a * b = b / a := by field_simp
    have hright : 1 / b * b = 1 := by field_simp
    rw [hleft, hright, Real.rpow_one]
    exact hJ
  have lpMean_mono_neg_exp {a b : ℝ} (ha : a < 0) (hab : a ≤ b) (hb : b < 0)
      (f : BooleanFunc n) (hf : IsNonnegative f) : lpMean a f ≤ lpMean b f := by
    by_cases hz : ∃ x, f x = 0
    · simp only [lpMean, hz, true_and, if_pos ha.le, if_pos hb.le]
      exact le_rfl
    · have hfpos : ∀ x, 0 < f x :=
        fun x ↦ lt_of_le_of_ne (hf x) (Ne.symm (not_exists.mp hz x))
      simp only [lpMean, hz, false_and, if_false, if_neg ha.ne, if_neg hb.ne,
        BooleanAnalysis.Hypercontractivity.cubeLpNorm]
      simp_rw [abs_of_pos (hfpos _)]
      have hA : 0 < expect (fun x ↦ f x ^ a) :=
        expect_pos_of_pos _ fun x ↦ Real.rpow_pos_of_pos (hfpos x) a
      have hB : 0 < expect (fun x ↦ f x ^ b) :=
        expect_pos_of_pos _ fun x ↦ Real.rpow_pos_of_pos (hfpos x) b
      have hratio : 1 ≤ a / b := by
        rw [le_div_iff_of_neg hb]
        nlinarith
      have hJ := expect_rpow_jensen (a / b) hratio (fun x ↦ f x ^ b)
        (fun x ↦ Real.rpow_nonneg (hf x) b)
      simp_rw [← Real.rpow_mul (hf _)] at hJ
      have hab' : b * (a / b) = a := by field_simp [hb.ne]
      rw [hab'] at hJ
      rw [← Real.rpow_le_rpow_iff_of_neg
        (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hA _) ha]
      rw [← Real.rpow_mul hB.le, ← Real.rpow_mul hA.le]
      have hleft : 1 / b * a = a / b := by field_simp
      have hright : 1 / a * a = 1 := by field_simp [ha.ne]
      rw [hleft, hright, Real.rpow_one]
      exact hJ
  have lpMean_neg_le_zero {a : ℝ} (ha : a < 0)
      (f : BooleanFunc n) (hf : IsNonnegative f) :
      lpMean a f ≤ lpMean 0 f := by
    by_cases hz : ∃ x, f x = 0
    · simp [lpMean, hz, ha.le]
    · have hfpos : ∀ x, 0 < f x :=
        fun x ↦ lt_of_le_of_ne (hf x) (Ne.symm (not_exists.mp hz x))
      rw [show lpMean a f = (expect (fun x ↦ f x ^ a)) ^ (1 / a) by
        simp [lpMean, hz, ha.ne, abs_of_pos (hfpos _)],
        show lpMean 0 f = Real.exp (expect (fun x ↦ Real.log (f x))) by
          simp [lpMean, hz, abs_of_pos (hfpos _)]]
      have hA : 0 < expect (fun x ↦ f x ^ a) :=
        expect_pos_of_pos _ fun x ↦ Real.rpow_pos_of_pos (hfpos x) a
      rw [Real.rpow_def_of_pos hA]
      apply Real.exp_le_exp.mpr
      have hJ := expect_log_le_log_expect (fun x ↦ f x ^ a)
        (fun x ↦ Real.rpow_pos_of_pos (hfpos x) a)
      simp_rw [Real.log_rpow (hfpos _)] at hJ
      have hJ' : a * expect (fun x ↦ Real.log (f x)) ≤
          Real.log (expect (fun x ↦ f x ^ a)) := by
        convert hJ using 1
        unfold expect
        rw [← Finset.mul_sum]
        ring
      calc
        Real.log (expect (fun x ↦ f x ^ a)) * (1 / a) =
            Real.log (expect (fun x ↦ f x ^ a)) / a := by ring_nf
        _ ≤ expect (fun x ↦ Real.log (f x)) :=
          (div_le_iff_of_neg ha).2 (by simpa [mul_comm] using hJ')
  have lpMean_zero_le_pos {b : ℝ} (hb : 0 < b)
      (f : BooleanFunc n) (hf : IsNonnegative f) :
      lpMean 0 f ≤ lpMean b f := by
    by_cases hz : ∃ x, f x = 0
    · have hzero : lpMean 0 f = 0 := by simp [lpMean, hz]
      rw [hzero]
      exact lpMean_nonneg_all b f
    · have hfpos : ∀ x, 0 < f x :=
        fun x ↦ lt_of_le_of_ne (hf x) (Ne.symm (not_exists.mp hz x))
      rw [show lpMean 0 f = Real.exp (expect (fun x ↦ Real.log (f x))) by
        simp [lpMean, hz, abs_of_pos (hfpos _)],
        lpMean_of_pos b hb]
      simp_rw [abs_of_pos (hfpos _)]
      have hB : 0 < expect (fun x ↦ f x ^ b) :=
        expect_pos_of_pos _ fun x ↦ Real.rpow_pos_of_pos (hfpos x) b
      rw [Real.rpow_def_of_pos hB]
      apply Real.exp_le_exp.mpr
      have hJ := expect_log_le_log_expect (fun x ↦ f x ^ b)
        (fun x ↦ Real.rpow_pos_of_pos (hfpos x) b)
      simp_rw [Real.log_rpow (hfpos _)] at hJ
      have hJ' : b * expect (fun x ↦ Real.log (f x)) ≤
          Real.log (expect (fun x ↦ f x ^ b)) := by
        convert hJ using 1
        unfold expect
        rw [← Finset.mul_sum]
        ring
      calc
        expect (fun x ↦ Real.log (f x)) ≤
            Real.log (expect (fun x ↦ f x ^ b)) / b :=
          (le_div_iff₀ hb).2 (by simpa [mul_comm] using hJ')
        _ = Real.log (expect (fun x ↦ f x ^ b)) * (1 / b) := by ring_nf
  rcases lt_trichotomy b 0 with hbneg | hbzero | hbpos
  · exact lpMean_mono_neg_exp (lt_of_le_of_lt hab hbneg) hab hbneg f hf
  · subst b
    rcases lt_or_eq_of_le hab with haneg | ha0
    · exact lpMean_neg_le_zero haneg f hf
    · subst a
      exact le_rfl
  · rcases lt_trichotomy a 0 with haneg | hazero | hapos
    · exact (lpMean_neg_le_zero haneg f hf).trans (lpMean_zero_le_pos hbpos f hf)
    · subst a
      exact lpMean_zero_le_pos hbpos f hf
    · exact lpMean_mono_pos_exp hapos hab f hf

/-- The two-function form gives `E[f(x)g(y)] ≥ ‖f‖_p ‖g‖_q` for nonnegative
functions on correlated Boolean strings and finite `p,q < 1`.
The source also permits an exponent of one at correlation zero; those endpoint cases
and infinite exponents are not represented by this declaration.

**Source:** [OD14, Exs. 10.6--10.9].

**Proof sketch.** For p ≠ 0, combine reverse Hölder at p with one-function reverse
hypercontractivity at d = 1 − ρ²/(1 − p); the correlation restriction gives q ≤ d, so mean
monotonicity completes the bound. If p = 0 ≠ q, interchange the functions by self-adjointness.
If both exponents vanish, use geometric-mean multiplicativity, its expectation bound, and the
zero-exponent noise estimate, treating zeros by the stipulated convention.
-/
theorem reverse_bonami_beckner_two_function (p q ρ : ℝ)
    (hp : p < 1) (hq : q < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ (1 - p) * (1 - q))
    (f g : BooleanFunc n) (hf : IsNonnegative f) (hg : IsNonnegative g) :
    innerProduct f (noiseOp ρ g) ≥ lpMean p f * lpMean q g := by
  have lpMean_nonneg_all (r : ℝ) (u : BooleanFunc n) : 0 ≤ lpMean r u := by
    unfold lpMean
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
    · exact Real.rpow_nonneg (by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg _) _) _
  have lpMean_zero_le_expect (u : BooleanFunc n) (hu : IsNonnegative u) :
      lpMean 0 u ≤ expect u := by
    convert lpMean_exponent_mono 0 1 (by norm_num) le_rfl u hu using 1
    rw [lpMean_of_pos 1 zero_lt_one]
    simp [abs_of_nonneg (hu _)]
  have reverse_holder_zero (u v : BooleanFunc n) (hu : IsNonnegative u)
      (hv : IsNonnegative v) :
      innerProduct u v ≥ lpMean 0 u * lpMean 0 v := by
    classical
    by_cases huzero : ∃ x, u x = 0
    · rw [show lpMean 0 u = 0 by simp [lpMean, huzero], zero_mul]
      unfold innerProduct
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ mul_nonneg (hu x) (hv x)
    · by_cases hvzero : ∃ x, v x = 0
      · rw [show lpMean 0 v = 0 by simp [lpMean, hvzero], mul_zero]
        unfold innerProduct
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ mul_nonneg (hu x) (hv x)
      · have hupos : ∀ x, 0 < u x := fun x ↦
            (hu x).lt_of_ne (Ne.symm (not_exists.mp huzero x))
        have hvpos : ∀ x, 0 < v x := fun x ↦
            (hv x).lt_of_ne (Ne.symm (not_exists.mp hvzero x))
        have hprodpos : IsNonnegative (fun x ↦ u x * v x) :=
          fun x ↦ mul_nonneg (hu x) (hv x)
        have hprodzero : ¬∃ x, u x * v x = 0 := by
          push_neg
          exact fun x ↦ mul_ne_zero (hupos x).ne' (hvpos x).ne'
        have hmul : lpMean 0 (fun x ↦ u x * v x) = lpMean 0 u * lpMean 0 v := by
          rw [show lpMean 0 (fun x ↦ u x * v x) =
              Real.exp (expect (fun x ↦ Real.log (u x * v x))) by
            unfold lpMean
            rw [if_neg (by simpa using hprodzero), if_pos rfl]
            simp_rw [abs_of_pos (mul_pos (hupos _) (hvpos _))]]
          rw [show lpMean 0 u = Real.exp (expect (fun x ↦ Real.log (u x))) by
            simp [lpMean, huzero, abs_of_pos (hupos _)]]
          rw [show lpMean 0 v = Real.exp (expect (fun x ↦ Real.log (v x))) by
            simp [lpMean, hvzero, abs_of_pos (hvpos _)]]
          simp_rw [Real.log_mul (hupos _).ne' (hvpos _).ne']
          unfold expect
          rw [Finset.sum_add_distrib, mul_add, Real.exp_add]
        rw [← hmul]
        exact lpMean_zero_le_expect (fun x ↦ u x * v x) hprodpos
  have two_function_core : ∀ (a b R : ℝ), a < 1 → a ≠ 0 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ (1 - a) * (1 - b) →
      ∀ (u v : BooleanFunc n), IsNonnegative u → IsNonnegative v →
        innerProduct u (noiseOp R v) ≥ lpMean a u * lpMean b v := by
    intro a b R ha ha0 hR0 hR1 hRsq u v hu hv
    let c := a / (a - 1)
    let d := 1 - R ^ 2 / (1 - a)
    have h1a : 0 < 1 - a := sub_pos.mpr ha
    have ham1 : a - 1 ≠ 0 := (sub_neg.mpr ha).ne
    have hc1 : c < 1 := by
      dsimp [c]
      rw [div_lt_iff_of_neg (sub_neg.mpr ha)]
      linarith
    have hconj : 1 - c = 1 / (1 - a) := by
      dsimp [c]
      field_simp [h1a.ne', ham1]
      ring
    have hRsq1 : R ^ 2 ≤ 1 := by nlinarith
    have hbd : b ≤ d := by
      have hdiv : R ^ 2 / (1 - a) ≤ 1 - b := by
        rw [div_le_iff₀ h1a]
        simpa [mul_comm] using hRsq
      dsimp [d]
      linarith
    have hd1 : d ≤ 1 := by
      dsimp [d]
      exact sub_le_self 1 (div_nonneg (sq_nonneg R) h1a.le)
    have hcd : c ≤ d := by
      rw [show c = 1 - 1 / (1 - a) by linarith [hconj]]
      dsimp [d]
      have := div_le_div_of_nonneg_right hRsq1 h1a.le
      linarith
    have hratio : (1 - d) / (1 - c) = R ^ 2 := by
      rw [hconj]
      dsimp [d]
      field_simp [h1a.ne']
      ring
    have hholder := reverse_holder a ha ha0 u (noiseOp R v) hu
      (noiseOp_nonneg hR0 hR1 hv)
    have hbb := reverse_bonami_beckner d c R hc1 hcd hd1 hR0 hR1
      (by rw [hratio]) v hv
    have hmean : lpMean c (noiseOp R v) ≥ lpMean b v :=
      (lpMean_exponent_mono b d hbd hd1 v hv).trans hbb
    exact (mul_le_mul_of_nonneg_left hmean (lpMean_nonneg_all a u)).trans hholder
  by_cases hp0 : p = 0
  · by_cases hq0 : q = 0
    · subst p
      subst q
      have hhold :=
        reverse_holder_zero f (noiseOp ρ g) hf (noiseOp_nonneg hρ0 hρ1 hg)
      have hcorr : ρ ^ 2 ≤ (1 - (0 : ℝ)) / (1 - (0 : ℝ)) := by
        norm_num
        simpa using hρsq
      have hbb := reverse_bonami_beckner 0 0 ρ (by norm_num) le_rfl (by norm_num)
        hρ0 hρ1 hcorr g hg
      exact (mul_le_mul_of_nonneg_left hbb (lpMean_nonneg_all 0 f)).trans hhold
    · subst p
      calc
        lpMean 0 f * lpMean q g = lpMean q g * lpMean 0 f := mul_comm _ _
        _ ≤ innerProduct g (noiseOp ρ f) := two_function_core q 0 ρ hq hq0 hρ0 hρ1
          (by simpa [mul_comm] using hρsq) g f hg hf
        _ = innerProduct f (noiseOp ρ g) := by
          rw [innerProduct_comm, noiseOp_self_adjoint]
  · exact two_function_core p q ρ hp hp0 hρ0 hρ1 hρsq f g hf hg

end BooleanAnalysis.Hypercontractivity
