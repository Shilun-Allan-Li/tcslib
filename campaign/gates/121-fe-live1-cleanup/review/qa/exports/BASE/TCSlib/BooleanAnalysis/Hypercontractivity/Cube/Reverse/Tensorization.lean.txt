/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.TwoPoint

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Tensorization and monotonicity for reverse noise

One stage of Borell's reverse Bonami–Beckner argument, retaining the extended-mean conventions.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `reverse_minkowski_mixed`.
* `tensorize_reverse_bonami_beckner`.
* `reverse_bonami_beckner_positive_sharp`.
* `lpMean_noise_antitone`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercises 10.6–10.9.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

attribute [local simp] BooleanAnalysis.Hypercontractivity.cubeLpNorm

/-! ### Tensorization -/

/-- Minkowski's inequality for finite sums with exponent `r ≥ 1`. -/
private lemma finset_Lr_sum_le {ι κ : Type*} [DecidableEq ι] (r : ℝ) (hr : 1 ≤ r)
    (s : Finset ι) (t : Finset κ) (a : ι → κ → ℝ) (ha : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ a i j) :
    (∑ j ∈ t, (∑ i ∈ s, a i j) ^ r) ^ (1 / r) ≤
      ∑ i ∈ s, (∑ j ∈ t, a i j ^ r) ^ (1 / r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hr0.ne', Real.zero_rpow (inv_ne_zero hr0.ne')]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      calc
        (∑ j ∈ t, (a i j + ∑ k ∈ s, a k j) ^ r) ^ (1 / r) ≤
            (∑ j ∈ t, a i j ^ r) ^ (1 / r) + (∑ j ∈ t, (∑ k ∈ s, a k j) ^ r) ^ (1 / r) :=
          Real.Lp_add_le_of_nonneg t hr (fun j hj ↦ ha i (Finset.mem_insert_self i s) j hj)
            (fun j hj ↦ Finset.sum_nonneg fun k hk ↦ ha k (Finset.mem_insert_of_mem hk) j hj)
        _ ≤ (∑ j ∈ t, a i j ^ r) ^ (1 / r) + ∑ k ∈ s, (∑ j ∈ t, a k j ^ r) ^ (1 / r) :=
          add_le_add_left (ih fun k hk j hj ↦ ha k (Finset.mem_insert_of_mem hk) j hj) _

/-- Reverse Minkowski in the mixed-norm form needed to exchange the last bit
with the first `n` bits during tensorization.

**Source:** [OD14, Exs. 10.6--10.9 (tensorization argument)].

**Proof sketch.** Set r = p/q ≥ 1 and raise the comparison to positive powers to reduce it to
ordinary Minkowski for finite sums of F^q. Factor out the uniform weights and simplify the
exponent products.
-/
lemma reverse_minkowski_mixed (p q : ℝ) (hq : 0 < q) (hqp : q ≤ p)
    (F : BoolCube n → BoolCube 1 → ℝ) (hF : ∀ x y, 0 ≤ F x y) :
    lpMean q (fun x ↦ lpMean p (fun y ↦ F x y)) ≥
      lpMean p (fun y ↦ lpMean q (fun x ↦ F x y)) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le hq hqp
  set r := p / q with hr_def
  have hr : 1 ≤ r := (le_div_iff₀ hq).2 (by simpa using hqp)
  have hEp (x : BoolCube n) : 0 ≤ expect fun y : BoolCube 1 ↦ F x y ^ p :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun y _ ↦ Real.rpow_nonneg (hF x y) p
  have hEq (y : BoolCube 1) : 0 ≤ expect fun x : BoolCube n ↦ F x y ^ q :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hF x y) q
  rw [lpMean_of_pos q hq, lpMean_of_pos p hp0]
  simp_rw [lpMean_of_pos p hp0, lpMean_of_pos q hq, abs_of_nonneg (hF _ _),
    abs_of_nonneg (Real.rpow_nonneg (hEp _) _), abs_of_nonneg (Real.rpow_nonneg (hEq _) _),
    ← Real.rpow_mul (hEp _), ← Real.rpow_mul (hEq _)]
  ring_nf
  have hA0 : 0 ≤ expect fun x : BoolCube n ↦
      (expect fun y : BoolCube 1 ↦ F x y ^ p) ^ (p⁻¹ * q) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hEp x) _
  have hB0 : 0 ≤ expect fun y : BoolCube 1 ↦
      (expect fun x : BoolCube n ↦ F x y ^ q) ^ (p * q⁻¹) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun y _ ↦ Real.rpow_nonneg (hEq y) _
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hA0 _) hq).1
  rw [← Real.rpow_mul hB0, ← Real.rpow_mul hA0]
  ring_nf
  rw [show q * p⁻¹ = 1 / r by rw [hr_def]; field_simp, show q * q⁻¹ = 1 by field_simp,
    Real.rpow_one]
  -- both sides are now unweighted finite sums, where Minkowski applies
  have hraw := finset_Lr_sum_le r hr Finset.univ Finset.univ (fun x y ↦ F x y ^ q)
    (fun x _ y _ ↦ Real.rpow_nonneg (hF x y) q)
  have hwn : (0:ℝ) ≤ uniformWeight n := pow_nonneg (by norm_num) _
  have hw1 : (0:ℝ) ≤ uniformWeight 1 := pow_nonneg (by norm_num) _
  unfold expect
  calc
    (uniformWeight 1 * ∑ y : BoolCube 1,
        (uniformWeight n * ∑ x : BoolCube n, F x y ^ q) ^ r) ^ (1 / r) =
        uniformWeight n * uniformWeight 1 ^ (1 / r) *
          (∑ y : BoolCube 1, (∑ x : BoolCube n, F x y ^ q) ^ r) ^ (1 / r) := by
      have hsum : 0 ≤ ∑ y : BoolCube 1, (∑ x : BoolCube n, F x y ^ q) ^ r :=
        Finset.sum_nonneg fun y _ ↦ Real.rpow_nonneg
          (Finset.sum_nonneg fun x _ ↦ Real.rpow_nonneg (hF x y) q) r
      rw [show (∑ y : BoolCube 1, (uniformWeight n * ∑ x : BoolCube n, F x y ^ q) ^ r) =
          uniformWeight n ^ r * ∑ y : BoolCube 1, (∑ x : BoolCube n, F x y ^ q) ^ r by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ Real.mul_rpow hwn
          (Finset.sum_nonneg fun x _ ↦ Real.rpow_nonneg (hF x y) q)]
      rw [Real.mul_rpow hw1 (mul_nonneg (Real.rpow_nonneg hwn r) hsum),
        Real.mul_rpow (Real.rpow_nonneg hwn r) hsum, ← Real.rpow_mul hwn,
        show r * (1 / r) = 1 by field_simp, Real.rpow_one]
      ring
    _ ≤ uniformWeight n * uniformWeight 1 ^ (1 / r) *
          ∑ x : BoolCube n, (∑ y : BoolCube 1, (F x y ^ q) ^ r) ^ (1 / r) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = uniformWeight n * ∑ x : BoolCube n,
          (uniformWeight 1 * ∑ y : BoolCube 1, F x y ^ p) ^ (1 / r) := by
      rw [mul_assoc, Finset.mul_sum]
      refine congrArg _ (Finset.sum_congr rfl fun x _ ↦ ?_)
      rw [Real.mul_rpow hw1 (Finset.sum_nonneg fun y _ ↦ Real.rpow_nonneg (hF x y) p)]
      refine congrArg _ (congrArg (fun z : ℝ ↦ z ^ (1 / r)) (Finset.sum_congr rfl fun y _ ↦ ?_))
      rw [← Real.rpow_mul (hF x y), hr_def]
      congr 1
      field_simp

/-- A one-bit reverse bound tensorizes to every Boolean cube.  The inductive
step splits off the last bit with `noiseOp_snoc_slice` and `lpMean_collapse_last`,
then exchanges the two blocks with `reverse_minkowski_mixed`.

**Source:** [OD14, Exs. 10.6--10.9].

**Proof sketch.** Induct on dimension; dimension zero is the mean of a constant. Split the last
bit, apply the one-bit reverse estimate, exchange mixed means by reverse Minkowski, and apply
induction to the remaining slices. The nested p-th means collapse to the original p-th mean.
-/
theorem tensorize_reverse_bonami_beckner (p q ρ : ℝ)
    (hq : 0 < q) (hqp : q < p)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hone : ∀ f : BooleanFunc 1, IsNonnegative f →
      lpMean q (noiseOp ρ f) ≥ lpMean p f)
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f := by
  have hp0 : 0 < p := hq.trans hqp
  induction n with
  | zero => rw [noiseOp_dim_zero, lpMean_dim_zero q hq f hf, lpMean_dim_zero p hp0 f hf]
  | succ k ih =>
      set F : BoolCube k → BoolCube 1 → ℝ :=
        fun x y ↦ noiseOp ρ (restrictLast f (y 0)) x
      have hF (x : BoolCube k) (y : BoolCube 1) : 0 ≤ F x y :=
        noiseOp_nonneg hρ0 hρ1 (fun z ↦ hf (Fin.snoc z (y 0))) x
      calc
        lpMean q (noiseOp ρ f) =
            lpMean q (fun x : BoolCube k ↦ lpMean q (noiseOp ρ (fun y : BoolCube 1 ↦ F x y))) := by
          rw [lpMean_collapse_last q hq (noiseOp ρ f)]
          exact congrArg _ (funext fun x ↦ congrArg _ (funext fun y ↦ noiseOp_snoc_slice ρ f x y))
        _ ≥ lpMean q (fun x : BoolCube k ↦ lpMean p (fun y : BoolCube 1 ↦ F x y)) :=
          lpMean_mono q hq (fun x ↦ lpMean_nonneg p hp0 _) fun x ↦ hone (fun y ↦ F x y) (hF x)
        _ ≥ lpMean p (fun y : BoolCube 1 ↦ lpMean q (fun x : BoolCube k ↦ F x y)) :=
          reverse_minkowski_mixed p q hq hqp.le F hF
        _ ≥ lpMean p (fun y : BoolCube 1 ↦
              lpMean p (fun x : BoolCube k ↦ restrictLast f (y 0) x)) :=
          lpMean_mono p hp0 (fun y ↦ lpMean_nonneg p hp0 _) fun y ↦
            ih (restrictLast f (y 0)) fun x ↦ hf (Fin.snoc x (y 0))
        _ = lpMean p (fun x : BoolCube k ↦
              lpMean p (fun y : BoolCube 1 ↦ f (Fin.snoc x (y 0)))) :=
          (lpMean_comm p hp0 fun x y ↦ f (Fin.snoc x (y 0))).symm
        _ = lpMean p f := (lpMean_collapse_last p hp0 f).symm

/-- States reverse hypercontractivity at sharp correlation for `0 < q < p < 1`.

**Source:** [OD14, Exs. 10.6--10.9]. -/
theorem reverse_bonami_beckner_positive_sharp (p q ρ : ℝ)
    (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 = (1 - p) / (1 - q))
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f :=
  tensorize_reverse_bonami_beckner p q ρ hq hqp hρ0 hρ1
    (fun g hg ↦ reverse_bonami_beckner_one_bit p q ρ hq hqp hp hρ0 hρsq g hg) f hf

/-! ### Reverse Hölder and the general statement -/

/-- More noise can only increase an `L^q` mean when `q < 1`.  Together with
`noiseOp_compose`, this relaxes equality in the correlation constraint.

**Proof sketch.** Kernel averaging increases means of exponent below one: use concavity for
positive powers, concavity of logarithm at zero, and convexity of negative powers followed by a
negative root. Handle zeros at nonpositive exponents by the stipulated zero-mean convention.
Factor the smaller correlation through the larger one and apply this averaging bound.
-/
lemma lpMean_noise_antitone (q ρ σ : ℝ) (hq : q < 1)
    (hρ0 : 0 ≤ ρ) (hρσ : ρ ≤ σ) (hσ1 : σ ≤ 1)
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean q (noiseOp σ f) := by
  classical
  have mean_nonneg : ∀ (r : ℝ) (u : BooleanFunc n), 0 ≤ lpMean r u := by
    intro r u
    unfold lpMean
    split_ifs
    · exact le_rfl
    · positivity
    · exact Real.rpow_nonneg (by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg (u x)) r) _
  have expect_pos : ∀ (u : BooleanFunc n), (∀ x, 0 < u x) → 0 < expect u := by
    intro u hu
    unfold expect uniformWeight
    exact mul_pos (pow_pos (by norm_num) _)
      (Finset.sum_pos (fun x _ ↦ hu x) Finset.univ_nonempty)
  have noise_positive : ∀ (τ : ℝ), 0 ≤ τ → τ ≤ 1 → ∀ (u : BooleanFunc n),
      (∀ x, 0 < u x) → ∀ x, 0 < noiseOp τ u x := by
    intro τ hτ0 hτ1 u hu x
    rw [noiseOp_eq_kernel_sum]
    have hkdiag : 0 < noiseKernel τ x x := by
      unfold noiseKernel
      apply Finset.prod_pos
      intro i hi
      cases x i <;> norm_num [boolToSign] <;> linarith
    calc
      0 < noiseKernel τ x x * u x := mul_pos hkdiag (hu x)
      _ ≤ ∑ y : BoolCube n, noiseKernel τ x y * u y := by
        have h := Finset.single_le_sum
          (s := Finset.univ)
          (fun y _ ↦ mul_nonneg
            (noiseKernel_nonneg hτ0 hτ1 x y) (hu y).le)
          (Finset.mem_univ x)
        simpa using h
  have kernel_double_sum : ∀ (τ : ℝ), 0 ≤ τ → τ ≤ 1 → ∀ (u : BooleanFunc n),
      ∑ x : BoolCube n, ∑ y : BoolCube n,
          noiseKernel τ x y * u y = ∑ y : BoolCube n, u y := by
    intro τ hτ0 hτ1 u
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [← Finset.sum_mul,
      noiseKernel_sum_left hτ0 hτ1 y, one_mul]
  have convex_rpow_of_neg : ∀ {r : ℝ}, r < 0 →
      ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ x ^ r) := by
    intro r hr
    have hneglog : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ -Real.log x) := by
      simpa only [Pi.neg_apply] using strictConcaveOn_log_Ioi.concaveOn.neg
    have hinner : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ r * Real.log x) := by
      have h := hneglog.smul (show 0 ≤ -r by linarith)
      convert h using 1
      ext x
      simp only [smul_eq_mul]
      ring
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have hinner_le := hinner.2 hx hy ha hb hab
    have hcombo : 0 < a • x + b • y := by
      simp only [smul_eq_mul]
      rcases eq_or_lt_of_le ha with ha0 | ha'
      · subst a
        norm_num at hab ⊢
        simpa [hab] using hy
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
    calc
      (a • x + b • y) ^ r = Real.exp (r * Real.log (a • x + b • y)) := by
        rw [Real.rpow_def_of_pos hcombo]
        congr 1
        ring
      _ ≤ Real.exp (a • (r * Real.log x) + b • (r * Real.log y)) :=
        Real.exp_le_exp.mpr hinner_le
      _ ≤ a • Real.exp (r * Real.log x) + b • Real.exp (r * Real.log y) :=
        convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      _ = a • x ^ r + b • y ^ r := by
        rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
        congr 2 <;> congr 1 <;> ring
  have expect_rpow_le_noise : ∀ (r τ : ℝ), 0 < r → r < 1 → 0 ≤ τ → τ ≤ 1 →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        expect (fun x ↦ u x ^ r) ≤ expect (fun x ↦ noiseOp τ u x ^ r) := by
    intro r τ hr0 hr1 hτ0 hτ1 u hu
    unfold expect
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _)
    rw [← kernel_double_sum τ hτ0 hτ1 (fun x ↦ u x ^ r)]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [noiseOp_eq_kernel_sum]
    exact (Real.concaveOn_rpow hr0.le hr1.le).le_map_sum
      (fun y _ ↦ noiseKernel_nonneg hτ0 hτ1 x y)
      (noiseKernel_sum_right hτ0 hτ1 x)
      (fun y _ ↦ hu y)
  have expect_noise_le_rpow : ∀ (r τ : ℝ), r < 0 → 0 ≤ τ → τ ≤ 1 →
      ∀ (u : BooleanFunc n), (∀ x, 0 < u x) →
        expect (fun x ↦ noiseOp τ u x ^ r) ≤ expect (fun x ↦ u x ^ r) := by
    intro r τ hr hτ0 hτ1 u hu
    unfold expect
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _)
    rw [← kernel_double_sum τ hτ0 hτ1 (fun x ↦ u x ^ r)]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [noiseOp_eq_kernel_sum]
    exact (convex_rpow_of_neg hr).map_sum_le
      (fun y _ ↦ noiseKernel_nonneg hτ0 hτ1 x y)
      (noiseKernel_sum_right hτ0 hτ1 x)
      (fun y _ ↦ hu y)
  have expect_log_le_noise : ∀ (τ : ℝ), 0 ≤ τ → τ ≤ 1 →
      ∀ (u : BooleanFunc n), (∀ x, 0 < u x) →
        expect (fun x ↦ Real.log (u x)) ≤
          expect (fun x ↦ Real.log (noiseOp τ u x)) := by
    intro τ hτ0 hτ1 u hu
    unfold expect
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _)
    rw [← kernel_double_sum τ hτ0 hτ1 (fun x ↦ Real.log (u x))]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [noiseOp_eq_kernel_sum]
    exact strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (fun y _ ↦ noiseKernel_nonneg hτ0 hτ1 x y)
      (noiseKernel_sum_right hτ0 hτ1 x)
      (fun y _ ↦ hu y)
  have one_step : ∀ (r τ : ℝ), r < 1 → 0 ≤ τ → τ ≤ 1 →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean r (noiseOp τ u) ≥ lpMean r u := by
    intro r τ hr hτ0 hτ1 u hu
    have hnoise := noiseOp_nonneg hτ0 hτ1 hu
    by_cases hrpos : 0 < r
    · rw [lpMean_of_pos r hrpos, lpMean_of_pos r hrpos]
      simp_rw [abs_of_nonneg (hnoise _), abs_of_nonneg (hu _)]
      exact Real.rpow_le_rpow
        (by
          rw [expect_eq_fintypeExpect]
          exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hu x) r)
        (expect_rpow_le_noise r τ hrpos hr hτ0 hτ1 u hu)
        (by positivity)
    · have hrnonpos : r ≤ 0 := le_of_not_gt hrpos
      by_cases hz : ∃ x, u x = 0
      · rw [show lpMean r u = 0 by simp [lpMean, hz, hrnonpos]]
        exact mean_nonneg r _
      · have hupos : ∀ x, 0 < u x := fun x ↦
          lt_of_le_of_ne (hu x) (Ne.symm (not_exists.mp hz x))
        have hnpos := noise_positive τ hτ0 hτ1 u hupos
        have hnz : ¬∃ x, noiseOp τ u x = 0 := not_exists.mpr fun x hx ↦ (hnpos x).ne' hx
        rcases eq_or_lt_of_le hrnonpos with rfl | hrneg
        · rw [show lpMean 0 (noiseOp τ u) =
              Real.exp (expect (fun x ↦ Real.log |noiseOp τ u x|)) by simp [lpMean, hnz],
            show lpMean 0 u = Real.exp (expect (fun x ↦ Real.log |u x|)) by
              simp [lpMean, hz]]
          simp_rw [abs_of_pos (hnpos _), abs_of_pos (hupos _)]
          exact Real.exp_le_exp.mpr (expect_log_le_noise τ hτ0 hτ1 u hupos)
        · rw [show lpMean r (noiseOp τ u) =
              (expect (fun x ↦ |noiseOp τ u x| ^ r)) ^ (1 / r) by
                simp [lpMean, hnz, hrneg.ne],
            show lpMean r u = (expect (fun x ↦ |u x| ^ r)) ^ (1 / r) by
                simp [lpMean, hz, hrneg.ne]]
          simp_rw [abs_of_pos (hnpos _), abs_of_pos (hupos _)]
          exact (Real.rpow_le_rpow_iff_of_neg
            (expect_pos _ fun x ↦ Real.rpow_pos_of_pos (hupos x) r)
            (expect_pos _ fun x ↦ Real.rpow_pos_of_pos (hnpos x) r)
            (one_div_neg.mpr hrneg)).2
              (expect_noise_le_rpow r τ hrneg hτ0 hτ1 u hupos)
  have hσ0 : 0 ≤ σ := le_trans hρ0 hρσ
  by_cases hσzero : σ = 0
  · have hρzero : ρ = 0 := le_antisymm (by simpa [hσzero] using hρσ) hρ0
    subst σ
    subst ρ
    rfl
  · let τ : ℝ := ρ / σ
    have hτ0 : 0 ≤ τ := div_nonneg hρ0 hσ0
    have hσpos : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσzero)
    have hτ1 : τ ≤ 1 := (div_le_one hσpos).2 hρσ
    have hfac : noiseOp τ (noiseOp σ f) = noiseOp ρ f := by
      rw [noiseOp_compose]
      congr 2
      dsimp [τ]
      field_simp
    rw [← hfac]
    exact one_step q τ hq hτ0 hτ1 (noiseOp σ f)
      (noiseOp_nonneg hσ0 hσ1 hf)

end BooleanAnalysis.Hypercontractivity
