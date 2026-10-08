/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Holder

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Extension of reverse hypercontractivity

One stage of Borell's reverse Bonami–Beckner argument, retaining the extended-mean conventions.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `extend_reverse_bonami_beckner`.
* `reverse_bonami_beckner`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercises 10.6–10.9.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

attribute [local simp] BooleanAnalysis.Hypercontractivity.cubeLpNorm

/-- Reverse hypercontractivity extends to nonnegative functions for real exponents
`q ≤ p ≤ 1` with `q < 1` and correlations `0 ≤ ρ ≤ 1` up to the sharp bound
`ρ² ≤ (1-p)/(1-q)`.

**Source:** [OD14, Exs. 10.6--10.9].

**Proof sketch.** Continuity at exponents zero and one reaches the boundary cases.
Reverse Hölder handles negative exponents, and the noise semigroup factors the case
where the exponents lie on opposite sides of zero. These steps reduce the inequality
to the positive-exponent sharp theorem. -/
lemma extend_reverse_bonami_beckner (p q ρ : ℝ)
    (hq : q < 1) (hqp : q ≤ p) (hp : p ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ (1 - p) / (1 - q))
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f := by
  classical
  have mean_nonneg (r : ℝ) (u : BooleanFunc n) : 0 ≤ lpMean r u := by
    unfold lpMean
    split_ifs
    · exact le_rfl
    · positivity
    · exact Real.rpow_nonneg (by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg _) r) _
  have noise_strict_pos : ∀ (R : ℝ), 0 ≤ R → R < 1 →
      ∀ (u : BooleanFunc n), IsNonnegative u → (∃ y, 0 < u y) →
        ∀ x, 0 < noiseOp R u x := by
    intro R hR0 hR1 u hu hex x
    rw [noiseOp_eq_kernel_sum]
    have hkernel (y : BoolCube n) :
        0 < noiseKernel R x y := by
      unfold noiseKernel
      apply Finset.prod_pos
      intro i hi
      cases x i <;> cases y i <;> norm_num [boolToSign] <;> nlinarith
    exact Finset.sum_pos'
      (fun y _ ↦ mul_nonneg (hkernel y).le (hu y))
      ⟨hex.choose, Finset.mem_univ _, mul_pos (hkernel hex.choose) hex.choose_spec⟩
  have positive_subsharp : ∀ (P Q R : ℝ), 0 < Q → Q < P → P < 1 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ (1 - P) / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean P u := by
    intro P Q R hQ hQP hP hR0 hR1 hRsq u hu
    let S : ℝ := Real.sqrt ((1 - P) / (1 - Q))
    have hden : 0 < 1 - Q := sub_pos.mpr (lt_trans hQP hP)
    have hratio0 : 0 ≤ (1 - P) / (1 - Q) :=
      div_nonneg (sub_nonneg.mpr hP.le) hden.le
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq : S ^ 2 = (1 - P) / (1 - Q) := Real.sq_sqrt hratio0
    have hS1 : S ≤ 1 := by
      rw [← sq_le_sq₀ hS0 (by norm_num : (0 : ℝ) ≤ 1), hSsq]
      norm_num
      exact (div_le_one hden).2 (by linarith)
    have hRS : R ≤ S := by
      rw [← sq_le_sq₀ hR0 hS0, hSsq]
      exact hRsq
    exact le_trans
      (reverse_bonami_beckner_positive_sharp P Q S hQ hQP hP hS0 hS1 hSsq u hu)
      (lpMean_noise_antitone Q R S (lt_trans hQP hP) hR0 hRS hS1 u hu)
  have lpMean_continuous_zero (u : BooleanFunc n) (hu : ∀ x, 0 < u x) :
      ContinuousAt (fun r : ℝ ↦ lpMean r u) 0 := by
    let M : ℝ → ℝ := fun r ↦ expect (fun x ↦ u x ^ r)
    let A : ℝ := expect (fun x ↦ Real.log (u x))
    have hnz : ¬∃ x, u x = 0 := not_exists.mpr fun x hx ↦ (hu x).ne' hx
    have hM0 : M 0 = 1 := by simp [M, expect, uniformWeight]
    have hMpos (r : ℝ) : 0 < M r := by
      dsimp [M, expect, uniformWeight]
      apply mul_pos (pow_pos (by norm_num) _)
      exact Finset.sum_pos' (fun x _ ↦ (Real.rpow_pos_of_pos (hu x) r).le)
        ⟨Classical.arbitrary _, Finset.mem_univ _, Real.rpow_pos_of_pos (hu _) r⟩
    have hM : HasDerivAt M A 0 := by
      dsimp [M, A, expect]
      apply HasDerivAt.const_mul
      apply HasDerivAt.fun_sum
      intro x hx
      change HasDerivAt (fun r : ℝ ↦ u x ^ r) (Real.log (u x)) 0
      simpa only [Real.rpow_def_of_pos (hu x), id_eq, mul_zero, Real.exp_zero,
        one_mul, mul_one] using
        ((hasDerivAt_id (x := (0 : ℝ))).const_mul (Real.log (u x))).exp
    have hlog : HasDerivAt (fun r ↦ Real.log (M r)) A 0 := by
      convert hM.log (hMpos 0).ne' using 1
      all_goals simp [hM0]
    let G : ℝ → ℝ :=
      Function.update (fun r ↦ (Real.log (M r) - Real.log (M 0)) / (r - 0)) 0 A
    have hG : ContinuousAt G 0 := hlog.continuousAt_div
    have hfun : (fun r : ℝ ↦ lpMean r u) = fun r ↦ Real.exp (G r) := by
      funext r
      by_cases hr : r = 0
      · subst r
        simp [lpMean, hnz, G, A, abs_of_pos (hu _)]
      · rw [lpMean]
        simp only [hnz, false_and, if_neg hr,
          BooleanAnalysis.Hypercontractivity.cubeLpNorm]
        have habs : expect (fun x ↦ |u x| ^ r) = M r := by
          have heq : (fun x ↦ |u x| ^ r) = fun x ↦ u x ^ r := by
            funext x
            rw [abs_of_pos (hu x)]
          rw [heq]
        rw [habs, Real.rpow_def_of_pos (hMpos r)]
        simp [G, hr, hM0, div_eq_mul_inv]
    rw [hfun]
    simpa only [Function.comp_apply] using Real.continuous_exp.continuousAt.comp hG
  have zero_subsharp : ∀ (P R : ℝ), 0 < P → P < 1 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ 1 - P →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean 0 (noiseOp R u) ≥ lpMean P u := by
    intro P R hP0 hP1 hR0 hR1 hRsq u hu
    by_cases hu0 : u = 0
    · subst u
      rw [show noiseOp R (0 : BooleanFunc n) = 0 by
        simpa using noiseOp_const_mul R 0 (0 : BooleanFunc n)]
      simp [lpMean, hP0.ne', not_le.mpr hP0, expect, uniformWeight]
    · have hex : ∃ y, 0 < u y := by
        by_contra h
        push_neg at h
        exact hu0 (funext fun y ↦ le_antisymm (h y) (hu y))
      have hRlt : R < 1 := by nlinarith [sq_nonneg R]
      have houtpos := noise_strict_pos R hR0 hRlt u hu hex
      have ht : Filter.Tendsto (fun r : ℝ ↦ lpMean r (noiseOp R u))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (lpMean 0 (noiseOp R u))) :=
        (lpMean_continuous_zero (noiseOp R u) houtpos).mono_left inf_le_left
      apply ge_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hP0).filter_mono inf_le_left] with r hr0 hrP
      change 0 < r at hr0
      have hr1 : r < 1 := lt_trans hrP hP1
      have hbound : R ^ 2 ≤ (1 - P) / (1 - r) := by
        rw [le_div_iff₀ (sub_pos.mpr hr1)]
        calc
          R ^ 2 * (1 - r) ≤ R ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg R)
          _ = R ^ 2 := by ring
          _ ≤ 1 - P := hRsq
      exact positive_subsharp P r R hr0 hrP hP1 hR0 hR1 hbound u hu
  have negative_subsharp : ∀ (P Q R : ℝ), Q < P → P < 0 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ (1 - P) / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean P u := by
    intro P Q R hQP hP hR0 hR1 hRsq u hu
    by_cases hz : ∃ x, u x = 0
    · have hright : lpMean P u = 0 := by simp [lpMean, hz, hP.le]
      rw [hright]
      exact mean_nonneg Q _
    · have hupos : ∀ x, 0 < u x :=
        fun x ↦ (hu x).lt_of_ne (Ne.symm (not_exists.mp hz x))
      have hratio_lt : (1 - P) / (1 - Q) < 1 := by
        rw [div_lt_one (by linarith : 0 < 1 - Q)]
        linarith
      have hRlt : R < 1 := by nlinarith [sq_nonneg R]
      let H : BooleanFunc n := noiseOp R u
      have hHpos : ∀ x, 0 < H x :=
        noise_strict_pos R hR0 hRlt u hu ⟨Classical.arbitrary _, hupos _⟩
      have hE : 0 < expect (fun x ↦ H x ^ Q) :=
        ReverseMoments.expect_rpow_pos (fun x ↦ (hHpos x).le) ⟨Classical.arbitrary _, hHpos _⟩
      let A : ℝ := (expect (fun x ↦ H x ^ Q)) ^ (1 / Q)
      have hApos : 0 < A := Real.rpow_pos_of_pos hE _
      let Q' : ℝ := Q / (Q - 1)
      let P' : ℝ := P / (P - 1)
      have hQ'0 : 0 < Q' := by
        dsimp [Q']
        exact div_pos_of_neg_of_neg (lt_trans hQP hP) (by linarith)
      have hP'0 : 0 < P' := by
        dsimp [P']
        exact div_pos_of_neg_of_neg hP (by linarith)
      have hPm : P - 1 ≠ 0 := by linarith
      have hQm : Q - 1 ≠ 0 := by linarith
      have hOneP : 1 - P ≠ 0 := by linarith
      have hOneQ : 1 - Q ≠ 0 := by linarith
      have heqP : P / (P - 1) = (-P) / (1 - P) := by
        field_simp [hPm, hOneP]
        all_goals ring
      have heqQ : Q / (Q - 1) = (-Q) / (1 - Q) := by
        field_simp [hQm, hOneQ]
        all_goals ring
      have hP'Q' : P' < Q' := by
        dsimp [P', Q']
        rw [heqP, heqQ,
          div_lt_div_iff₀ (by linarith : 0 < 1 - P) (by linarith : 0 < 1 - Q)]
        nlinarith
      have hQ'1 : Q' < 1 := by
        dsimp [Q']
        rw [div_lt_iff_of_neg (by linarith : Q - 1 < 0)]
        linarith
      have h1Q : 1 - Q' = 1 / (1 - Q) := by
        dsimp [Q']
        field_simp [hQm, hOneQ]
        all_goals ring
      have h1P : 1 - P' = 1 / (1 - P) := by
        dsimp [P']
        field_simp [hPm, hOneP]
        all_goals ring
      have hratio : (1 - Q') / (1 - P') = (1 - P) / (1 - Q) := by
        rw [h1Q, h1P]
        field_simp [hOneP, hOneQ]
      let g : BooleanFunc n := fun x ↦ (H x / A) ^ (Q - 1)
      have hgpos (x : BoolCube n) : 0 < g x :=
        Real.rpow_pos_of_pos (div_pos (hHpos x) hApos) _
      have hQne : Q ≠ 0 := by linarith
      have hnormQ : expect (fun x ↦ (H x / A) ^ Q) = 1 := by
        simpa [A] using ReverseMoments.expect_normalized_rpow_eq_one
          hQne H (fun x ↦ (hHpos x).le) hE
      have hnormg : lpMean Q' g = 1 := by
        rw [lpMean_of_pos Q' hQ'0]
        simp_rw [abs_of_pos (hgpos _)]
        have hmom : expect (fun x ↦ g x ^ Q') = 1 := by
          rw [← hnormQ]
          apply congrArg expect
          funext x
          dsimp [g, Q']
          rw [← Real.rpow_mul (div_pos (hHpos x) hApos).le]
          congr 1
          field_simp [hQm]
        rw [hmom, one_div, Real.one_rpow]
      have hinner : innerProduct H g = A := by
        have hpoint (x : BoolCube n) : H x * g x = A * (H x / A) ^ Q := by
          dsimp [g]
          have hrpow :
              (H x / A) ^ Q = (H x / A) * (H x / A) ^ (Q - 1) := by
            calc
              (H x / A) ^ Q = (H x / A) ^ (Q - 1 + 1) := by
                congr 1
                all_goals ring
              _ = (H x / A) ^ (Q - 1) * (H x / A) ^ (1 : ℝ) :=
                Real.rpow_add (div_pos (hHpos x) hApos) (Q - 1) 1
              _ = (H x / A) * (H x / A) ^ (Q - 1) := by
                rw [Real.rpow_one]
                ring
          rw [hrpow]
          field_simp
        unfold innerProduct expect
        simp_rw [hpoint, ← Finset.mul_sum]
        rw [show uniformWeight n * (A * ∑ x, (H x / A) ^ Q) =
          A * (uniformWeight n * ∑ x, (H x / A) ^ Q) by ring]
        change A * expect (fun x ↦ (H x / A) ^ Q) = A
        rw [hnormQ]
        ring
      have hBB : lpMean P' (noiseOp R g) ≥ lpMean Q' g := by
        have hRsq' : R ^ 2 ≤ (1 - Q') / (1 - P') := by
          rw [hratio]
          exact hRsq
        exact positive_subsharp Q' P' R hP'0 hP'Q' hQ'1 hR0 hR1 hRsq' g
          (fun x ↦ (hgpos x).le)
      have hhold := reverse_holder P (by linarith : P < 1) (by linarith : P ≠ 0)
        u (noiseOp R g) hu (noiseOp_nonneg hR0 hR1 fun x ↦ (hgpos x).le)
      rw [show P / (P - 1) = P' by rfl] at hhold
      have hself : innerProduct u (noiseOp R g) = innerProduct H g := by
        dsimp [H]
        exact (BooleanAnalysis.noiseOp_self_adjoint R u g).symm
      rw [hself, hinner] at hhold
      rw [hnormg] at hBB
      have hmul : lpMean P u ≤ lpMean P u * lpMean P' (noiseOp R g) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hBB (mean_nonneg P u)
      have hA : A = lpMean Q H := by
        dsimp [A]
        rw [lpMean]
        simp only [not_exists.mpr (fun x hx ↦ (hHpos x).ne' hx), false_and, if_false,
          if_neg hQne, BooleanAnalysis.Hypercontractivity.cubeLpNorm]
        simp_rw [abs_of_pos (hHpos _)]
      dsimp [H] at hA
      rw [← hA]
      exact hmul.trans hhold
  have zero_target : ∀ (Q R : ℝ), Q < 0 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ 1 / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean 0 u := by
    intro Q R hQ hR0 hR1 hRsq u hu
    by_cases hz : ∃ x, u x = 0
    · have hright : lpMean 0 u = 0 := by simp [lpMean, hz]
      rw [hright]
      exact mean_nonneg Q _
    · have hupos : ∀ x, 0 < u x :=
        fun x ↦ (hu x).lt_of_ne (Ne.symm (not_exists.mp hz x))
      have ht : Filter.Tendsto (fun r : ℝ ↦ lpMean r u)
          (nhdsWithin 0 (Set.Iio 0)) (nhds (lpMean 0 u)) :=
        (lpMean_continuous_zero u hupos).mono_left inf_le_left
      apply le_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hQ).filter_mono inf_le_left] with r hr0 hQr
      change r < 0 at hr0
      have hden : 0 < 1 - Q := by linarith
      have hscaled : R ^ 2 * (1 - Q) ≤ 1 := (le_div_iff₀ hden).mp hRsq
      have hbound : R ^ 2 ≤ (1 - r) / (1 - Q) := by
        rw [le_div_iff₀ hden]
        linarith
      exact negative_subsharp r Q R hQr hr0 hR0 hR1 hbound u hu
  have cross_zero : ∀ (P Q R : ℝ), Q < 0 → 0 < P → P < 1 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ (1 - P) / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean P u := by
    intro P Q R hQ hP0 hP1 hR0 hR1 hRsq u hu
    let A : ℝ := Real.sqrt (1 / (1 - Q))
    have hden : 0 < 1 - Q := by linarith
    have hfrac : 0 < 1 / (1 - Q) := one_div_pos.mpr hden
    have hA0 : 0 < A := Real.sqrt_pos.2 hfrac
    have hAsq : A ^ 2 = 1 / (1 - Q) := Real.sq_sqrt hfrac.le
    have hfrac1 : 1 / (1 - Q) ≤ 1 := (div_le_one hden).2 (by linarith)
    have hA1 : A ≤ 1 := by nlinarith [hAsq, hA0, hfrac1]
    have hRA : R ≤ A := by
      rw [← sq_le_sq₀ hR0 hA0.le, hAsq]
      exact hRsq.trans (by
        rw [div_le_div_iff_of_pos_right hden]
        nlinarith)
    let T : ℝ := R / A
    have hT0 : 0 ≤ T := div_nonneg hR0 hA0.le
    have hT1 : T ≤ 1 := (div_le_one hA0).2 hRA
    have hscaled : R ^ 2 * (1 - Q) ≤ 1 - P := (le_div_iff₀ hden).mp hRsq
    have hTsq : T ^ 2 ≤ 1 - P := by
      dsimp [T]
      rw [div_pow, hAsq]
      field_simp [hden.ne', hA0.ne']
      nlinarith
    have hcomp : noiseOp A (noiseOp T u) = noiseOp R u := by
      rw [noiseOp_compose]
      congr 2
      dsimp [T]
      field_simp
    rw [← hcomp]
    exact le_trans
      (zero_subsharp P T hP0 hP1 hT0 hT1 hTsq u hu)
      (zero_target Q A hQ hA0.le hA1 hAsq.le (noiseOp T u)
        (noiseOp_nonneg hT0 hT1 hu))
  have lpMean_const (r c : ℝ) (hc : 0 ≤ c) :
      lpMean r (fun _ : BoolCube n ↦ c) = c := by
    by_cases hc0 : c = 0
    · subst c
      by_cases hr : r ≤ 0
      · simp [lpMean, hr]
      · have hr0 : 0 < r := lt_of_not_ge hr
        rw [lpMean_of_pos r hr0]
        simp [expect, uniformWeight, Real.zero_rpow hr0.ne']
        rw [Real.zero_rpow (inv_pos.mpr hr0).ne']
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      by_cases hr0 : r = 0
      · subst r
        simp [lpMean, hc0, abs_of_pos hcpos, expect, uniformWeight, Real.exp_log hcpos]
      · rw [lpMean]
        simp only [not_exists.mpr (fun _ h ↦ hc0 h), false_and, if_false, if_neg hr0,
          BooleanAnalysis.Hypercontractivity.cubeLpNorm, abs_of_pos hcpos]
        have he : expect (fun _ : BoolCube n ↦ c ^ r) = c ^ r := by
          simp [expect, uniformWeight]
        rw [he, ← Real.rpow_mul hcpos.le]
        field_simp
        exact Real.rpow_one c
  have noiseOp_zero (u : BooleanFunc n) :
      noiseOp 0 u = fun _ ↦ expect u := by
    funext x
    rw [noiseOp_eq_kernel_sum]
    unfold noiseKernel expect uniformWeight
    simp [Finset.prod_const, Finset.card_univ, ← Finset.mul_sum]
  have endpoint_one : ∀ (Q R : ℝ), Q < 1 → 0 ≤ R → R ≤ 1 →
      R ^ 2 ≤ (1 - 1) / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean 1 u := by
    intro Q R hQ hR0 hR1 hRsq u hu
    have hR : R = 0 := by
      have hden : 0 < 1 - Q := sub_pos.mpr hQ
      rw [show (1 - 1) / (1 - Q) = 0 by
        field_simp
        all_goals ring] at hRsq
      nlinarith [sq_nonneg R]
    subst R
    rw [noiseOp_zero]
    have hexpect : 0 ≤ expect u := by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ hu x
    rw [lpMean_const Q (expect u) hexpect, lpMean_of_pos 1 (by norm_num)]
    simp_rw [abs_of_nonneg (hu _), Real.rpow_one]
    norm_num
  have noiseOp_one (u : BooleanFunc n) : noiseOp 1 u = u := by
    funext x
    unfold noiseOp
    simp only [one_pow, one_mul]
    exact (walsh_expansion u x).symm
  by_cases hp1 : p = 1
  · subst p
    exact endpoint_one q ρ hq hρ0 hρ1 hρsq f hf
  have hp' : p < 1 := lt_of_le_of_ne hp hp1
  by_cases hqp' : q = p
  · subst q
    simpa only [noiseOp_one] using
      lpMean_noise_antitone p ρ 1 hp' hρ0 hρ1 (by norm_num) f hf
  have hqp'' : q < p := lt_of_le_of_ne hqp hqp'
  rcases lt_trichotomy p 0 with hpneg | hpzero | hppos
  · exact negative_subsharp p q ρ hqp'' hpneg hρ0 hρ1 hρsq f hf
  · subst p
    exact zero_target q ρ (by linarith) hρ0 hρ1 (by simpa using hρsq) f hf
  · rcases lt_trichotomy q 0 with hqneg | hqzero | hqpos
    · exact cross_zero p q ρ hqneg hppos hp' hρ0 hρ1 hρsq f hf
    · subst q
      exact zero_subsharp p ρ hppos hp' hρ0 hρ1 (by simpa using hρsq) f hf
    · exact positive_subsharp p q ρ hqpos hqp'' hp' hρ0 hρ1 hρsq f hf

/-- Reverse hypercontractivity holds for nonnegative cube functions and finite
`q ≤ p ≤ 1`, `q < 1`, at the stated sharp correlation bound.
The source's strict `q < p` theorem is extended here to equal finite exponents.
Its `q = -∞` minimum-mean endpoint is not represented.

**Source:** [OD14, Exs. 10.6--10.9]. -/
theorem reverse_bonami_beckner (p q ρ : ℝ)
    (hq : q < 1) (hqp : q ≤ p) (hp : p ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ (1 - p) / (1 - q))
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f :=
  extend_reverse_bonami_beckner p q ρ hq hqp hp hρ0 hρ1 hρsq f hf

end BooleanAnalysis.Hypercontractivity
