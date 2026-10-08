/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.General

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Discrete random-variable hypercontractivity

Finite-law norm bounds, discrete contraction, and the sharp radius with its optimality theorem.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `discrete_lp_norm_le`.
* `discrete_hypercontractive`.
* `symmetric_discrete_hypercontractive`.
* `sharp_discrete_hypercontractive`.
* `sharp_discrete_radius_optimal`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Proposition 10.17 and Theorem 10.18.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A discrete variable with atom masses at least `lam` has `q`-norm at most
`(1/lam)^(1/2-1/q)` times its second norm. [OD14, Prop. 10.17]
Any positive lower bound may replace the exact minimum.

**Proof sketch.** Each support value is at most the second norm divided by `√lam` in
absolute value. Bound the `q`th power by this maximum to the power `q-2` times its square,
then average and take roots. -/
theorem discrete_lp_norm_le (X : Ω → ℝ) (q lam : ℝ) (hq : 2 < q) (hlam : 0 < lam)
    (hX : Measurable X) (hatoms : HasAtomLowerBound X μ lam) :
    rvLpNorm X μ q ≤ (1 / lam) ^ (1 / 2 - 1 / q) * rvLpNorm X μ 2 := by
  classical
  obtain ⟨s, hs, hmass⟩ := hatoms
  have hq0 : 0 < q := by linarith
  let L := ENNReal.ofReal lam
  let N := eLpNorm X 2 μ
  have hmem : MemLp X 2 μ := by
    apply MemLp.of_bound hX.aestronglyMeasurable (∑ x ∈ s, ‖x‖)
    filter_upwards [hs] with ω hω
    exact Finset.single_le_sum (fun x _ => norm_nonneg x) hω
  have hN : N ≠ ∞ := hmem.2.ne
  have hbound : ∀ᵐ ω ∂μ, ‖X ω‖ₑ ≤ N / L ^ (1 / 2 : ℝ) := by
    filter_upwards [hs] with ω hω
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))]
    calc
      ‖X ω‖ₑ * L ^ (1 / 2 : ℝ) ≤
          ‖X ω‖ₑ * (μ {v | X v = X ω}) ^ (1 / 2 : ℝ) := by
        gcongr
        exact hmass (X ω) hω
      _ ≤ N := by
        simpa [N, ENNReal.smul_def, smul_eq_mul] using
          le_eLpNorm_of_bddBelow (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
            ‖X ω‖₊ (measurableSet_eq_fun hX measurable_const)
            (Filter.Eventually.of_forall fun v hv => by
              change X v = X ω at hv
              rw [hv])
  have hnorm : eLpNorm X (ENNReal.ofReal q) μ ≤
      (1 / L) ^ (1 / 2 - 1 / q : ℝ) * N := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le, eLpNorm'_eq_lintegral_enorm]
    calc
      (∫⁻ ω, ‖X ω‖ₑ ^ q ∂μ) ^ (1 / q) ≤
          (∫⁻ ω, (N / L ^ (1 / 2 : ℝ)) ^ (q - 2) *
            ‖X ω‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / q) := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        apply lintegral_mono_ae
        filter_upwards [hbound] with ω hω
        calc
          ‖X ω‖ₑ ^ q = ‖X ω‖ₑ ^ (q - 2) * ‖X ω‖ₑ ^ (2 : ℝ) := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num)]
            congr 1
            ring
          _ ≤ (N / L ^ (1 / 2 : ℝ)) ^ (q - 2) * ‖X ω‖ₑ ^ (2 : ℝ) := by
            exact mul_le_mul_right' (ENNReal.rpow_le_rpow hω (by linarith)) _
      _ = ((N / L ^ (1 / 2 : ℝ)) ^ (q - 2) * N ^ (2 : ℝ)) ^ (1 / q) := by
        rw [lintegral_const_mul _ (hX.enorm.pow_const _),
          lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 2)]
        norm_num [N, eLpNorm]
      _ = (1 / L) ^ (1 / 2 - 1 / q : ℝ) * N := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          ENNReal.div_rpow_of_nonneg _ _
            (mul_nonneg (by linarith) (by positivity)),
          ← ENNReal.rpow_mul, div_eq_mul_inv, mul_right_comm,
          ← ENNReal.rpow_add_of_nonneg _ _
            (mul_nonneg (by linarith) (by positivity)) (by positivity)]
        have hexp : (q - 2) * (1 / q) + 2 * (1 / q) = 1 := by
          field_simp [hq0.ne'] <;> ring
        have hcoef : (1 / 2 : ℝ) * ((q - 2) * (1 / q)) = 1 / 2 - 1 / q := by
          field_simp [hq0.ne'] <;> ring
        rw [hexp, hcoef, ENNReal.rpow_one]
        simp [one_div, ENNReal.inv_rpow, mul_comm]
  have hfinite : (1 / L) ^ (1 / 2 - 1 / q : ℝ) * N ≠ ∞ := by
    apply ENNReal.mul_ne_top ?_ hN
    exact ENNReal.rpow_ne_top_of_ne_zero (by simp [one_div, L])
      (ENNReal.div_ne_top ENNReal.one_ne_top (ENNReal.ofReal_pos.mpr hlam).ne')
  simpa [rvLpNorm, N, L, ENNReal.toReal_mul, ENNReal.toReal_div,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hlam.le] using
    ENNReal.toReal_mono hfinite hnorm

/-- A centered discrete variable with atom masses at least `lam` is hypercontractive in
both conjugate directions at radius `lam^(1/2-1/q)/(2√(q-1))`.
[OD14, Prop. 10.17]

**Proof sketch.** Separate the almost-surely zero case. Otherwise normalize the second norm,
use the discrete norm bound and Theorem 10.16, then rescale. Affine-variable duality gives
the conjugate-exponent estimate. -/
theorem discrete_hypercontractive (X : Ω → ℝ) (q lam : ℝ)
    (hq : 2 < q) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hX : Measurable X) (hatoms : HasAtomLowerBound X μ lam) (hmean : ∫ ω, X ω ∂μ = 0) :
    IsHypercontractive X μ 2 (ENNReal.ofReal q)
        (lam ^ (1 / 2 - 1 / q) / (2 * Real.sqrt (q - 1))) ∧
      IsHypercontractive X μ (ENNReal.ofReal (q / (q - 1))) 2
        (lam ^ (1 / 2 - 1 / q) / (2 * Real.sqrt (q - 1))) := by
  classical
  let A : ℝ := lam ^ (1 / 2 - 1 / q)
  let r : ℝ := A / (2 * Real.sqrt (q - 1))
  let N : ℝ := rvLpNorm X μ 2
  have hqpos : 0 < q := by linarith
  have hQ2 : (2 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq.le
  have hQ0 : ENNReal.ofReal q ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hqpos).ne'
  have hmemq : MemLp X (ENNReal.ofReal q) μ := hatoms.memLp hX _
  have hmem2 : MemLp X 2 μ := hatoms.memLp hX _
  have hNnonneg : 0 ≤ N := ENNReal.toReal_nonneg
  have hApos : 0 < A := Real.rpow_pos_of_pos hlam0 _
  have hAone : A ≤ 1 := by
    apply Real.rpow_le_one hlam0.le hlam1
    apply sub_nonneg.mpr
    rw [div_le_div_iff₀ hqpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hsqrt : 1 < Real.sqrt (q - 1) := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (show 1 < q - 1 by linarith)
  have hdenpos : 0 < 2 * Real.sqrt (q - 1) := by positivity
  have hrnonneg : 0 ≤ r := div_nonneg hApos.le hdenpos.le
  have hrone : r < 1 := by
    apply (div_lt_one hdenpos).mpr
    exact lt_of_le_of_lt hAone (by linarith)
  have hforward : IsHypercontractive X μ 2 (ENNReal.ofReal q) r := by
    by_cases hNzero : N = 0
    · -- A vanishing second norm makes every affine perturbation constant almost surely.
      have hnormzero : eLpNorm X 2 μ = 0 := by
        exact ((ENNReal.toReal_eq_zero_iff _).mp
          (by simpa [N, rvLpNorm] using hNzero)).resolve_right hmem2.2.ne
      have hzero : X =ᵐ[μ] 0 :=
        (eLpNorm_eq_zero_iff hX.aestronglyMeasurable (by norm_num)).mp hnormzero
      refine ⟨by norm_num, hQ2, hrnonneg, hrone, hmemq, ?_⟩
      intro a b
      have haffine : ∀ (p : ENNReal) (c : ℝ),
          eLpNorm (fun ω => a + c * X ω) p μ =
            eLpNorm (fun _ : Ω => a) p μ := by
        intro p c
        apply eLpNorm_congr_ae
        filter_upwards [hzero] with ω hω
        simp [hω]
      calc
        eLpNorm (fun ω => a + r * b * X ω) (ENNReal.ofReal q) μ =
            eLpNorm (fun _ : Ω => a) (ENNReal.ofReal q) μ :=
          haffine _ (r * b)
        _ = eLpNorm (fun _ : Ω => a) 2 μ := by
          rw [eLpNorm_const a hQ0 (IsProbabilityMeasure.ne_zero μ),
            eLpNorm_const a (by norm_num : (2 : ENNReal) ≠ 0)
              (IsProbabilityMeasure.ne_zero μ)]
          simp [measure_univ]
        _ ≤ eLpNorm (fun ω => a + b * X ω) 2 μ :=
          le_of_eq (haffine 2 b).symm
    · -- Normalize the second norm and apply the centered-variable estimate.
      have hNpos : 0 < N := lt_of_le_of_ne hNnonneg (Ne.symm hNzero)
      let Y : Ω → ℝ := fun ω => N⁻¹ * X ω
      let C : ℝ := rvLpNorm Y μ q
      have hYmem : MemLp Y (ENNReal.ofReal q) μ := hmemq.const_mul N⁻¹
      have hscale : ∀ t : ℝ, rvLpNorm Y μ t = N⁻¹ * rvLpNorm X μ t := by
        intro t
        simpa only [rvLpNorm, Y, Pi.smul_apply, smul_eq_mul,
          ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hNnonneg)] using
          congrArg ENNReal.toReal (eLpNorm_const_smul N⁻¹ X (ENNReal.ofReal t) μ)
      have hsecond : rvLpNorm Y μ 2 = 1 := by
        rw [hscale]
        change N⁻¹ * N = 1
        exact inv_mul_cancel₀ hNzero
      have hYmean : ∫ ω, Y ω ∂μ = 0 := by
        simp only [Y, integral_const_mul, hmean, mul_zero]
      have hC1 : 1 ≤ C := by
        have hi : rvLpNorm Y μ 2 ≤ rvLpNorm Y μ q := by
          simpa [rvLpNorm] using ENNReal.toReal_mono hYmem.2.ne
            (eLpNorm_le_eLpNorm_of_exponent_le hQ2 hYmem.1)
        simpa only [hsecond] using hi
      have hCpos : 0 < C := by linarith
      have hnormalized := mean_zero_hypercontractive Y q C hq hYmem hYmean
        hsecond rfl hCpos
      have hrescaled : IsHypercontractive X μ 2 (ENNReal.ofReal q)
          (1 / (2 * C * Real.sqrt (q - 1))) := by
        simpa only [Y, ← mul_assoc, mul_inv_cancel₀ hNzero, one_mul] using
          hnormalized.const_mul N
      -- The discrete norm bound makes the desired radius smaller.
      have hbound : rvLpNorm X μ q ≤ A⁻¹ * N := by
        simpa only [A, N, one_div, Real.inv_rpow hlam0.le] using
          discrete_lp_norm_le X q lam hq hlam0 hX hatoms
      have hCbound : C ≤ A⁻¹ := by
        calc
          C = N⁻¹ * rvLpNorm X μ q := hscale q
          _ ≤ N⁻¹ * (A⁻¹ * N) :=
            mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hNnonneg)
          _ = A⁻¹ * (N⁻¹ * N) := by ring
          _ = A⁻¹ := by rw [inv_mul_cancel₀ hNzero, mul_one]
      have hAC : A * C ≤ 1 := by
        calc
          A * C ≤ A * A⁻¹ := mul_le_mul_of_nonneg_left hCbound hApos.le
          _ = 1 := mul_inv_cancel₀ hApos.ne'
      have hradius : r ≤ 1 / (2 * C * Real.sqrt (q - 1)) := by
        apply (div_le_div_iff₀ hdenpos (by positivity :
          0 < 2 * C * Real.sqrt (q - 1))).mpr
        calc
          A * (2 * C * Real.sqrt (q - 1)) =
              (A * C) * (2 * Real.sqrt (q - 1)) := by ring
          _ ≤ 1 * (2 * Real.sqrt (q - 1)) :=
            mul_le_mul_of_nonneg_right hAC hdenpos.le
      exact hrescaled.mono_radius hmean hrnonneg hradius
  exact ⟨hforward, IsHypercontractive.conjugate hq hmean hforward⟩


/-- Symmetry removes the factor one half from the discrete hypercontractive radius.
[OD14, Prop. 10.17, symmetric improvement]

**Proof sketch.** Normalize as in the nonsymmetric discrete case, apply Theorem 10.13
instead of Theorem 10.16, and use the same duality for the second inequality. -/
theorem symmetric_discrete_hypercontractive (X : Ω → ℝ) (q lam : ℝ)
    (hq : 2 < q) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hX : Measurable X) (hatoms : HasAtomLowerBound X μ lam) (hsym : IsSymmetricRV X μ) :
    IsHypercontractive X μ 2 (ENNReal.ofReal q) (lam ^ (1 / 2 - 1 / q) / Real.sqrt (q - 1)) ∧
      IsHypercontractive X μ (ENNReal.ofReal (q / (q - 1))) 2
        (lam ^ (1 / 2 - 1 / q) / Real.sqrt (q - 1)) := by
  classical
  let A : ℝ := lam ^ (1 / 2 - 1 / q)
  let r : ℝ := A / Real.sqrt (q - 1)
  let N : ℝ := rvLpNorm X μ 2
  have hqpos : 0 < q := by linarith
  have hQ2 : (2 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq.le
  have hQ0 : ENNReal.ofReal q ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hqpos).ne'
  have hmemq : MemLp X (ENNReal.ofReal q) μ := hatoms.memLp hX _
  have hmem2 : MemLp X 2 μ := hatoms.memLp hX _
  have hNnonneg : 0 ≤ N := ENNReal.toReal_nonneg
  have hApos : 0 < A := Real.rpow_pos_of_pos hlam0 _
  have hAone : A ≤ 1 := by
    apply Real.rpow_le_one hlam0.le hlam1
    apply sub_nonneg.mpr
    rw [div_le_div_iff₀ hqpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hsqrt : 1 < Real.sqrt (q - 1) := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (show 1 < q - 1 by linarith)
  have hdenpos : 0 < Real.sqrt (q - 1) := by linarith
  have hrnonneg : 0 ≤ r := div_nonneg hApos.le hdenpos.le
  have hrone : r < 1 := by
    apply (div_lt_one hdenpos).mpr
    exact hAone.trans_lt hsqrt
  have hmean : ∫ ω, X ω ∂μ = 0 := by
    have hi := hsym.integral_eq
    rw [integral_neg] at hi
    linarith
  have hforward : IsHypercontractive X μ 2 (ENNReal.ofReal q) r := by
    by_cases hNzero : N = 0
    · -- A vanishing second norm makes every affine perturbation constant almost surely.
      have hnormzero : eLpNorm X 2 μ = 0 := by
        exact ((ENNReal.toReal_eq_zero_iff _).mp
          (by simpa [N, rvLpNorm] using hNzero)).resolve_right hmem2.2.ne
      have hzero : X =ᵐ[μ] 0 :=
        (eLpNorm_eq_zero_iff hX.aestronglyMeasurable (by norm_num)).mp hnormzero
      refine ⟨by norm_num, hQ2, hrnonneg, hrone, hmemq, ?_⟩
      intro a b
      have haffine : ∀ (p : ENNReal) (c : ℝ),
          eLpNorm (fun ω => a + c * X ω) p μ =
            eLpNorm (fun _ : Ω => a) p μ := by
        intro p c
        apply eLpNorm_congr_ae
        filter_upwards [hzero] with ω hω
        simp [hω]
      calc
        eLpNorm (fun ω => a + r * b * X ω) (ENNReal.ofReal q) μ =
            eLpNorm (fun _ : Ω => a) (ENNReal.ofReal q) μ :=
          haffine _ (r * b)
        _ = eLpNorm (fun _ : Ω => a) 2 μ := by
          rw [eLpNorm_const a hQ0 (IsProbabilityMeasure.ne_zero μ),
            eLpNorm_const a (by norm_num : (2 : ENNReal) ≠ 0)
              (IsProbabilityMeasure.ne_zero μ)]
          simp [measure_univ]
        _ ≤ eLpNorm (fun ω => a + b * X ω) 2 μ :=
          le_of_eq (haffine 2 b).symm
    · -- Normalize the second norm while preserving symmetry.
      let Y : Ω → ℝ := fun ω => N⁻¹ * X ω
      let C : ℝ := rvLpNorm Y μ q
      have hYmem : MemLp Y (ENNReal.ofReal q) μ := hmemq.const_mul N⁻¹
      have hYsym : IsSymmetricRV Y μ := by
        change IdentDistrib Y (fun ω => -Y ω) μ μ
        simpa only [Y, Function.comp_def, mul_neg] using
          hsym.comp (show Measurable (fun x : ℝ => N⁻¹ * x) from
            measurable_const.mul measurable_id)
      have hscale : ∀ t : ℝ, rvLpNorm Y μ t = N⁻¹ * rvLpNorm X μ t := by
        intro t
        simpa only [rvLpNorm, Y, Pi.smul_apply, smul_eq_mul,
          ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hNnonneg)] using
          congrArg ENNReal.toReal (eLpNorm_const_smul N⁻¹ X (ENNReal.ofReal t) μ)
      have hsecond : rvLpNorm Y μ 2 = 1 := by
        rw [hscale]
        change N⁻¹ * N = 1
        exact inv_mul_cancel₀ hNzero
      have hC1 : 1 ≤ C := by
        have hi : rvLpNorm Y μ 2 ≤ rvLpNorm Y μ q := by
          simpa [rvLpNorm] using ENNReal.toReal_mono hYmem.2.ne
            (eLpNorm_le_eLpNorm_of_exponent_le hQ2 hYmem.1)
        simpa only [hsecond] using hi
      have hCpos : 0 < C := by linarith
      have hnormalized := symmetric_hypercontractive Y q C hq hYsym hYmem
        hsecond rfl hCpos
      have hrescaled : IsHypercontractive X μ 2 (ENNReal.ofReal q)
          (1 / (C * Real.sqrt (q - 1))) := by
        simpa only [Y, ← mul_assoc, mul_inv_cancel₀ hNzero, one_mul] using
          hnormalized.const_mul N
      -- The discrete norm bound makes the desired radius smaller.
      have hbound : rvLpNorm X μ q ≤ A⁻¹ * N := by
        simpa only [A, N, one_div, Real.inv_rpow hlam0.le] using
          discrete_lp_norm_le X q lam hq hlam0 hX hatoms
      have hCbound : C ≤ A⁻¹ := by
        calc
          C = N⁻¹ * rvLpNorm X μ q := hscale q
          _ ≤ N⁻¹ * (A⁻¹ * N) :=
            mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hNnonneg)
          _ = A⁻¹ * (N⁻¹ * N) := by ring
          _ = A⁻¹ := by rw [inv_mul_cancel₀ hNzero, mul_one]
      have hAC : A * C ≤ 1 := by
        calc
          A * C ≤ A * A⁻¹ := mul_le_mul_of_nonneg_left hCbound hApos.le
          _ = 1 := mul_inv_cancel₀ hApos.ne'
      have hradius : r ≤ 1 / (C * Real.sqrt (q - 1)) := by
        apply (div_le_div_iff₀ hdenpos (by positivity :
          0 < C * Real.sqrt (q - 1))).mpr
        calc
          A * (C * Real.sqrt (q - 1)) =
              (A * C) * Real.sqrt (q - 1) := by ring
          _ ≤ 1 * Real.sqrt (q - 1) :=
            mul_le_mul_of_nonneg_right hAC hdenpos.le
      exact hrescaled.mono_radius hmean hrnonneg hradius
  exact ⟨hforward, IsHypercontractive.conjugate hq hmean hforward⟩


/-- A centered discrete variable with atom masses at least `0 < lam < 1/2` is
hypercontractive in both conjugate directions at the sharp discrete radius.
[OD14, Thm. 10.18] The lower-bound form follows from the monotonicity of the sharp radius.

**Proof sketch.** The scalar biased two-point inequality and Wolff's finite-space
optimizer reduction give sharp conjugate noise contraction. Full finite operator
duality gives the forward bound, which the finite-law integral and norm formulas
transfer to affine perturbations of the random variable. Apply the established
affine-variable conjugacy theorem to obtain the other direction. -/
theorem sharp_discrete_hypercontractive (X : Ω → ℝ) (q lam : ℝ)
    (hq : 2 < q) (hlam0 : 0 < lam) (hlamhalf : lam < 1 / 2)
    (hX : Measurable X) (hatoms : HasAtomLowerBound X μ lam) (hmean : ∫ ω, X ω ∂μ = 0) :
    IsHypercontractive X μ 2 (ENNReal.ofReal q) (sharpDiscreteRadius q lam) ∧
      IsHypercontractive X μ (ENNReal.ofReal (q / (q - 1))) 2
        (sharpDiscreteRadius q lam) := by
  have hforward := SharpDiscrete.finite_law_sharp_forward
    μ X q lam hq hlam0 hlamhalf hX hatoms hmean
  exact ⟨hforward, IsHypercontractive.conjugate hq hmean hforward⟩


/-- For the centered two-point law with masses `lam` and `1-lam` at `1-lam` and `-lam`,
the sharp radius is necessary and sufficient in each conjugate direction.
[OD14, Thm. 10.18, optimality claim]

**Proof sketch.** The extremizing affine perturbation in the sharp two-point inequality
excludes all larger radii. Every function of a two-valued variable is affine, so operator
duality gives the same optimal radius in the conjugate direction. -/
theorem sharp_discrete_radius_optimal (X : Ω → ℝ) (q lam ρ : ℝ)
    (hq : 2 < q) (hlam0 : 0 < lam) (hlamhalf : lam < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hX : Measurable X)
    (hpositive : μ {ω | X ω = 1 - lam} = ENNReal.ofReal lam)
    (hnegative : μ {ω | X ω = -lam} = ENNReal.ofReal (1 - lam)) :
    (IsHypercontractive X μ 2 (ENNReal.ofReal q) ρ ↔ ρ ≤ sharpDiscreteRadius q lam) ∧
    (IsHypercontractive X μ (ENNReal.ofReal (q / (q - 1))) 2 ρ ↔
      ρ ≤ sharpDiscreteRadius q lam) := by
  have hmean := (FiniteLaw.centered_two_point_moments μ X lam hX
    hlam0.le (by linarith) hpositive hnegative).1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    exact SharpDiscrete.two_point_conjugate_radius_le μ X q lam ρ hX hq
      hlam0 hlamhalf hpositive hnegative
      (IsHypercontractive.conjugate hq hmean h)
  · intro h
    exact (SharpDiscrete.two_point_forward_sharp μ X q lam hX hq
      hlam0 hlamhalf hpositive hnegative).mono_radius hmean hρ0 h
  · intro h
    exact SharpDiscrete.two_point_conjugate_radius_le μ X q lam ρ hX hq
      hlam0 hlamhalf hpositive hnegative h
  · intro h
    exact (SharpDiscrete.two_point_conjugate_sharp μ X q lam hX hq
      hlam0 hlamhalf hpositive hnegative).mono_radius hmean hρ0 h

end BooleanAnalysis.Hypercontractivity
