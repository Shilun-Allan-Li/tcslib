/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance
import TCSlib.BooleanAnalysis.GaussianSpace.InvarianceTruncation
import TCSlib.BooleanAnalysis.GaussianSpace.InvarianceDistribution
import TCSlib.BooleanAnalysis.GaussianSpace.SumInvariance
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Third-order, smoothed and distributional invariance

## Main definitions

All polynomial evaluations, variances, influences, noisy influences and truncations
reuse existing BooleanAnalysis definitions. Lévy distance comes from `SumInvariance`.

## Main results

* `invariance_c3`: third-order invariance for hypercontractive inputs.
* `invariance_lowDegree_tail`: Lipschitz invariance with a high-degree tail.
* `invariance_no_notables`: smoothed invariance from small noisy influences.
* `invariance_levy` and `invariance_c3_levy`: distributional invariance in Lévy distance.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Remark 11.66 and Corollaries 11.69–11.70.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

/-- Standardized hypercontractive inputs satisfy third-order invariance without
matching third moments, with the source's exact `C/3` constant.
[OD14, Remark 11.66]

**Proof sketch.** Replace coordinates one at a time and use a second-order Taylor
expansion. Hypercontractivity bounds the third absolute moment of the terms
containing the replaced coordinate by their coefficient L² norm, giving the
`ρ^(-3k)` and influence-to-three-halves factors. -/
theorem invariance_c3 {n k : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ)
    (hIX : iIndepFun X μ) (hIY : iIndepFun Y ν)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hX : ∀ i, IsHypercontractive (X i) μ 2 3 ρ)
    (hY : ∀ i, IsHypercontractive (Y i) ν 2 3 ρ)
    (hmX : ∀ i, (∫ ω, X i ω ∂μ) = 0) (hmY : ∀ i, (∫ ω, Y i ω ∂ν) = 0)
    (hvX : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1)
    (hvY : ∀ i, (∫ ω, Y i ω ^ 2 ∂ν) = 1)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ) (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ t, |iteratedDeriv 3 ψ t| ≤ C) :
    |(∫ ω, ψ (evalMultilinearRV F X ω) ∂μ) -
      (∫ ω, ψ (evalMultilinearRV F Y ω) ∂ν)| ≤
      (C / 3) * (1 / ρ) ^ (3 * k) *
        ∑ i : Fin n, (influence i F.eval) ^ (3 / 2 : ℝ) := by
  classical
  obtain ⟨κ, hκ, Z, hIZ, hL, hR, hXL, hYR⟩ :=
    Invariance.independent_polynomial_coupling F X Y hIX hIY
      (fun i => (hX i).2.2.2.2.1.aemeasurable)
      (fun i => (hY i).2.2.2.2.1.aemeasurable)
  letI := hκ
  have hZ (a : Fin n ⊕ Fin n) : IsHypercontractive (Z a) κ 2 3 ρ := by
    cases a with
    | inl i => exact (hX i).identDistrib (hL i)
    | inr i => exact (hY i).identDistrib (hR i)
  have hmZ (a : Fin n ⊕ Fin n) : (∫ z, Z a z ∂κ) = 0 := by
    cases a with
    | inl i => exact (hL i).integral_eq.symm.trans (hmX i)
    | inr i => exact (hR i).integral_eq.symm.trans (hmY i)
  have hvZ (a : Fin n ⊕ Fin n) : (∫ z, Z a z ^ 2 ∂κ) = 1 := by
    cases a with
    | inl i => exact ((hL i).pow (n := 2)).integral_eq.symm.trans (hvX i)
    | inr i => exact ((hR i).pow (n := 2)).integral_eq.symm.trans (hvY i)
  have eX := (hXL.comp hψ.continuous.measurable).integral_eq
  have eY := (hYR.comp hψ.continuous.measurable).integral_eq
  simp only [Function.comp_def] at eX eY
  rw [eX, eY]
  exact Invariance.invariance_c3_of_independent_pair
    F hdegree Z hIZ ρ hρ hZ hmZ hvZ ψ hψ C hC hderiv

/-- Small influences of the low-degree part suffice for Lipschitz invariance,
with an additional L² high-degree tail. [OD14, Cor. 11.69, first assertion]
The source's real cutoff is represented using the existing truncation at its
natural floor; this preserves exactly which integer Fourier levels are retained.

**Proof sketch.** Apply the proved low-degree Lipschitz principle to the
truncation. Bound both discarded tails by Cauchy–Schwarz and the matching
Boolean/Gaussian second-moment coefficient identities. -/
theorem invariance_lowDegree_tail :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ} (f : BooleanFunc n), cubeVariance f ≤ 1 →
      ∀ k : ℝ, 0 ≤ k → ∀ ε : ℝ, 0 ≤ ε →
      (∀ i, influence i (KKL.lowDegreePart f ⌊k⌋₊) ≤ ε) →
      ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ →
        |expect (fun x => ψ (f x)) -
          (∫ z : Fin n → ℝ, ψ (evalMultilinearRV (fourierCoeff f) (fun i z => z i) z)
            ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))| ≤
          K * (c : ℝ) * ((2 : ℝ) ^ k * ε ^ (1 / 4 : ℝ) +
            l2Norm (KKL.highDegreePart f ⌊k⌋₊)) := by
  obtain ⟨K, hK, hbound⟩ := Invariance.invariance_lipschitz_boolean_gaussian
  refine ⟨K + 2, by linarith, ?_⟩
  intro n f hvar k hk ε hε hinf c ψ hψ
  let d : ℕ := ⌊k⌋₊
  let g := KKL.lowDegreePart f d
  let T := l2Norm (KKL.highDegreePart f d)
  let a := (2 : ℝ) ^ k * ε ^ (1 / 4 : ℝ)
  let E (u : BooleanFunc n) := expect (fun x => ψ (u x))
  let J (u : BooleanFunc n) := ∫ z : Fin n → ℝ,
    ψ (evalMultilinearRV (fourierCoeff u) (fun i z => z i) z)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)
  have hdiff : f - g = KKL.highDegreePart f d := by
    funext x
    change f x - KKL.lowDegreePart f d x = KKL.highDegreePart f d x
    linarith [KKL.low_plus_high_eq f d x]
  have hleft := Invariance.lipschitz_expect_sub_le_l2Norm f g hψ
  rw [hdiff] at hleft
  change |E f - E g| ≤ (c : ℝ) * T at hleft
  have hmid := hbound g (Invariance.lowDegreePart_polynomial_degree f d)
    ((Invariance.lowDegreePart_variance_le f d).trans hvar) ε hε hinf c ψ hψ
  have hfloor : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hk)
  have hmid' : |E g - J g| ≤ K * (c : ℝ) * a := by
    calc
      _ ≤ K * (c : ℝ) * (2 : ℝ) ^ d * ε ^ (1 / 4 : ℝ) := hmid
      _ ≤ K * (c : ℝ) * (2 : ℝ) ^ k * ε ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfloor (mul_nonneg hK.le c.coe_nonneg))
          (Real.rpow_nonneg hε _)
      _ = _ := by dsimp [a]; ring
  have hright := Invariance.lipschitz_gaussian_extension_sub_le_l2Norm f g hψ
  rw [hdiff] at hright
  change |J f - J g| ≤ (c : ℝ) * T at hright
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  change |E f - J f| ≤ (K + 2) * (c : ℝ) * (a + T)
  calc
    _ ≤ |E f - E g| + (|E g - J g| + |J g - J f|) :=
      (abs_sub_le _ _ _).trans (add_le_add_left (abs_sub_le _ _ _) _)
    _ ≤ (c : ℝ) * T + (K * (c : ℝ) * a + (c : ℝ) * T) :=
      add_le_add hleft (add_le_add hmid' (by simpa only [abs_sub_comm] using hright))
    _ ≤ _ := by
      nlinarith only [mul_nonneg hK.le (mul_nonneg c.coe_nonneg hT),
        mul_nonneg c.coe_nonneg ha]

/-- Noise-smoothed functions with no notable coordinates satisfy a dimension-free
Lipschitz invariance bound. [OD14, Cor. 11.69, second assertion]
No-notables is stated directly with the existing noisy influence, avoiding a
second notability predicate. The source allows `ε ≤ 1` and `δ ≤ 1/20`.

**Proof sketch.** The noisy influence bounds all truncated influences after
smoothing. Exponential decay controls the tail. Choose the real cutoff
`log(1/ε)/3` in the preceding theorem and compare the resulting powers. -/
theorem invariance_no_notables :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ} (h : BooleanFunc n), cubeVariance h ≤ 1 →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 20 →
      (∀ i, KKL.noisyInfluence (1 - δ) i h ≤ ε) →
      ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ →
        |expect (fun x => ψ (noiseOp (1 - δ) h x)) -
          (∫ z : Fin n → ℝ,
            ψ (evalMultilinearRV (fourierCoeff (noiseOp (1 - δ) h)) (fun i z => z i) z)
            ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))| ≤
          K * (c : ℝ) * ε ^ (δ / 3) := by
  obtain ⟨K, hK, hbound⟩ := invariance_lowDegree_tail
  refine ⟨2 * K, by positivity, ?_⟩
  intro n h hvar ε δ hε hε1 hδ hδ20 hinf c ψ hψ
  have hδ1 : δ ≤ 1 := by linarith
  have hρ0 : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  have hρ1 : 1 - δ ≤ 1 := by linarith
  let k := Real.log (1 / ε) / 3
  have hk : 0 ≤ k := Invariance.invariance_cutoff_nonneg hε hε1
  have hvarNoise : cubeVariance (noiseOp (1 - δ) h) ≤ 1 :=
    (cubeVariance_noiseOp_le h (1 - δ) hρ0 hρ1).trans hvar
  have hlow (i : Fin n) :
      influence i (KKL.lowDegreePart (noiseOp (1 - δ) h) ⌊k⌋₊) ≤ ε :=
    (KKL.influence_lowDegreePart_le (noiseOp (1 - δ) h) ⌊k⌋₊ i).trans
      ((KKL.influence_noiseOp_le_noisyInfluence h i (1 - δ) hρ0 hρ1).trans (hinf i))
  have htail :
      l2Norm (KKL.highDegreePart (noiseOp (1 - δ) h) ⌊k⌋₊) ≤ ε ^ (δ / 3) := by
    simpa only [k, Invariance.invariance_cutoff_exp hε δ] using
      Invariance.highDegree_noise_l2Norm_le_exp h hvar δ hδ.le hδ1 k hk
  have hpower := Invariance.invariance_cutoff_power_le hε hε1 hδ20
  calc
    _ ≤ K * (c : ℝ) * ((2 : ℝ) ^ k * ε ^ (1 / 4 : ℝ) +
        l2Norm (KKL.highDegreePart (noiseOp (1 - δ) h) ⌊k⌋₊)) :=
      hbound (noiseOp (1 - δ) h) hvarNoise k hk ε hε.le hlow c ψ hψ
    _ ≤ K * (c : ℝ) * (ε ^ (δ / 3) + ε ^ (δ / 3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hpower htail) (mul_nonneg hK.le c.coe_nonneg)
    _ = _ := by ring

/-- Fourth-order invariance gives a fifth-root Lévy bound for degree-bounded,
variance-normalized small-influence polynomials. [OD14, Cor. 11.70, first assertion]

**Proof sketch.** Smooth half-line indicators with width η and fourth derivative
of order η⁻⁴. Balance the resulting Taylor error and CDF shifts by choosing η
proportional to the fifth root of the influence scale. -/
theorem invariance_levy :
    ∃ K : ℝ, 0 < K ∧ ∀ {n k : ℕ} {Ω Ξ : Type*}
      [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (F : MultilinearPolynomial n), F.HasDegreeAtMost k → cubeVariance F.eval ≤ 1 →
      ∀ ε : ℝ, 0 ≤ ε → (∀ i, influence i F.eval ≤ ε) →
      ∀ (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ),
      iIndepFun X μ → iIndepFun Y ν →
      (∀ i, HasInvarianceMoments (X i) μ) → (∀ i, HasInvarianceMoments (Y i) ν) →
        levyDistance (μ.map (evalMultilinearRV F X)) (ν.map (evalMultilinearRV F Y)) ≤
          K * (2 : ℝ) ^ k * ε ^ (1 / 5 : ℝ) := by
  refine ⟨13, by norm_num, ?_⟩
  intro n k Ω Ξ _ _ μ ν _ _ F hdegree hvar ε hε hinf X Y hIX hIY hX hY
  let B : ℝ := (k : ℝ) * (9 : ℝ) ^ k * ε / 12
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hU := (evalMultilinearRV_memLp F X μ hIX
    (fun i => (hX i).reasonable.memLp)).aemeasurable
  have hV := (evalMultilinearRV_memLp F Y ν hIY
    (fun i => (hY i).reasonable.memLp)).aemeasurable
  have hlevy := Invariance.levy_bound_of_derivative_map 3 hU hV B hB (by
      intro φ hφ C hC0 hC
      calc
        _ ≤ (C / 12) * (k : ℝ) * (9 : ℝ) ^ k * ε :=
          invariance_small_influences F hdegree hvar ε hε hinf X Y hIX hIY
            hX hY φ hφ C hC0 hC
        _ = C * B := by dsimp [B]; ring)
  norm_num at hlevy
  calc
    _ ≤ 13 * B ^ (1 / 5 : ℝ) := hlevy
    _ ≤ 13 * ((2 : ℝ) ^ k * ε ^ (1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Invariance.invariance_fifth_power_le k hε) (by norm_num)
    _ = _ := by ring

/-- Third-order hypercontractive invariance gives an eighth-root Lévy bound,
with universal constants in the degree exponent. [OD14, Cor. 11.70, second assertion]

**Proof sketch.** Bound the sum of influence-to-three-halves powers by the
square root of the maximum influence times total influence. Apply third-order
invariance to smooth cutoffs and balance their width and Taylor error. The scalar
hypercontractive radius bound absorbs the remaining degree factor into the
exponent of the reciprocal radius. -/
theorem invariance_c3_levy :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ {n k : ℕ} {Ω Ξ : Type*}
      [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (F : MultilinearPolynomial n), F.HasDegreeAtMost k → cubeVariance F.eval ≤ 1 →
      ∀ ε : ℝ, 0 ≤ ε → (∀ i, influence i F.eval ≤ ε) →
      ∀ (X : Fin n → Ω → ℝ) (Y : Fin n → Ξ → ℝ),
      iIndepFun X μ → iIndepFun Y ν → ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 →
      (∀ i, IsHypercontractive (X i) μ 2 3 ρ) →
      (∀ i, IsHypercontractive (Y i) ν 2 3 ρ) →
      (∀ i, (∫ ω, X i ω ∂μ) = 0) → (∀ i, (∫ ω, Y i ω ∂ν) = 0) →
      (∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1) → (∀ i, (∫ ω, Y i ω ^ 2 ∂ν) = 1) →
        levyDistance (μ.map (evalMultilinearRV F X)) (ν.map (evalMultilinearRV F Y)) ≤
          K * (1 / ρ) ^ (A * k) * ε ^ (1 / 8 : ℝ) := by
  refine ⟨8, 2, by norm_num, by norm_num, ?_⟩
  intro n k Ω Ξ _ _ μ ν _ _ F hdegree hvar ε hε hinf X Y hIX hIY
    ρ hρ hX hY hmX hmY hvX hvY
  have hρpos : 0 < ρ := hρ.1
  let B : ℝ := (1 / ρ) ^ (3 * k) *
    (∑ i : Fin n, (influence i F.eval) ^ (3 / 2 : ℝ)) / 3
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact div_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (influence_nonneg i F.eval) _))
      (by norm_num)
  have hU := (evalMultilinearRV_memLp_nat (by decide : 0 < 3) F X μ hIX
    (fun i => (hX i).2.2.2.2.1)).aemeasurable
  have hV := (evalMultilinearRV_memLp_nat (by decide : 0 < 3) F Y ν hIY
    (fun i => (hY i).2.2.2.2.1)).aemeasurable
  have hlevy := Invariance.levy_bound_of_derivative_map 2 hU hV B hB (by
    intro φ hφ C hC0 hC
    calc
      _ ≤ (C / 3) * (1 / ρ) ^ (3 * k) *
          ∑ i : Fin n, (influence i F.eval) ^ (3 / 2 : ℝ) :=
        invariance_c3 F hdegree X Y hIX hIY ρ hρ hX hY hmX hmY hvX hvY φ hφ C hC0 hC
      _ = C * B := by dsimp [B]; ring)
  norm_num at hlevy
  by_cases hn : n = 0
  · subst n
    have hBzero : B = 0 := by simp [B]
    rw [hBzero, Real.zero_rpow (by norm_num), mul_zero] at hlevy
    exact hlevy.trans (by positivity)
  · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hρmax := Invariance.hypercontractive_radius_le_five_sixths
      (hX i) hρpos (hmX i) (hvX i)
    have hr : (6 / 5 : ℝ) ≤ 1 / ρ := (le_div_iff₀ hρpos).mpr (by linarith)
    have hBbound : B ≤ (k : ℝ) * (1 / ρ) ^ (3 * k) * Real.sqrt ε / 3 := by
      calc
        _ ≤ (1 / ρ) ^ (3 * k) * ((k : ℝ) * Real.sqrt ε) / 3 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (sum_three_halves_influences_le_degree_mul F.eval
                (F.has_degree_at_most_eval hdegree) hvar ε hinf) (by positivity))
            (by norm_num)
        _ = _ := by ring
    calc
      _ ≤ 8 * B ^ (1 / 4 : ℝ) := hlevy
      _ ≤ 8 * ((k : ℝ) * (1 / ρ) ^ (3 * k) * Real.sqrt ε / 3) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hB hBbound (by norm_num)) (by norm_num)
      _ ≤ 8 * ((1 / ρ) ^ (2 * k) * ε ^ (1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Invariance.invariance_c3_quarter_power_le k hr hε)
          (by norm_num)
      _ = _ := by
        rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        ring

end BooleanAnalysis.GaussianSpace
