/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.ThirdMoments
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Sequence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Third-order coordinate replacement

## Main definitions

The existing affine coordinate decomposition and hybrid input family are reused.

## Main results

* `single_coordinate_replacement_bound_c3`: the one-coordinate third-order estimate.
* `invariance_c3_of_independent_pair`: the estimate summed along independent replacements.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Remark 11.66.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanAnalysis.GaussianSpace.Invariance

open ThresholdFunctions Hypercontractivity

/-- Absolute power moments factor over independent inputs. This specializes
Mathlib's independence integration formula and is technical replacement glue. -/
private lemma integral_abs_mul_pow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U V : Ω → ℝ) (hU : AEMeasurable U μ) (hV : AEMeasurable V μ)
    (hind : IndepFun U V μ) (p : ℕ) :
    (∫ ω, |U ω * V ω| ^ p ∂μ) =
      (∫ ω, |U ω| ^ p ∂μ) * (∫ ω, |V ω| ^ p ∂μ) := by
  simpa only [abs_mul, mul_pow] using
    hind.integral_fun_comp_mul_comp hU hV
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x| ^ p) (μ.map U))
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x| ^ p) (μ.map V))

/-- Replacing one coordinate of a standardized hypercontractive input family costs
at most `(C/3) ρ^(-3k) Infᵢ(F)^(3/2)`. [OD14, Remark 11.66]

**Proof sketch.** Split off the coordinate from its independent background.
Quadratic Taylor replacement leaves two cubic remainders. Factor their moments
by independence and bound the coordinate-containing polynomial in each family. -/
theorem single_coordinate_replacement_bound_c3
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (i : Fin n) (X Y : Fin n → Ω → ℝ)
    (hIX : iIndepFun X μ) (hIY : iIndepFun Y μ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hX : ∀ j, IsHypercontractive (X j) μ 2 3 ρ)
    (hY : ∀ j, IsHypercontractive (Y j) μ 2 3 ρ)
    (hmX : ∀ j, (∫ ω, X j ω ∂μ) = 0)
    (hmY : ∀ j, (∫ ω, Y j ω ∂μ) = 0)
    (hvX : ∀ j, (∫ ω, X j ω ^ 2 ∂μ) = 1)
    (hvY : ∀ j, (∫ ω, Y j ω ^ 2 ∂μ) = 1)
    (hXY : ∀ j, j ≠ i → X j = Y j)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ)
    (C : ℝ) (hC0 : 0 ≤ C) (hderiv : ∀ t, |iteratedDeriv 3 ψ t| ≤ C) :
    |(∫ ω, ψ (evalMultilinearRV F X ω) ∂μ) -
      (∫ ω, ψ (evalMultilinearRV F Y ω) ∂μ)| ≤
      (C / 3) * (1 / ρ) ^ (3 * k) * (influence i F.eval) ^ (3 / 2 : ℝ) := by
  classical
  let A := evalMultilinearRV (coordinateFree F i) X
  let D := evalMultilinearRV (coordinateDerivative F i) X
  obtain ⟨hAeq, hDeq⟩ := coordinate_parts_eq_of_off_coordinate F i X Y hXY
  change A = evalMultilinearRV (coordinateFree F i) Y at hAeq
  change D = evalMultilinearRV (coordinateDerivative F i) Y at hDeq
  have hsplitX : evalMultilinearRV F X = fun ω => A ω + D ω * X i ω := by
    funext ω
    simpa only [A, D, mul_comm] using eval_coordinate_split F i X ω
  have hsplitY : evalMultilinearRV F Y = fun ω => A ω + D ω * Y i ω := by
    funext ω
    rw [eval_coordinate_split, ← hAeq, ← hDeq]
    ring
  have hXm (j : Fin n) : MemLp (X j) 3 μ := (hX j).2.2.2.2.1
  have hYm (j : Fin n) : MemLp (Y j) 3 μ := (hY j).2.2.2.2.1
  have hAmem : MemLp A 3 μ := evalMultilinearRV_memLp_nat (by norm_num : 0 < 3) _ X μ hIX hXm
  have hDmem : MemLp D 3 μ := evalMultilinearRV_memLp_nat (by norm_num : 0 < 3) _ X μ hIX hXm
  have hIXAD : IndepFun (X i) (fun ω => (A ω, D ω)) μ :=
    indep_coordinate_parts hIX (fun j => (hXm j).aemeasurable) F i
  have hIYAD : IndepFun (Y i) (fun ω => (A ω, D ω)) μ := by
    rw [hAeq, hDeq]
    exact indep_coordinate_parts hIY (fun j => (hYm j).aemeasurable) F i
  have hfactor (W : Ω → ℝ) (hW : AEMeasurable W μ)
      (hind : IndepFun W (fun ω => (A ω, D ω)) μ) :=
    integral_abs_mul_pow W D hW hDmem.aemeasurable
      (hind.comp measurable_id measurable_snd) 3
  have hboundX := coordinate_abs_third_moment F hdegree i X hIX ρ hρ hX hmX hvX
  change (∫ ω, |X i ω * D ω| ^ 3 ∂μ) ≤ _ at hboundX
  have hboundY := coordinate_abs_third_moment F hdegree i Y hIY ρ hρ hY hmY hvY
  rw [← hDeq] at hboundY
  have hψX := integrable_test_of_memLp 2
    (evalMultilinearRV_memLp_nat (by norm_num : 0 < 3) F X μ hIX hXm) ψ hψ C hderiv
  have hψY := integrable_test_of_memLp 2
    (evalMultilinearRV_memLp_nat (by norm_num : 0 < 3) F Y μ hIY hYm) ψ hψ C hderiv
  calc
    _ ≤ (C / 6) * ((∫ ω, |X i ω| ^ 3 ∂μ) + ∫ ω, |Y i ω| ^ 3 ∂μ) *
        (∫ ω, |D ω| ^ 3 ∂μ) := by
      rw [hsplitX, hsplitY]
      exact independent_affine_replacement_bound_c3 A D (X i) (Y i)
        (hAmem.aemeasurable.prodMk hDmem.aemeasurable) hDmem (hXm i) (hYm i)
        (by rw [hmX, hmY]) (by rw [hvX, hvY]) hIXAD hIYAD ψ hψ C hderiv
        (by simpa only [hsplitX] using hψX) (by simpa only [hsplitY] using hψY)
    _ = (C / 6) * ((∫ ω, |X i ω * D ω| ^ 3 ∂μ) +
        ∫ ω, |Y i ω * D ω| ^ 3 ∂μ) := by
      rw [hfactor (X i) (hXm i).aemeasurable hIXAD,
        hfactor (Y i) (hYm i).aemeasurable hIYAD]
      ring
    _ ≤ (C / 6) * ((1 / ρ) ^ (3 * k) * (influence i F.eval) ^ (3 / 2 : ℝ) +
        (1 / ρ) ^ (3 * k) * (influence i F.eval) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hboundX hboundY) (by positivity)
    _ = _ := by ring

/-- Mutually independent copies of standardized hypercontractive coordinates
satisfy third-order invariance. [OD14, Remark 11.66]

**Proof sketch.** Each hybrid selects distinct independent inputs. Apply the
single-coordinate estimate and sum the errors along the replacement sequence. -/
theorem invariance_c3_of_independent_pair
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (Z : (Fin n ⊕ Fin n) → Ω → ℝ) (hIZ : iIndepFun Z μ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hZ : ∀ a, IsHypercontractive (Z a) μ 2 3 ρ)
    (hmZ : ∀ a, (∫ ω, Z a ω ∂μ) = 0)
    (hvZ : ∀ a, (∫ ω, Z a ω ^ 2 ∂μ) = 1)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ)
    (C : ℝ) (hC0 : 0 ≤ C) (hderiv : ∀ t, |iteratedDeriv 3 ψ t| ≤ C) :
    |(∫ ω, ψ (evalMultilinearRV F (fun i => Z (Sum.inl i)) ω) ∂μ) -
      (∫ ω, ψ (evalMultilinearRV F (fun i => Z (Sum.inr i)) ω) ∂μ)| ≤
      (C / 3) * (1 / ρ) ^ (3 * k) *
        ∑ i : Fin n, (influence i F.eval) ^ (3 / 2 : ℝ) := by
  classical
  have hI (r : ℕ) : iIndepFun (hybridInput Z r) μ :=
    iIndepFun.precomp (f := Z) (g := hybridIndex r) (hybridIndex_injective r) hIZ
  calc
    _ ≤ ∑ i : Fin n,
        (C / 3) * (1 / ρ) ^ (3 * k) * (influence i F.eval) ^ (3 / 2 : ℝ) := by
      apply hybrid_expectation_bound
      intro i
      exact single_coordinate_replacement_bound_c3 F hdegree i
        (hybridInput Z i.val) (hybridInput Z (i.val + 1))
        (hI i.val) (hI (i.val + 1)) ρ hρ
        (fun j => hZ (hybridIndex i.val j))
        (fun j => hZ (hybridIndex (i.val + 1) j))
        (fun j => hmZ (hybridIndex i.val j))
        (fun j => hmZ (hybridIndex (i.val + 1) j))
        (fun j => hvZ (hybridIndex i.val j))
        (fun j => hvZ (hybridIndex (i.val + 1) j))
        (fun j hji => hybridInput_succ_off Z i j hji) ψ hψ C hC0 hderiv
    _ = _ := by rw [Finset.mul_sum]

end BooleanAnalysis.GaussianSpace.Invariance
