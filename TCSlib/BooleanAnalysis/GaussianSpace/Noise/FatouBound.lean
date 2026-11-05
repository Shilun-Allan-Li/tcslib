/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Passing nonnegative integral bounds to almost-everywhere limits

## Main definitions

The existing Bochner integral and lower Lebesgue integral are reused.

## Main results

* `integrable_and_integral_le_of_nonneg_tendsto`: convergent bounds on
  nonnegative integrals give integrability and the corresponding limit bound.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian Hypercontractivity.
  This is technical limit-passage glue for the approximation argument.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

/-- An almost-everywhere limit of nonnegative integrable functions is integrable
when their integrals have convergent finite upper bounds; its integral is at most
the limiting bound.

**Proof sketch.** Fatou's lemma bounds the lower integral of the limit's norm by
the lower limit of the approximants' norm integrals. Nonnegativity identifies
these with the given integrals. The finite limiting bound gives integrability,
and the real integral is bounded by the integral of the norm. -/
lemma integrable_and_integral_le_of_nonneg_tendsto {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℕ → ℝ} {c : ℝ}
    (hF : ∀ m, Integrable (F m) μ) (hF0 : ∀ m, 0 ≤ᵐ[μ] F m)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => F m x) atTop (𝓝 (f x)))
    (hf : AEStronglyMeasurable f μ) (hbound : ∀ m, (∫ x, F m x ∂μ) ≤ C m)
    (hC : Tendsto C atTop (𝓝 c)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ c := by
  have hnorm (m : ℕ) :
      (∫⁻ x, ‖F m x‖ₑ ∂μ) = ENNReal.ofReal (∫ x, F m x ∂μ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF m)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hF0 m] with x hx
    exact Real.norm_of_nonneg hx
  have hfatou : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤ ENNReal.ofReal c := by
    calc
      _ = ∫⁻ x, liminf (fun m => ‖F m x‖ₑ) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact hx.enorm.liminf_eq.symm
      _ ≤ liminf (fun m => ∫⁻ x, ‖F m x‖ₑ ∂μ) atTop :=
        lintegral_liminf_le' (fun m => (hF m).aestronglyMeasurable.enorm)
      _ = liminf (fun m => ENNReal.ofReal (∫ x, F m x ∂μ)) atTop := by
        simp_rw [hnorm]
      _ ≤ liminf (fun m => ENNReal.ofReal (C m)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun m => ENNReal.ofReal_le_ofReal (hbound m))
      _ = ENNReal.ofReal c := (ENNReal.tendsto_ofReal hC).liminf_eq
  have hfi : Integrable f μ :=
    ⟨hf, hasFiniteIntegral_iff_enorm.mpr (hfatou.trans_lt ENNReal.ofReal_lt_top)⟩
  have hc0 : 0 ≤ c :=
    ge_of_tendsto hC (Eventually.of_forall fun m =>
      (integral_nonneg_of_ae (hF0 m)).trans (hbound m))
  have hintnorm : (∫ x, ‖f x‖ ∂μ) ≤ c := by
    apply (ENNReal.ofReal_le_ofReal_iff hc0).mp
    rwa [ofReal_integral_norm_eq_lintegral_enorm hfi]
  refine ⟨hfi, ?_⟩
  calc
    (∫ x, f x ∂μ) ≤ |∫ x, f x ∂μ| := le_abs_self _
    _ ≤ ∫ x, ‖f x‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
    _ ≤ c := hintnorm

end BooleanAnalysis.GaussianSpace
