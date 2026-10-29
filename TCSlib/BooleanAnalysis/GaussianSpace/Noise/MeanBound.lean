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
# Bounding a probability mean by an Lp seminorm

## Main definitions

The existing Bochner integral and Lp seminorm are reused.

## Main results

* `norm_integral_le_toReal_eLpNorm`: a probability mean is bounded by every
  finite-valued Lp seminorm with exponent at least one.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian Hypercontractivity.
  This is technical probability-mean glue for the endpoint cases.
-/

open MeasureTheory
open scoped ENNReal

namespace BooleanAnalysis.GaussianSpace

/-- The absolute mean of a real Lp function on a probability space is at most
its Lp seminorm for every exponent at least one, including infinity.

**Proof sketch.** Bound the mean by the lower integral of the pointwise norm.
This is the L1 seminorm, which is at most the given Lp seminorm on a probability
space. The input's finite seminorm permits conversion back to a real bound. -/
lemma norm_integral_le_toReal_eLpNorm {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p : ℝ≥0∞) (hp : 1 ≤ p)
    {f : α → ℝ} (hf : MemLp f p μ) :
    |∫ x, f x ∂μ| ≤ (eLpNorm f p μ).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hf.2.ne).mp
  rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]
  apply (enorm_integral_le_lintegral_enorm f).trans
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact eLpNorm_le_eLpNorm_of_exponent_le hp hf.aestronglyMeasurable

end BooleanAnalysis.GaussianSpace
