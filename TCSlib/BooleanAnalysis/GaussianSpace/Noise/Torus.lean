/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.NumberTheory.Real.Irrational

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A compact torus for Gaussian polynomial approximation

## Main definitions

* `gaussianTorusMap`: retain each real coordinate modulo one at two
  incommensurable frequencies.
* `gaussianTorusFourierLp`: torus Fourier monomials pulled back to real vectors.
* `gaussianTorusFrequency`: the real frequency of each pulled-back Fourier monomial.

## Main results

* `gaussianTorusMap_injective`: the two frequencies distinguish real vectors.
* `measurableEmbedding_gaussianTorusMap`: the map preserves measurable information.
* `mFourier_gaussianTorusMap`: pulled-back Fourier monomials are linear phases.
* `span_mFourier_toLp_dense`: Fourier monomials are dense for any finite torus measure.
* `span_gaussianTorusFourier_dense`: their pullbacks are dense on real vectors.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Theorem 11.22. The compact torus is an
  auxiliary approximation device for the polynomial density theorem.
-/

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

variable {n : ℕ}

/-- Each coordinate is recorded modulo one, both directly and after multiplication
by `√2`. These two frequencies retain all information about the real vector. -/
noncomputable def gaussianTorusMap (x : Fin n → ℝ) : UnitAddTorus (Fin n × Bool) :=
  fun j => ((if j.2 then Real.sqrt 2 * x j.1 else x j.1 : ℝ) : UnitAddCircle)

/-- The two incommensurable frequencies make the torus map injective.

**Proof sketch.** Equal images make both a coordinate difference and its `√2`
multiple integers. Irrationality of `√2` forces the difference to vanish. -/
lemma gaussianTorusMap_injective : Function.Injective (gaussianTorusMap (n := n)) := by
  intro x y hxy
  funext i
  have h₀ : (x i : UnitAddCircle) = (y i : UnitAddCircle) := congrFun hxy (i, false)
  have h₁ : ((Real.sqrt 2 * x i : ℝ) : UnitAddCircle) =
      ((Real.sqrt 2 * y i : ℝ) : UnitAddCircle) := congrFun hxy (i, true)
  have hd₀ : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, h₀, sub_self]
  have hd₁ : ((Real.sqrt 2 * x i - Real.sqrt 2 * y i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, h₁, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hd₀
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hd₁
  simp only [zsmul_eq_mul, mul_one] at hm hk
  have hm₀ : m = 0 := by
    by_contra hm₀
    apply (irrational_sqrt_two.mul_intCast hm₀).ne_int k
    rw [hm]
    nlinarith [hk]
  exact sub_eq_zero.mp (by simpa only [hm₀, Int.cast_zero] using hm.symm)

/-- The torus map is continuous. -/
@[fun_prop]
lemma continuous_gaussianTorusMap : Continuous (gaussianTorusMap (n := n)) := by
  apply continuous_pi
  rintro ⟨i, b⟩
  cases b
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      (continuous_const.mul (continuous_apply i))

/-- A real vector can be recovered measurably from its two-frequency torus image.
The inverse is only asserted to be measurable on the image. -/
lemma measurableEmbedding_gaussianTorusMap :
    MeasurableEmbedding (gaussianTorusMap (n := n)) :=
  continuous_gaussianTorusMap.measurableEmbedding gaussianTorusMap_injective

/-- A torus Fourier monomial pulls back to the exponential of a real linear form.
This identifies the compact approximation functions with Gaussian Taylor inputs. -/
lemma mFourier_gaussianTorusMap (m : (Fin n × Bool) → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier m (gaussianTorusMap x) =
      Complex.exp (((∑ i, (2 * Real.pi * ((m (i, false) : ℝ) +
        Real.sqrt 2 * (m (i, true) : ℝ))) * x i : ℝ) : ℂ) * Complex.I) := by
  change (∏ j : Fin n × Bool, fourier (m j)
    (((if j.2 then Real.sqrt 2 * x j.1 else x j.1 : ℝ) : UnitAddCircle))) = _
  simp_rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, Fintype.sum_prod_type]
  congr 1
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  rw [Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- Fourier monomials span a dense subspace of finite Lp for every finite Borel
measure on a finite-dimensional torus; no Haar-measure assumption is needed.

**Proof sketch.** Their span is uniformly dense among continuous functions by
Stone–Weierstrass. Map that span into Lp, where continuous functions are dense. -/
lemma span_mFourier_toLp_dense {ι : Type*} [Fintype ι]
    (μ : Measure (UnitAddTorus ι)) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (Submodule.span ℂ (Set.range (fun m : ι → ℤ =>
      ContinuousMap.toLp (E := ℂ) p μ ℂ (UnitAddTorus.mFourier m)))).topologicalClosure = ⊤ := by
  simpa only [Submodule.map_span, ContinuousLinearMap.coe_coe, ← Set.range_comp,
    Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ μ ℂ hp).topologicalClosure_map_submodule
      (UnitAddTorus.span_mFourier_closure_eq_top (d := ι))

/-- Pullback from the image measure on the torus covers the entire real or
complex Lp space of real vectors.

**Proof sketch.** Extend a measurable representative from the Borel image of the
injective torus map. The pushforward measure gives its extension the same norm. -/
lemma surjective_gaussianTorus_pullback {𝕜 : Type*} [RCLike 𝕜]
    (μ : Measure (Fin n → ℝ))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Surjective (Lp.compMeasurePreservingₗᵢ 𝕜 gaussianTorusMap
      ⟨continuous_gaussianTorusMap.measurable, rfl⟩ :
      Lp 𝕜 p (μ.map gaussianTorusMap) → Lp 𝕜 p μ) := by
  intro f
  obtain ⟨F, _, heq⟩ := measurableEmbedding_gaussianTorusMap.exists_measurable_extend
    (Lp.stronglyMeasurable f).measurable (fun _ => inferInstance)
  have hFmem : MemLp F p (μ.map gaussianTorusMap) :=
    measurableEmbedding_gaussianTorusMap.memLp_map_measure_iff.mpr
      (by rw [heq]; exact Lp.memLp f)
  refine ⟨hFmem.toLp F, ?_⟩
  change Lp.compMeasurePreserving _ _ (hFmem.toLp F) = f
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (Filter.Eventually.of_forall fun x => congrFun heq x)

/-- A Fourier monomial on the compact torus, considered as an Lp function of
real vectors through the two-frequency map. -/
noncomputable def gaussianTorusFourierLp (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : (Fin n × Bool) → ℤ) : Lp ℂ p μ :=
  Lp.compMeasurePreserving gaussianTorusMap ⟨continuous_gaussianTorusMap.measurable, rfl⟩
    (ContinuousMap.toLp (E := ℂ) p (μ.map gaussianTorusMap) ℂ (UnitAddTorus.mFourier m))

/-- The pulled-back Fourier class is represented almost everywhere by the
pointwise composition with the torus map. -/
lemma coeFn_gaussianTorusFourierLp (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : (Fin n × Bool) → ℤ) :
    gaussianTorusFourierLp μ p m =ᵐ[μ]
      fun x => UnitAddTorus.mFourier m (gaussianTorusMap x) := by
  apply (Lp.coeFn_compMeasurePreserving _ _).trans
  exact ae_of_ae_map continuous_gaussianTorusMap.measurable.aemeasurable
      (ContinuousMap.coeFn_toLp (μ.map gaussianTorusMap) (UnitAddTorus.mFourier m))

/-- Pulled-back Fourier monomials span a dense subspace for any finite measure
on real vectors and any finite exponent at least one.

**Proof sketch.** Fourier monomials are dense for the torus image measure.
The continuous pullback is surjective because the torus map is a measurable embedding. -/
lemma span_gaussianTorusFourier_dense (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (Submodule.span ℂ (Set.range (gaussianTorusFourierLp μ p))).topologicalClosure = ⊤ := by
  let L : Lp ℂ p (μ.map gaussianTorusMap) →L[ℂ] Lp ℂ p μ :=
    (Lp.compMeasurePreservingₗᵢ ℂ gaussianTorusMap
    (show MeasurePreserving gaussianTorusMap μ (μ.map gaussianTorusMap) from
      ⟨continuous_gaussianTorusMap.measurable, rfl⟩)).toContinuousLinearMap
  have hL : DenseRange L := (surjective_gaussianTorus_pullback (𝕜 := ℂ) μ p).denseRange
  simpa only [Submodule.map_span, ContinuousLinearMap.coe_coe, ← Set.range_comp,
    Function.comp_def, L, gaussianTorusFourierLp] using
    hL.topologicalClosure_map_submodule
      (span_mFourier_toLp_dense (μ.map gaussianTorusMap) p hp)

/-- The real-coordinate frequency corresponding to an integer Fourier frequency
on the two-frequency torus. -/
noncomputable def gaussianTorusFrequency (m : (Fin n × Bool) → ℤ) (i : Fin n) : ℝ :=
  2 * Real.pi * ((m (i, false) : ℝ) + Real.sqrt 2 * (m (i, true) : ℝ))

end BooleanAnalysis.GaussianSpace
