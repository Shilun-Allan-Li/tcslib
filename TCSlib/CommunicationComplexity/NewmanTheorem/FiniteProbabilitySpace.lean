/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.ConditionalProbability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite Probability Spaces

## Main results

- `CommunicationComplexity.FiniteMeasureSpace`: Typeclass for finite measurable spaces with discrete measurable structure.
- `CommunicationComplexity.FiniteProbabilitySpace`: Typeclass hierarchy bundling a finite measurable space with a probability measure.
- `FiniteProbabilitySpace.measureReal_prod`: The real-valued measure of a measurable rectangle in a product finite probability space factors as the product of the two measures.
- `FiniteProbabilitySpace.integral_eq_pmf_sum`: On a finite probability space, integrating a real-valued function equals a finite weighted sum over the PMF.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace CommunicationComplexity

/-- A finite measurable space: the type is finite and the measurable
structure is discrete. This deliberately does not include a measure. -/
class FiniteMeasureSpace (Ω : Type*) [MeasurableSpace Ω] where
  fintype :
    Fintype Ω
  discrete :
    DiscreteMeasurableSpace Ω

attribute [instance] FiniteMeasureSpace.fintype
attribute [instance] FiniteMeasureSpace.discrete

/-- Helper for bundling already-existing finite measurable-space instances locally. -/
def FiniteMeasureSpace.of
    (Ω : Type*) [MeasurableSpace Ω] [Fintype Ω] [DiscreteMeasurableSpace Ω] :
    FiniteMeasureSpace Ω :=
{ fintype := inferInstance
  discrete := inferInstance }

class FiniteProbabilitySpace (Ω : Type*) where
  toMeasureSpace : MeasureSpace Ω
  finite :
    @FiniteMeasureSpace Ω toMeasureSpace.toMeasurableSpace
  prob :
    @IsProbabilityMeasure Ω
      toMeasureSpace.toMeasurableSpace toMeasureSpace.volume

attribute [instance] FiniteProbabilitySpace.toMeasureSpace
attribute [instance] FiniteProbabilitySpace.finite
attribute [instance] FiniteProbabilitySpace.prob

/-- Helper for bundling already-existing instances locally. -/
def FiniteProbabilitySpace.of
    (Ω : Type*)
    [m : MeasureSpace Ω]
    [Fintype Ω]
    [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] :
    FiniteProbabilitySpace Ω :=
{ toMeasureSpace := m
  finite := FiniteMeasureSpace.of Ω
  prob := inferInstance }

/-- Build a finite probability space from a finite measurable space and an unbundled probability
measure. -/
noncomputable def FiniteProbabilitySpace.ofMeasure
    (Ω : Type*) [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    FiniteProbabilitySpace Ω :=
{ toMeasureSpace :=
    { toMeasurableSpace := inferInstance
      volume := μ }
  finite := inferInstance
  prob := inferInstance }

open Classical in
/-- A finite measure on a finite measurable space is determined by its singleton masses. -/
theorem FiniteMeasureSpace.measureReal_eq_sum_singletons
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) :
    μ.real S =
      ∑ ω : Ω, if ω ∈ S then μ.real ({ω} : Set Ω) else 0 := by
  let T : Finset Ω := Finset.univ.filter fun ω : Ω => ω ∈ S
  have hST : (↑T : Set Ω) = S := by
    ext ω
    simp [T]
  rw [← hST]
  rw [← MeasureTheory.sum_measureReal_singleton (μ := μ) T]
  simp [T, Finset.sum_filter]

open Classical in
/-- On a finite measurable space, the real measure of a preimage event is the sum of the
real masses of the fibers that imply the event. -/
theorem FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers
    {Ω α : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    [Fintype α] (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → α) (P : α → Prop) :
    μ.real {ω | P (Z ω)} =
      ∑ z : α, if P z then μ.real (Z ⁻¹' {z}) else 0 := by
  rw [FiniteMeasureSpace.measureReal_eq_sum_singletons μ {ω | P (Z ω)}]
  symm
  calc
    (∑ z : α, if P z then μ.real (Z ⁻¹' {z}) else 0)
        = ∑ z : α, if P z then
            ∑ ω : Ω, if Z ω = z then μ.real ({ω} : Set Ω) else 0
          else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : P z
        · simp [hz, FiniteMeasureSpace.measureReal_eq_sum_singletons μ
            (Z ⁻¹' {z} : Set Ω)]
        · simp [hz]
    _ = ∑ z : α, ∑ ω : Ω,
          if P z ∧ Z ω = z then μ.real ({ω} : Set Ω) else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : P z <;> simp [hz]
    _ = ∑ ω : Ω, ∑ z : α,
          if P z ∧ Z ω = z then μ.real ({ω} : Set Ω) else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ ω : Ω, if P (Z ω) then μ.real ({ω} : Set Ω) else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hP : P (Z ω)
        · rw [Finset.sum_eq_single (Z ω)]
          · simp [hP]
          · intro z _ hz_ne
            simp [hz_ne.symm]
          · intro hnot
            simp at hnot
        · rw [Finset.sum_eq_zero]
          · simp [hP]
          · intro z _
            by_cases hz : P z ∧ Z ω = z
            · exact (hP (by rw [hz.2]; exact hz.1)).elim
            · simp [hz]

open Classical in
/-- On a finite measurable space, absolute continuity is equivalent to absolute continuity on
singleton masses. -/
theorem FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω] {μ ν : Measure Ω} :
    μ ≪ ν ↔ ∀ ω, ν ({ω} : Set Ω) = 0 → μ ({ω} : Set Ω) = 0 := by
  constructor
  · intro h ω hν
    exact h hν
  · intro h S hνS
    let T : Finset Ω := Finset.univ.filter fun ω : Ω => ω ∈ S
    have hST : (↑T : Set Ω) = S := by
      ext ω
      simp [T]
    rw [← hST]
    rw [← MeasureTheory.sum_measure_singleton (μ := μ) (s := T)]
    apply Finset.sum_eq_zero
    intro ω hω
    exact h ω (measure_mono_null (μ := ν) (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      simpa [T] using hω) hνS)

/-- For any probability measure on a finite measurable space, the square of an expectation is
bounded by the expectation of the square. -/
theorem FiniteMeasureSpace.sq_integral_le_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    (∫ ω, f ω ∂μ)^2 ≤ ∫ ω, (f ω)^2 ∂μ :=
  ConvexOn.map_integral_le
    (by simpa using (show ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) from
      Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)))
    (by simpa using
      (show ContinuousOn (fun x : ℝ => x ^ 2) Set.univ from
        (continuous_pow 2).continuousOn))
    isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    Integrable.of_finite
    Integrable.of_finite

open Classical in
/-- On a finite measurable space, the integral of a function of a finite-valued random variable
is the sum over its fibers. -/
theorem FiniteMeasureSpace.integral_comp_eq_sum_measureReal_fibers
    {Ω α : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Fintype α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → α) (f : α → ℝ) :
    ∫ ω, f (Z ω) ∂μ = ∑ z : α, μ.real (Z ⁻¹' {z}) * f z := by
  have hmap :
      ∫ ω, f (Z ω) ∂μ = ∫ z, f z ∂Measure.map Z μ := by
    exact (integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  rw [hmap]
  rw [MeasureTheory.integral_fintype f Integrable.of_finite]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_measureReal_apply Measurable.of_discrete MeasurableSet.of_discrete]

open Classical in
/-- Law of total probability over the fibers of a finite-valued random variable, in real-valued
measure form. -/
theorem FiniteMeasureSpace.measureReal_eq_sum_cond_fiber_real
    {Ω α : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Fintype α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → α) (S : Set Ω) :
    μ.real S =
      ∑ z : α, μ.real (Z ⁻¹' {z}) * (μ[|(Z ⁻¹' {z})]).real S := by
  have htotal := ProbabilityTheory.sum_meas_smul_cond_fiber (X := Z) Measurable.of_discrete μ
  have hS : (∑ z, μ (Z ⁻¹' {z}) • μ[|(Z ⁻¹' {z})]) S = μ S := by
    rw [htotal]
  rw [Measure.real, ← hS]
  simp only [Measure.real, Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z _
    rw [ENNReal.toReal_mul]
  · intro z _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

instance finiteMeasureSpaceBool : FiniteMeasureSpace Bool :=
  FiniteMeasureSpace.of Bool

noncomputable instance finiteMeasureSpaceProd
    (Ω₁ Ω₂ : Type*) [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [FiniteMeasureSpace Ω₁] [FiniteMeasureSpace Ω₂] :
    FiniteMeasureSpace (Ω₁ × Ω₂) :=
  FiniteMeasureSpace.of (Ω₁ × Ω₂)

open Classical in
noncomputable instance finiteMeasureSpacePi
    {ι : Type*} [Fintype ι] (Ω : ι → Type*) [∀ i, MeasurableSpace (Ω i)]
    [∀ i, FiniteMeasureSpace (Ω i)] :
    FiniteMeasureSpace ((i : ι) → Ω i) :=
  FiniteMeasureSpace.of ((i : ι) → Ω i)

noncomputable instance instProd (Ω₁ Ω₂ : Type*)
    [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂] :
    FiniteProbabilitySpace (Ω₁ × Ω₂) :=
  FiniteProbabilitySpace.of (Ω₁ × Ω₂)

open Classical in
noncomputable instance instPi
    {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, FiniteProbabilitySpace (Ω i)] :
    FiniteProbabilitySpace ((i : ι) → Ω i) :=
  FiniteProbabilitySpace.of ((i : ι) → Ω i)

open Classical in
/-- On a finite discrete type with the uniform measure on `Set.univ`,
the real-valued measure of a set is its cardinality divided by the size
of the ambient type. -/
theorem uniformOn_univ_measureReal_eq_card_filter
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (S : Set Ω) :
    ((ProbabilityTheory.uniformOn Set.univ : Measure Ω) S).toReal =
      ((Finset.univ.filter fun ω : Ω => ω ∈ S).card : ℝ) / Fintype.card Ω := by
  rw [ProbabilityTheory.uniformOn_univ, ENNReal.toReal_div,
    Measure.count_apply MeasurableSet.of_discrete,
    Set.encard_eq_coe_toFinset_card]
  simp [ENat.toENNReal_coe, ENNReal.toReal_natCast]

open Classical in
/-- On a finite discrete type with the uniform measure on `Set.univ`, the real-valued measure of
a set is the cardinality of the corresponding subtype divided by the size of the ambient type. -/
theorem uniformOn_univ_measureReal_eq_card_subtype
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (S : Set Ω) [Fintype {ω : Ω // ω ∈ S}] :
    ((ProbabilityTheory.uniformOn Set.univ : Measure Ω) S).toReal =
      (Fintype.card {ω : Ω // ω ∈ S} : ℝ) / Fintype.card Ω := by
  rw [uniformOn_univ_measureReal_eq_card_filter]
  congr 1
  exact_mod_cast (by simp [Fintype.card_subtype])

namespace FiniteProbabilitySpace

/-- You usually won't need this theorem explicitly, because of the instance below. -/
theorem nonempty
    {Ω : Type*} [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  (nonempty_of_measure_ne_zero (s := Set.univ) (μ := (volume : Measure Ω))
    (by simp)).to_type

instance (priority := 100) instNonempty
    (Ω : Type*) [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  FiniteProbabilitySpace.nonempty (Ω := Ω)

def toPMF (Ω : Type*) [FiniteProbabilitySpace Ω] : PMF Ω :=
  (volume : Measure Ω).toPMF

open Classical in
theorem measure_eq {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume S = ∑ ω : S, toPMF Ω ω := by
  have hμ : (toPMF Ω).toMeasure = (volume : Measure Ω) := by
    simp only [toPMF, Measure.toPMF_toMeasure]
  rw [← hμ]
  rw [PMF.toMeasure_apply (p := toPMF Ω) (s := S) MeasurableSet.of_discrete]
  rw [← tsum_subtype S (toPMF Ω), tsum_fintype]

/-- The singleton masses of a finite probability space sum to `1` along
any finite enumeration. -/
theorem hasSum_measure_singletons
    {Ω α : Type*} [FiniteProbabilitySpace Ω] [Finite α]
    (e : Ω ≃ α) :
    HasSum (fun a : α => volume ({e.symm a} : Set Ω)) 1 := by
  have huniv : (Set.univ : Set Ω) = ⋃ a : α, {e.symm a} := by
    ext x
    simp
  rw [show 1 = volume (Set.univ : Set Ω) from measure_univ.symm]
  rw [huniv]
  rw [measure_iUnion
    (fun a b hab => Set.disjoint_singleton.mpr (e.symm.injective.ne hab))
    (fun _ => MeasurableSet.of_discrete)]
  exact ENNReal.summable.hasSum

theorem pmf_prod {Ω₁ Ω₂ : Type*}
    [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂] :
    ∀ x y, toPMF (Ω₁ × Ω₂) (x, y) = (toPMF Ω₁ x) * (toPMF Ω₂ y) := by
  intro x y
  -- toPMF Ω (x,y) = volume {(x,y)} = volume ({x} ×ˢ {y}) = volume {x} * volume {y}
  simp only [toPMF, Measure.toPMF_apply]
  rw [show ({(x, y)} : Set (Ω₁ × Ω₂)) = {x} ×ˢ {y} from by ext; simp [Prod.ext_iff]]
  rw [show (volume : Measure (Ω₁ × Ω₂)) = volume.prod volume from rfl]
  rw [Measure.prod_prod]

/-- The real-valued measure of a measurable rectangle in a product
finite probability space factors as the product of the two measures. -/
theorem measureReal_prod
    {Ω₁ Ω₂ : Type*} [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂]
    (A : Set Ω₁) (B : Set Ω₂) :
    volume.real (A ×ˢ B : Set (Ω₁ × Ω₂)) =
      volume.real A * volume.real B := by
  rw [Measure.real, Measure.real, Measure.real]
  rw [show (volume : Measure (Ω₁ × Ω₂)) = volume.prod volume from rfl]
  rw [Measure.prod_prod, ENNReal.toReal_mul]

/-- The real-valued measure of a finite disjoint union is the sum of
the real-valued measures of its parts. -/
theorem measureReal_iUnion_fintype
    {Ω ι : Type*} [FiniteProbabilitySpace Ω] [Fintype ι]
    (A : ι → Set Ω) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    volume.real (⋃ i, A i) = ∑ i, volume.real (A i) := by
  rw [Measure.real]
  rw [measure_iUnion hdisj (fun _ => MeasurableSet.of_discrete),
    tsum_fintype, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [Measure.real]

/-- The real-valued measure of the preimage of a finite set splits as
a sum over singleton fibers. -/
theorem measureReal_preimage_finset
    {Ξ Ω : Type*} [FiniteProbabilitySpace Ξ]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (φ : Ξ → Ω) (T : Finset Ω) :
    volume.real (φ ⁻¹' (↑T : Set Ω) : Set Ξ) =
      ∑ a ∈ T, volume.real (φ ⁻¹' ({a} : Set Ω) : Set Ξ) := by
  rw [Measure.real]
  rw [show (φ ⁻¹' (↑T : Set Ω) : Set Ξ) = ⋃ a ∈ T, φ ⁻¹' ({a} : Set Ω) from by
    ext ξ
    simp]
  rw [measure_biUnion_finset
    (fun a _ b _ h => Disjoint.preimage _ (Set.disjoint_singleton.mpr h))
    (fun _ _ => MeasurableSet.of_discrete)]
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [Measure.real]

/-- The real-valued measure of a finite set splits as a sum over its singleton parts. -/
theorem measureReal_finset
    {Ω : Type*} [FiniteProbabilitySpace Ω] (T : Finset Ω) :
    volume.real (↑T : Set Ω) = ∑ a ∈ T, volume.real ({a} : Set Ω) := by
  exact measureReal_preimage_finset id T

/-- On a finite probability space, integrating a real-valued function is a finite weighted sum. -/
theorem integral_eq_pmf_sum {Ω : Type*} [FiniteProbabilitySpace Ω]
    (f : Ω → ℝ) :
    ∫ ω, f ω = ∑ ω : Ω, (toPMF Ω ω).toReal * f ω := by
  rw [MeasureTheory.integral_fintype f (Integrable.of_finite)]; congr 1

/-- On a finite probability space, the square of an expectation is bounded by the expectation of
the square. -/
theorem sq_integral_le_integral_sq
    {Ω : Type*} [FiniteProbabilitySpace Ω] (f : Ω → ℝ) :
    (∫ ω, f ω)^2 ≤ ∫ ω, (f ω)^2 :=
  FiniteMeasureSpace.sq_integral_le_integral_sq volume f

/-- Integrating a function over a coordinate of a finite product space is the same as
integrating it over the original finite probability space. -/
theorem integral_comp_eval
    {ι Ω : Type*} [Fintype ι] [FiniteProbabilitySpace Ω]
    (i : ι) (f : Ω → ℝ) :
    ∫ ωs : (j : ι) → Ω, f (ωs i) = ∫ ω, f ω := by
  let ν : Measure ((j : ι) → Ω) := Measure.pi fun _ : ι => (volume : Measure Ω)
  have hmap := measurePreserving_eval (μ := fun (_ : ι) => (volume : Measure Ω)) i
  have h1 :
      ∫ ωs : (j : ι) → Ω, f (ωs i) ∂ν =
        ∫ ω, f ω ∂(Measure.map (Function.eval i) ν) :=
    (integral_map (measurable_pi_apply i).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  simpa [ν, hmap.map_eq] using h1

/-- The real-valued measure of a cylinder set in a finite product probability space is the
product of the real-valued measures of its coordinate slices. -/
theorem measureReal_pi_univ
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, FiniteProbabilitySpace (Ω i)]
    (s : ∀ i, Set (Ω i)) :
    volume.real (Set.pi Set.univ s : Set ((i : ι) → Ω i)) =
      ∏ i, volume.real (s i) := by
  rw [Measure.real]
  change (Measure.pi (fun i => (volume : Measure (Ω i))) (Set.pi Set.univ s)).toReal = _
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  simp [Measure.real]

/-- The real-valued measure of a set is the integral of its indicator. -/
theorem measureReal_eq_integral_indicator_one
    {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume.real S = ∫ ω, Set.indicator S (1 : Ω → ℝ) ω := by
  rw [MeasureTheory.integral_indicator_one MeasurableSet.of_discrete]

open Classical in
/-- The real-valued measure of a set is the integral of the corresponding `0/1` function. -/
theorem measureReal_eq_integral_indicator
    {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume.real S = ∫ ω, if ω ∈ S then (1 : ℝ) else 0 := by
  have hfun : Set.indicator S (1 : Ω → ℝ) = fun ω => if ω ∈ S then (1 : ℝ) else 0 := by
    funext ω
    by_cases hω : ω ∈ S <;> simp [hω]
  rw [measureReal_eq_integral_indicator_one, hfun]

/-- The weights of a finite probability space sum to `1`. -/
theorem pmf_toReal_sum_eq_one {Ω : Type*} [FiniteProbabilitySpace Ω] :
    ∑ ω : Ω, (toPMF Ω ω).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun _ _ => (PMF.apply_lt_top _ _).ne)]
  conv_lhs => rw [show ∑ ω : Ω, toPMF Ω ω = ∑' ω : Ω, toPMF Ω ω from
    (tsum_fintype _).symm]
  rw [PMF.tsum_coe]; simp

/-- Each weight in a finite probability space is nonnegative. -/
theorem pmf_toReal_nonneg {Ω : Type*} [FiniteProbabilitySpace Ω] (ω : Ω) :
    0 ≤ (toPMF Ω ω).toReal := ENNReal.toReal_nonneg

/-- Some point in a finite probability space has positive probability mass. -/
theorem exists_pmf_toReal_pos {Ω : Type*} [FiniteProbabilitySpace Ω] :
    ∃ ω : Ω, 0 < (toPMF Ω ω).toReal := by
  by_contra h; push_neg at h
  have : ∑ ω : Ω, (toPMF Ω ω).toReal = 0 :=
    Finset.sum_eq_zero (fun ω _ => le_antisymm (h ω) ENNReal.toReal_nonneg)
  linarith [pmf_toReal_sum_eq_one (Ω := Ω)]

/-- If f(x) ≤ c everywhere under a probability measure, then ∫ f ≤ c. -/
theorem integral_le_of_le {Ω : Type*} [FiniteProbabilitySpace Ω]
    {f : Ω → ℝ} {c : ℝ} (hf : ∀ ω, f ω ≤ c) :
    ∫ ω, f ω ≤ c := by
  rw [integral_eq_pmf_sum]
  calc ∑ ω, (toPMF Ω ω).toReal * f ω
      ≤ ∑ ω, (toPMF Ω ω).toReal * c :=
        Finset.sum_le_sum (fun ω _ =>
          mul_le_mul_of_nonneg_left (hf ω) (pmf_toReal_nonneg (Ω := Ω) ω))
    _ = c := by rw [← Finset.sum_mul, pmf_toReal_sum_eq_one (Ω := Ω), one_mul]

/-- Markov's inequality for nonnegative functions on a finite probability space. -/
theorem measureReal_ge_le_integral_div
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {f : Ω → ℝ} {ε : ℝ} (hf_nonneg : ∀ ω, 0 ≤ f ω) (hε : 0 < ε) :
    volume.real {ω : Ω | ε ≤ f ω} ≤ (∫ ω, f ω) / ε := by
  have hmarkov :
      ε * volume.real {ω : Ω | ε ≤ f ω} ≤ ∫ ω, f ω :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := (volume : Measure Ω)) (f := f)
      (ae_of_all _ hf_nonneg) Integrable.of_finite ε
  rw [le_div_iff₀ hε]
  simpa [Measure.real, mul_comm] using hmarkov

/-- If f(x) > c everywhere under a probability measure on a nonempty type,
then ∫ f > c. -/
theorem lt_integral_of_lt {Ω : Type*} [FiniteProbabilitySpace Ω]
    {f : Ω → ℝ} {c : ℝ} (hf : ∀ ω, c < f ω) :
    c < ∫ ω, f ω := by
  rw [integral_eq_pmf_sum]
  obtain ⟨ω₀, hω₀⟩ := exists_pmf_toReal_pos (Ω := Ω)
  calc c = ∑ ω, (toPMF Ω ω).toReal * c := by
        rw [← Finset.sum_mul, pmf_toReal_sum_eq_one (Ω := Ω), one_mul]
    _ < ∑ ω, (toPMF Ω ω).toReal * f ω :=
        Finset.sum_lt_sum
          (fun ω _ => mul_le_mul_of_nonneg_left (hf ω).le (pmf_toReal_nonneg (Ω := Ω) ω))
          ⟨ω₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hf ω₀) hω₀⟩

end FiniteProbabilitySpace

end CommunicationComplexity
