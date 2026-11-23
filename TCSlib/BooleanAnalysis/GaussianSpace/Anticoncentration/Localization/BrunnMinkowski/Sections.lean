/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.Compact
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ConcaveCompactness
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Constructions.SumProd

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concavity of roots of section volumes

## Main definitions

No new definitions.

## Main results

* `isCompact_section_of_isCompact`: sections of a compact product-space set are compact.
* `concaveOn_rpow_volumeReal_section`: the dimension root of the volume
  of a section of a compact convex set is concave on its projection.

* `volumeReal_section_pos_of_mem_interior_projection`: interior sections
  have positive volume when the compact convex body does.

* `setIntegral_fst_eq_integral_volumeReal_section_mul`: integrate a
  continuous first-coordinate weight using real section volumes.

* `volumeReal_section_le_midpoint_mul_of_projection_subset`: a bounded
  projection controls every section volume by its midpoint volume.

## References

* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, proof of Claim 2, p.380.
* [Gar02] Richard J. Gardner, *The Brunn–Minkowski inequality*,
  Bulletin of the American Mathematical Society 39 (2002), 355–405,
  Corollary 5.3, the root-volume inequality applied to sections.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- Fixing the first coordinate of a compact subset of a product leaves
a compact section when the first factor is a T₁ space.
[LS93, Lemma 2.5, proof of Claim 2, section-compactness prerequisite]

No separation assumption on the second factor is needed.

**Proof sketch.** The fixed-coordinate slice of the product is closed,
because the singleton in the first factor is closed. Its intersection
with the compact set is compact. Projection to the second factor
identifies this compact intersection with the desired section. -/
theorem isCompact_section_of_isCompact
    {X Y : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace Y] {K : Set (X × Y)}
    (hK : IsCompact K) (x : X) :
    IsCompact {y : Y | (x, y) ∈ K} :=
  (by
  apply (isInducing_prodMkRight x).isCompact_preimage ?_ hK
  have hrange : Set.range (Prod.mk x : Y → X × Y) = Prod.fst ⁻¹' {x} := by
    ext ⟨a, b⟩
    simp [eq_comm]
  rw [hrange]
  exact isClosed_singleton.preimage continuous_fst
)

/-- The dimension root of the volume of a section of a compact convex set
is concave on the first-coordinate projection.
[LS93, Lemma 2.5, proof of Claim 2, p.380; Gar02, Corollary 5.3]

The dimension parameter counts the section coordinates. Sections on the
projection are nonempty, but need not have positive volume. No assertion
of concavity outside the projection is made.

**Proof sketch.** The projection is convex. Every section is closed and
contained in the compact second projection, hence compact. At parameters
in the first projection the sections are nonempty. Convexity of the
original set places the weighted Minkowski sum of two sections inside
the section at the weighted parameter. Apply the compact root-volume
Brunn–Minkowski inequality to these three sections. -/
theorem concaveOn_rpow_volumeReal_section
    {n : ℕ} (hn : 1 ≤ n) {K : Set (ℝ × (Fin n → ℝ))}
    (hK : IsCompact K) (hconvex : Convex ℝ K) :
    ConcaveOn ℝ (Set.image Prod.fst K)
      (fun a : ℝ =>
        (volume.real {y : Fin n → ℝ | (a, y) ∈ K}) ^ (1 / (n : ℝ))) :=
  (by
  open scoped Pointwise in
    let S (a : ℝ) := {y : Fin n → ℝ | (a, y) ∈ K}
    have hcompact (a : ℝ) : IsCompact (S a) :=
      isCompact_section_of_isCompact hK a
    have hnonempty (a : ℝ) (ha : a ∈ Set.image Prod.fst K) : (S a).Nonempty := by
      obtain ⟨⟨a, y⟩, hy, rfl⟩ := ha
      exact ⟨y, hy⟩
    refine ⟨hconvex.linear_image (LinearMap.fst ℝ ℝ (Fin n → ℝ)), ?_⟩
    intro a ha b hb r s hr hs hrs
    have hrs' : 1 - s = r := by linarith
    have hs1 : s ≤ 1 := by linarith
    have hcontain : (1 - s) • S a + s • S b ⊆ S ((1 - s) * a + s * b) := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact hconvex hx hy (sub_nonneg.mpr hs1) hs (by ring)
    have h := volumeReal_rpow_le_of_smul_add_subset hn
      (hcompact a) (hcompact b) (hcompact _) (hnonempty a ha) (hnonempty b hb)
      ⟨hs, hs1⟩ hcontain
    simpa only [hrs', smul_eq_mul] using h
)

/-- Every section of a compact convex set over an interior point of its
first-coordinate projection has positive real volume, provided the set
has positive ambient volume.
[LS93, Lemma 2.5, proof of Claim 2, section-normalization prerequisite]

The positive dimension parameter counts the section coordinates.
No separate full-dimensionality or positive-section hypothesis is
assumed.

**Proof sketch.** Product-measure disintegration and positive ambient
volume give at least one section of positive volume. Every section is
compact, so its volume is finite. The nonnegative dimension-root section
profile is concave on the projection, and is positive at that one
parameter. Interior strict positivity for nonnegative concave functions
therefore makes the profile positive at every interior parameter.
Its underlying section volume must consequently be positive. -/
theorem volumeReal_section_pos_of_mem_interior_projection
    {n : ℕ} (hn : 1 ≤ n) {K : Set (ℝ × (Fin n → ℝ))}
    (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hvol : 0 < volume K) {x : ℝ}
    (hx : x ∈ interior (Set.image Prod.fst K)) :
    0 < volume.real {y : Fin n → ℝ | (x, y) ∈ K} :=
  (by
  let S (a : ℝ) := {y : Fin n → ℝ | (a, y) ∈ K}
  have hcompact (a : ℝ) : IsCompact (S a) :=
    isCompact_section_of_isCompact hK a
  obtain ⟨a, ha⟩ : ∃ a : ℝ, volume (S a) ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : volume K = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_apply hK.measurableSet]
      change (∫⁻ a, volume (S a)) = 0
      simp only [h, lintegral_zero]
    exact (ne_of_gt hvol) hzero
  have hreal : 0 < volume.real (S a) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ha (hcompact a).measure_lt_top.ne
  have hnonempty : (S a).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    apply ha
    rw [he]
    exact measure_empty
  have hroot := pos_on_interior_of_nonneg_concaveOn
    (concaveOn_rpow_volumeReal_section hn hK hconvex)
    (fun a _ => Real.rpow_nonneg (measureReal_nonneg) _)
    ⟨a, by obtain ⟨y, hy⟩ := hnonempty; exact ⟨(a, y), hy, rfl⟩,
      Real.rpow_pos_of_pos hreal _⟩ x hx
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  by_contra h
  have heq : volume.real (S x) = 0 :=
    le_antisymm (le_of_not_gt h) measureReal_nonneg
  change 0 < (volume.real (S x)) ^ (1 / (n : ℝ)) at hroot
  rw [heq, Real.zero_rpow (ne_of_gt (one_div_pos.mpr hnpos))] at hroot
  exact (lt_irrefl 0) hroot
)

/-- Integrating a continuous first-coordinate weight over a compact set
equals integrating that weight times the real volume of each section.
[LS93, Lemma 2.5, proof of Claim 2, p.380, weighted section bookkeeping]

Only continuity on the first projection is needed. This is the weighted
Fubini identity underlying section-profile normalization; convexity,
positive volume, and a positive section dimension are unnecessary.

**Proof sketch.** The weight pulled back by the first projection is
integrable on the compact set. Extend it by zero and apply product
Fubini. At each first coordinate its fiber is the indicator of the
corresponding section times a constant. Integrating this constant
indicator gives the section's real volume times the weight. -/
theorem setIntegral_fst_eq_integral_volumeReal_section_mul
    {n : ℕ} {K : Set (ℝ × (Fin n → ℝ))}
    (hK : IsCompact K) {H : ℝ → ℝ}
    (hH : ContinuousOn H (Set.image Prod.fst K)) :
    (∫ p in K, H p.1) =
      ∫ t : ℝ, volume.real {y : Fin n → ℝ | (t, y) ∈ K} * H t :=
  (by
  have hc : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => H p.1) K :=
    hH.comp continuous_fst.continuousOn (fun p hp => ⟨p, hp, rfl⟩)
  have hi : Integrable (K.indicator (fun p : ℝ × (Fin n → ℝ) => H p.1)) :=
    (hc.integrableOn_compact hK).integrable_indicator hK.measurableSet
  rw [← integral_indicator hK.measurableSet]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with t
  have heq : (fun y : Fin n → ℝ => K.indicator (fun p => H p.1) (t, y)) =
      {y : Fin n → ℝ | (t, y) ∈ K}.indicator (fun _ => H t) := by
    funext y
    by_cases hy : (t, y) ∈ K
    · have hy' : y ∈ {y : Fin n → ℝ | (t, y) ∈ K} := hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy']
    · have hy' : y ∉ {y : Fin n → ℝ | (t, y) ∈ K} := hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
  rw [heq, integral_indicator_const (H t)
    (isCompact_section_of_isCompact hK t).measurableSet, smul_eq_mul]
)

/-- Every section of a compact convex body with first projection
containing the unit interval and contained in `[-R,R]` has real volume
at most `(2 + 2 * R)^n` times its midpoint section volume.
[LS93, Lemma 2.5, proof of Claim 2, uniform section-profile bound]

The dimension parameter counts the section coordinates. The estimate
is homogeneous and requires no positive-volume assumption. It also
holds outside the first projection, where the section is empty.
The explicit constant records a coarse bound used in normalized
section-profile domination.

**Proof sketch.** On the first projection, the nonnegative dimension
root of section volume is concave. Apply its homogeneous growth bound
with center one half and anchors zero and one. For a parameter in
`[-R,R]`, the resulting factor `1 + 2 * |t - 1/2|` is at most
`2 + 2 * R`. Raise the root inequality to the positive integer
dimension and recover section volumes. Outside the first projection
the section is empty, so the bound follows from nonnegativity. -/
theorem volumeReal_section_le_midpoint_mul_of_projection_subset
    {n : ℕ} (hn : 1 ≤ n) {K : Set (ℝ × (Fin n → ℝ))}
    (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.image Prod.fst K)
    {R : ℝ} (hR : 1 ≤ R)
    (hprojection : Set.image Prod.fst K ⊆ Set.Icc (-R) R)
    (t : ℝ) :
    volume.real {y : Fin n → ℝ | (t, y) ∈ K} ≤
      (2 + 2 * R) ^ n *
        volume.real {y : Fin n → ℝ | ((1 / 2 : ℝ), y) ∈ K} :=
  (by
  let w (s : ℝ) := volume.real {y : Fin n → ℝ | (s, y) ∈ K}
  have hw (s : ℝ) : 0 ≤ w s := measureReal_nonneg
  by_cases ht : t ∈ Set.image Prod.fst K
  · have hg := le_one_add_abs_div_mul_of_nonneg_concaveOn
      (concaveOn_rpow_volumeReal_section hn hK hconvex)
      (fun s _ => Real.rpow_nonneg (hw s) _) (by norm_num : (0 : ℝ) < 1 / 2)
      (hunit (by norm_num : (1 / 2 : ℝ) - 1 / 2 ∈ Set.Icc (0 : ℝ) 1))
      (hunit (by norm_num : (1 / 2 : ℝ) + 1 / 2 ∈ Set.Icc (0 : ℝ) 1)) ht
    have habs : |t - (1 / 2 : ℝ)| ≤ R + 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [(hprojection ht).1, (hprojection ht).2]
    have hfactor : 1 + |t - (1 / 2 : ℝ)| / (1 / 2) ≤ 2 + 2 * R := by
      linarith
    have hbound : (w t) ^ (1 / (n : ℝ)) ≤
        (2 + 2 * R) * (w (1 / 2)) ^ (1 / (n : ℝ)) :=
      hg.trans (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (hw _) _))
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (hw t) _) hbound n
    have hn0 : n ≠ 0 := by omega
    rw [mul_pow, one_div, Real.rpow_inv_natCast_pow (hw t) hn0,
      Real.rpow_inv_natCast_pow (hw (1 / 2)) hn0] at hp
    exact hp
  · have hempty : {y : Fin n → ℝ | (t, y) ∈ K} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact ht ⟨(t, y), hy, rfl⟩
    rw [hempty, measureReal_empty]
    exact mul_nonneg (pow_nonneg (by linarith) _) (hw _)
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
