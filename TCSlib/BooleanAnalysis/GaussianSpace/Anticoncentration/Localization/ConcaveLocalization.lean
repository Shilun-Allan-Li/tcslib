/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.CoordinateCuts
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.SegmentDensity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Point-or-segment concave localization

## Main definitions

No new definitions.

## Main results

* `exists_point_or_concave_profile_on_segment`: two continuous signed
  tests with positive integrals on a compact convex set are simultaneously
  nonnegative at a point, or have nonnegative weighted integrals along
  a nondegenerate segment against a nonzero concave-profile power.

## References

* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, proofs of Claims 1 and 2, pp.379–381.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- Two continuous real tests with positive integrals on a compact convex
set in real coordinate space admit either a common point where both
are nonnegative, or a nondegenerate segment on which both have
nonnegative integrals against the transverse-dimension power of a
nonzero concave profile.
[LS93, Lemma 2.5, proofs of Claims 1 and 2, pp.379–381]

The point or both segment endpoints belong to the original set.
The ambient dimension is one more than the positive transverse
dimension. The profile is concave on the open unit interval, has
midpoint value one, and has values between zero and two there.
The conclusion gives nonnegative, rather than strictly positive,
limits. It is the concave-profile stage of localization, before
the further reduction to an affine profile.

**Proof sketch.** Shrink the original set through nested compact convex
sets while keeping both signed integrals positive. Their nonempty
collinear intersection is compact and convex, hence a closed segment.
Its endpoints belong to every stage and therefore to the original set.
If the endpoints agree, the singleton-limit theorem makes both tests
nonnegative there. Otherwise apply the nondegenerate-segment density
result to the same nested bodies and tests. Its midpoint-normalized
concave profile gives the second alternative. -/
theorem exists_point_or_concave_profile_on_segment
    {n : ℕ} (hn : 1 ≤ n)
    (K₀ : Set (Fin (n + 1) → ℝ))
    (hK₀compact : IsCompact K₀) (hK₀convex : Convex ℝ K₀)
    (F G : (Fin (n + 1) → ℝ) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hFpos : 0 < ∫ x in K₀, F x)
    (hGpos : 0 < ∫ x in K₀, G x) :
    (∃ x ∈ K₀, 0 ≤ F x ∧ 0 ≤ G x) ∨
      ∃ a b : Fin (n + 1) → ℝ,
        a ∈ K₀ ∧ b ∈ K₀ ∧ a ≠ b ∧
        ∃ φ : ℝ → ℝ,
          ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) φ ∧
          φ (1 / 2 : ℝ) = 1 ∧
          (∀ t ∈ Set.Ioo (0 : ℝ) 1, φ t ∈ Set.Icc (0 : ℝ) 2) ∧
          0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1,
            (φ t) ^ n * F (AffineMap.lineMap a b t) ∧
          0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1,
            (φ t) ^ n * G (AffineMap.lineMap a b t) :=
  (by
  obtain ⟨K, hK0, hanti, hstage, hne, hcol⟩ :=
    exists_antitone_compact_convex_collinear_iInter_integral_pos_pi
      F G K₀ hK₀compact hK₀convex hFpos hGpos
  have hclosed (m : ℕ) : IsClosed (K m) := (hstage m).1.isClosed
  have hsubset : (⋂ m, K m) ⊆ K₀ := by
    rw [← hK0]
    exact Set.iInter_subset K 0
  have hcompact : IsCompact (⋂ m, K m) :=
    hK₀compact.of_isClosed_subset (isClosed_iInter hclosed) hsubset
  have hconvex : Convex ℝ (⋂ m, K m) := convex_iInter (fun m => (hstage m).2.1)
  obtain ⟨a, b, hab⟩ :=
    exists_eq_segment_of_nonempty_isCompact_convex_collinear hne hcompact hconvex hcol
  have ha : a ∈ K₀ := hsubset (hab.symm ▸ left_mem_segment ℝ a b)
  have hb : b ∈ K₀ := hsubset (hab.symm ▸ right_mem_segment ℝ a b)
  by_cases heq : a = b
  · left
    have hsingle : (⋂ m, K m) = {a} := by rw [hab, ← heq, segment_same]
    refine ⟨a, ha, ?_, ?_⟩
    · exact nonneg_of_pos_integral_of_iInter_eq_singleton volume K hanti hclosed
        (hstage 0).1 a hsingle F hF.continuousAt (fun m => (hstage m).2.2.1)
    · exact nonneg_of_pos_integral_of_iInter_eq_singleton volume K hanti hclosed
        (hstage 0).1 a hsingle G hG.continuousAt (fun m => (hstage m).2.2.2)
  · right
    refine ⟨a, b, ha, hb, heq, ?_⟩
    exact exists_concave_profile_of_iInter_eq_segment hn K (fun m => (hstage m).1)
      (fun m => (hstage m).2.1) hanti a b heq hab F G hF hG
      (fun m => (hstage m).2.2.1) (fun m => (hstage m).2.2.2)
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
