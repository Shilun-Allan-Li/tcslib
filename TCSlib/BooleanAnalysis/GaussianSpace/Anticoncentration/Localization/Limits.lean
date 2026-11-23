/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Constructions.SumProd

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Integral signs on limits of shrinking sets

## Main definitions

No new definitions.

## Main results

* `nonneg_of_pos_integral_of_iInter_eq_singleton`: positive integrals over
  nested compact closed sets force nonnegativity at a singleton limit.

* `tendsto_volumeReal_projection_diff_unitInterval`: projection lengths
  outside the limiting unit interval tend to zero.

* `eventually_abs_sub_lt_on_antitone_compacts`: tests agreeing on the
  limiting set are uniformly close on all sufficiently late stages.

## References

* [LS93] L. Lovász and M. Simonovits, *Random Walks in a Convex Body and an
  Improved Volume Algorithm*, Random Structures & Algorithms 4(4) (1993),
  359–412, Lemma 2.5, proofs of Claims 1 and 2, pp. 380–381.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- If a decreasing sequence of closed sets with compact initial set
has singleton intersection, a real-valued function continuous at that
point and having positive integral on every stage is nonnegative there.

This isolates the point-limit case of [LS93, Lemma 2.5, proof of Claim 1,
p.380], allowing an arbitrary measure and requiring continuity only at the
limiting point. No integrability assumption is needed, and the conclusion
is nonnegativity rather than strict positivity.

**Proof sketch.** If the value at the limiting point were negative,
continuity would give a neighborhood where the function is negative.
Compact nested-set neighborhood containment puts some whole stage inside
that neighborhood. Its integral is then nonpositive, contradicting the
assumed positivity of every stage integral. -/
theorem nonneg_of_pos_integral_of_iInter_eq_singleton
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    (μ : Measure E) (K : ℕ → Set E) (hanti : Antitone K)
    (hclosed : ∀ m : ℕ, IsClosed (K m)) (hcompact : IsCompact (K 0))
    (a : E) (hinter : (⋂ m : ℕ, K m) = {a})
    (f : E → ℝ) (hf : ContinuousAt f a)
    (hpos : ∀ m : ℕ, 0 < ∫ x in K m, f x ∂μ) :
    0 ≤ f a :=
  (by
  by_contra hneg
  have hfa : f a < 0 := lt_of_not_ge hneg
  have hn : {x | f x < 0} ∈ nhds a := hf (Iio_mem_nhds hfa)
  have hcp (m : ℕ) : IsCompact (K m) :=
    hcompact.of_isClosed_subset (hclosed m) (hanti (Nat.zero_le m))
  obtain ⟨m, hm⟩ := exists_subset_nhds_of_isCompact' hanti.directed_ge hcp hclosed (by
    intro x hx
    have hxa : x = a := by simpa only [hinter, Set.mem_singleton_iff] using hx
    simpa only [hxa] using hn)
  have hnonpos : ∫ x in K m, f x ∂μ ≤ 0 :=
    setIntegral_nonpos (hclosed m).measurableSet (fun x hx => (hm hx).le)
  exact (not_lt_of_ge hnonpos) (hpos m)
)

/-- The lengths of the portions of nested compact first-coordinate
projections outside the unit interval tend to zero when every limiting
point projects into that interval.
[LS93, Lemma 2.5, proof of Claim 2, pp.380–381, vanishing caps]

Only closedness, nesting and a compact initial set are required; the
sets need not be convex or have positive volume.

**Proof sketch.** For every positive radius, the intersection lies in
the open strip whose first coordinate is between minus that radius and
one plus that radius. Compact nested-set neighborhood containment puts
every sufficiently late set inside the strip. The part of its
projection outside the unit interval is then contained in two intervals
whose total length is twice the radius. This bounds the cap lengths by
a quantity tending to zero. -/
theorem tendsto_volumeReal_projection_diff_unitInterval
    {Y : Type*} [TopologicalSpace Y]
    (K : ℕ → Set (ℝ × Y)) (hanti : Antitone K)
    (hclosed : ∀ m : ℕ, IsClosed (K m))
    (hcompact : IsCompact (K 0))
    (hlim : ∀ p ∈ (⋂ m : ℕ, K m), p.1 ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun m : ℕ =>
        volume.real ((Set.image Prod.fst (K m)) \ Set.Icc (0 : ℝ) 1))
      Filter.atTop (nhds (0 : ℝ)) :=
  (by
  have hcp (m : ℕ) : IsCompact (K m) :=
    hcompact.of_isClosed_subset (hclosed m) (hanti (Nat.zero_le m))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall (fun m => lt_of_lt_of_le ha measureReal_nonneg)
  · intro ε hε
    let δ := ε / 4
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨m, hm⟩ := exists_subset_nhds_of_isCompact' hanti.directed_ge hcp hclosed (by
      intro p hp
      exact (isOpen_Ioo.preimage continuous_fst).mem_nhds
        (show p.1 ∈ Ioo (-δ) (1 + δ) from
          ⟨by linarith [(hlim p hp).1], by linarith [(hlim p hp).2]⟩))
    filter_upwards [Filter.eventually_ge_atTop m] with k hk
    have hsub : (Set.image Prod.fst (K k)) \ Icc (0 : ℝ) 1 ⊆
        Ioo (-δ) 0 ∪ Ioo 1 (1 + δ) := by
      rintro a ⟨⟨p, hp, rfl⟩, ha⟩
      have hstrip := hm (hanti hk hp)
      change -δ < p.1 ∧ p.1 < 1 + δ at hstrip
      by_cases h0 : p.1 < 0
      · exact Or.inl ⟨hstrip.1, h0⟩
      · exact Or.inr ⟨by by_contra h; exact ha ⟨le_of_not_gt h0, le_of_not_gt h⟩,
          hstrip.2⟩
    calc
      volume.real ((Set.image Prod.fst (K k)) \ Icc (0 : ℝ) 1) ≤
          volume.real (Ioo (-δ) 0 ∪ Ioo 1 (1 + δ)) := measureReal_mono hsub (by
            apply ne_top_of_le_ne_top _ (measure_union_le _ _)
            rw [Real.volume_Ioo, Real.volume_Ioo, ENNReal.add_ne_top]
            exact ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
      _ ≤ volume.real (Ioo (-δ) 0) + volume.real (Ioo 1 (1 + δ)) :=
        measureReal_union_le _ _
      _ < ε := by
        rw [Real.volume_real_Ioo_of_le (by linarith : -δ ≤ 0),
          Real.volume_real_Ioo_of_le (by linarith : 1 ≤ 1 + δ)]
        dsimp [δ]
        linarith
)
/-- Two continuous real tests that agree on the intersection of nested
closed sets with compact initial set become uniformly close on the
successive sets.
[LS93, Lemma 2.5, proof of Claim 2, pp.380–381, ambient-test approximation]

No nonemptiness, convexity or measure assumption is required.

**Proof sketch.** For each positive tolerance, the set where the
absolute difference of the tests is smaller than that tolerance is an
open neighborhood of the whole intersection. Compact nested-set
neighborhood containment puts one stage inside this neighborhood.
Nesting gives the same bound at every later stage. -/
theorem eventually_abs_sub_lt_on_antitone_compacts
    {E : Type*} [TopologicalSpace E]
    (K : ℕ → Set E) (hanti : Antitone K)
    (hclosed : ∀ m : ℕ, IsClosed (K m))
    (hcompact : IsCompact (K 0))
    (F G : E → ℝ) (hF : Continuous F) (hG : Continuous G)
    (heq : Set.EqOn F G (⋂ m : ℕ, K m)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        ∀ x ∈ K m, |F x - G x| < ε :=
  (by
  intro ε hε
  have hcp (m : ℕ) : IsCompact (K m) :=
    hcompact.of_isClosed_subset (hclosed m) (hanti (Nat.zero_le m))
  have hopen : IsOpen {x | |F x - G x| < ε} :=
    isOpen_lt (hF.sub hG).abs continuous_const
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact' hanti.directed_ge hcp hclosed (by
    intro x hx
    apply hopen.mem_nhds
    change |F x - G x| < ε
    simpa only [heq hx, sub_self, abs_zero] using hε)
  exact ⟨N, fun m hm x hx => hN (hanti hm hx)⟩
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
