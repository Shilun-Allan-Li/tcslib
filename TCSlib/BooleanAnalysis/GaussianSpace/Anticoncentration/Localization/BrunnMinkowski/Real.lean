/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Order.Compact

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-dimensional Brunn–Minkowski foundation

## Main definitions

No new definitions.

## Main results

* `volume_add_le_volume_add_of_isCompact`: the sum of the lengths of two
  nonempty compact real sets is at most the length of their Minkowski sum.
* `volume_add_le_of_add_subset`: the measurable-set version, allowing an
  arbitrary containing set.
* `ofReal_mul_volume_add_le_of_smul_add_subset`: the weighted version, including
  zero coefficients.

## References

* [Gar02] Richard J. Gardner, *The Brunn–Minkowski inequality*,
  Bulletin of the American Mathematical Society 39 (2002), 355–405,
  Theorem 2.1, compact-set case. The author's October 25, 2001 manuscript
  gives this argument on p.3: https://faculty.gardner.wwu.edu/gorizia12.pdf.
-/

open MeasureTheory
open scoped Pointwise

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- The lengths of two nonempty compact subsets of the real line add to
at most the length of their Minkowski sum.
[Gar02, Theorem 2.1, compact-set case]

This is the unweighted version; the convex-combination version follows
by applying it to positive scalar multiples and using dilation of volume.
Neither set is assumed convex or to have positive measure.

**Proof sketch.** Choose the maximum `a` of the first set and the minimum
`b` of the second. The translates `A + b` and `a + B` lie in `A + B`.
Their intersection is contained in the singleton `{a + b}`, which has
Lebesgue measure zero. Translation invariance and additivity for their
union, followed by monotonicity, give the inequality. -/
theorem volume_add_le_volume_add_of_isCompact
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) :=
  (by
  obtain ⟨a, ha, hmax⟩ := hA.exists_isMaxOn hAne
    (show ContinuousOn (fun x : ℝ => x) A from continuous_id.continuousOn)
  obtain ⟨b, hb, hmin⟩ := hB.exists_isMinOn hBne
    (show ContinuousOn (fun x : ℝ => x) B from continuous_id.continuousOn)
  let X := (fun x : ℝ => x + -b) ⁻¹' A
  let Y := (fun x : ℝ => x + -a) ⁻¹' B
  have hY : MeasurableSet Y :=
    (hB.isClosed.preimage (continuous_id.add continuous_const)).measurableSet
  have hvX : volume X = volume A := measure_preimage_add_right volume (-b) A
  have hvY : volume Y = volume B := measure_preimage_add_right volume (-a) B
  have hnull : volume (X ∩ Y) = 0 := by
    apply measure_mono_null (t := {a + b}) ?_ (measure_singleton (a + b))
    intro x hx
    have hxA : x + -b ≤ a := hmax hx.1
    have hxB : b ≤ x + -a := hmin hx.2
    exact Set.mem_singleton_iff.mpr (by linarith)
  have hsub : X ∪ Y ⊆ A + B := by
    intro x hx
    rcases hx with hx | hx
    · exact Set.mem_add.mpr ⟨x + -b, hx, b, hb, by ring⟩
    · exact Set.mem_add.mpr ⟨a, ha, x + -a, hx, by ring⟩
  calc
    volume A + volume B = volume X + volume Y := by rw [hvX, hvY]
    _ = volume (X ∪ Y) := by
      have h := measure_union_add_inter X hY (μ := volume)
      rw [hnull, add_zero] at h
      exact h.symm
    _ ≤ volume (A + B) := measure_mono hsub
)

/-- The volumes of two nonempty measurable real sets add to at most the
volume of any set containing their Minkowski sum.
[Gar02, Theorem 2.1]

This extends the compact-set inequality by inner regularity. The sets may
be unbounded or have infinite volume, and the containing set need not be
measurable.

**Proof sketch.** Express the volume of each measurable set as the
supremum of the volumes of its compact subsets. Enlarge each compact
subset by a fixed point of its respective set so that the compact
sum-set estimate applies even to empty approximants. Their sum is
contained in the given containing set. Take both suprema, using
preservation of nonempty suprema by addition in the extended
nonnegative reals. -/
theorem volume_add_le_of_add_subset
    {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hsub : A + B ⊆ C) :
    volume A + volume B ≤ volume C :=
  (by
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  rw [hA.measure_eq_iSup_isCompact volume, hB.measure_eq_iSup_isCompact volume]
  simp only [iSup_and']
  apply ENNReal.biSup_add_biSup_le'
    (show ∃ K : Set ℝ, K ⊆ A ∧ IsCompact K from ⟨∅, Set.empty_subset A, isCompact_empty⟩)
    (show ∃ L : Set ℝ, L ⊆ B ∧ IsCompact L from ⟨∅, Set.empty_subset B, isCompact_empty⟩)
  intro K ⟨hKA, hK⟩ L ⟨hLB, hL⟩
  calc
    volume K + volume L ≤ volume (insert a K) + volume (insert b L) :=
      add_le_add (measure_mono (Set.subset_insert a K)) (measure_mono (Set.subset_insert b L))
    _ ≤ volume (insert a K + insert b L) :=
      volume_add_le_volume_add_of_isCompact (hK.insert a) (hL.insert b)
        (Set.insert_nonempty a K) (Set.insert_nonempty b L)
    _ ≤ volume C := measure_mono ((Set.add_subset_add
      (Set.insert_subset ha hKA) (Set.insert_subset hb hLB)).trans hsub)
)

/-- The nonnegative weighted sum of the volumes of two nonempty measurable
real sets is at most the volume of any set containing their corresponding
weighted Minkowski sum.
[Gar02, Theorem 2.1, by dilation]

Zero coefficients and infinite volumes are allowed, with multiplication
interpreted in the extended nonnegative reals. Nonemptiness ensures that
a zero dilation is the singleton at zero rather than the empty set.

**Proof sketch.** Apply the measurable containing-set sum inequality to
the two dilated sets. Scalar dilation preserves measurability, including
at zero, and the volume of a nonnegative real dilation is its coefficient
times the original volume. Substitute these two volume identities. -/
theorem ofReal_mul_volume_add_le_of_smul_add_subset
    {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsub : r • A + s • B ⊆ C) :
    ENNReal.ofReal r * volume A + ENNReal.ofReal s * volume B ≤ volume C :=
  (by
  have h := volume_add_le_of_add_subset (hA.const_smul₀ r) (hB.const_smul₀ s)
    (hAne.image (fun x => r • x)) (hBne.image (fun x => s • x)) hsub
  rw [Measure.addHaar_smul_of_nonneg volume hr A,
    Measure.addHaar_smul_of_nonneg volume hs B] at h
  simpa using h
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
