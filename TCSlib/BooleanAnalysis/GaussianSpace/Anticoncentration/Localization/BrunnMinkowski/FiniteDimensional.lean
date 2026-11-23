/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.PrekopaLeindler
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.Marginal
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-dimensional Prékopa–Leindler inequality

## Main definitions

No new definitions.

## Main results

* `prekopaLeindler_integral_le_of_bddAbove_hasCompactSupport`: the
  finite-dimensional inequality for bounded compactly supported Borel
  inputs.

## References

* [Gar02] Richard J. Gardner, *The Brunn–Minkowski inequality*,
  Bulletin of the American Mathematical Society 39 (2002), 355–405,
  Theorem 4.2. The author's October 25, 2001 manuscript, pp.8–9,
  gives the induction by fiber integration:
  https://faculty.gardner.wwu.edu/gorizia12.pdf.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- The finite-dimensional Prékopa–Leindler inequality for nonnegative
bounded compactly supported Borel functions.
[Gar02, Theorem 4.2, bounded compact-support specialization]

The explicit integrability hypotheses simplify the product-integral
interface. They follow from the other hypotheses for these inputs.
The dimension may be zero.

**Proof sketch.** Induct on the dimension. In dimension zero the space
is a singleton of volume one, and the result is the pointwise hypothesis.
For the successor step split off one real coordinate using the
existing continuous linear finite-product equivalence, identified with
the measure-preserving coordinate split. For each pair of first
coordinates, apply the induction hypothesis to the three remaining
coordinate fibers. This gives the pointwise Prékopa–Leindler hypothesis
for the three marginal integrals. The fibers are bounded, measurable,
compactly supported and integrable at every parameter. The marginals are
measurable, bounded and integrable, so the one-dimensional inequality
applies. Fubini and the measure-preserving coordinate split identify
their integrals with the original integrals. -/
theorem prekopaLeindler_integral_le_of_bddAbove_hasCompactSupport
    {n : ℕ} {f g h : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfint : Integrable f) (hgint : Integrable g) (hhint : Integrable h)
    (hfnonneg : ∀ x, 0 ≤ f x)
    (hgnonneg : ∀ x, 0 ≤ g x)
    (hhnonneg : ∀ x, 0 ≤ h x)
    (hfbdd : BddAbove (Set.range f))
    (hgbdd : BddAbove (Set.range g))
    (hhbdd : BddAbove (Set.range h))
    (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hfg : ∀ x y : Fin n → ℝ,
      (f x) ^ (1 - t) * (g y) ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫ x, f x) ^ (1 - t) * (∫ x, g x) ^ t ≤ ∫ x, h x :=
  (by
  induction n with
  | zero =>
    have he : (1 - t) • (default : Fin 0 → ℝ) + t • default = default := Subsingleton.elim _ _
    rw [Measure.volume_pi_eq_dirac (default : Fin 0 → ℝ)]
    simpa only [integral_dirac, he] using hfg default default
  | succ n ih =>
    let T := Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have heq : (T : (ℝ × (Fin n → ℝ)) → (Fin (n + 1) → ℝ)) = e.symm := by
      change (Fin.consEquiv (fun _ : Fin (n + 1) => ℝ) : _ → _) = _
      rw [← Fin.insertNthEquiv_zero]
      rfl
    have hT : MeasurePreserving T volume volume := by
      rw [heq]
      exact MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ 0)
    have hTemb : MeasurableEmbedding T := by
      rw [heq]
      exact e.symm.measurableEmbedding
    have prep {k : (Fin (n + 1) → ℝ) → ℝ}
        (hkm : Measurable k) (hki : Integrable k) (hkn : ∀ x, 0 ≤ k x)
        (hkb : BddAbove (Set.range k)) (hkc : HasCompactSupport k) :
        (∀ a : ℝ, Measurable (fun y => k (T (a, y))) ∧
          Integrable (fun y => k (T (a, y))) ∧
          BddAbove (Set.range (fun y => k (T (a, y)))) ∧
          HasCompactSupport (fun y => k (T (a, y)))) ∧
        (Measurable (fun a => ∫ y, k (T (a, y))) ∧
          Integrable (fun a => ∫ y, k (T (a, y))) ∧
          BddAbove (Set.range (fun a => ∫ y, k (T (a, y))))) ∧
        (∫ a : ℝ, ∫ y, k (T (a, y))) = ∫ x, k x := by
      have hm := hkm.comp T.continuous.measurable
      have hi := hT.integrable_comp_of_integrable hki
      have hc := hkc.comp_homeomorph T.toHomeomorph
      obtain ⟨M, hM⟩ := hkb
      have hb : ∃ M : ℝ, ∀ p : ℝ × (Fin n → ℝ), |k (T p)| ≤ M :=
        ⟨M, fun p => by rw [abs_of_nonneg (hkn _)]; exact hM ⟨_, rfl⟩⟩
      have hfi := integrable_fiber_of_measurable_bounded_hasCompactSupport volume hm hc hb
      obtain ⟨N, hN⟩ := bounded_integral_fiber_of_bounded_hasCompactSupport volume hc hb
      refine ⟨?_, ⟨hm.stronglyMeasurable.integral_prod_right'.measurable,
        hi.integral_prod_left, ⟨N, ?_⟩⟩, ?_⟩
      · intro a
        refine ⟨hm.comp measurable_prodMk_left, hfi a, ⟨M, ?_⟩, ?_⟩
        · rintro _ ⟨y, rfl⟩
          exact hM ⟨_, rfl⟩
        · apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
          intro y hy
          exact ⟨(a, y), subset_tsupport (k ∘ T) hy, rfl⟩
      · rintro _ ⟨a, rfl⟩
        exact (le_abs_self _).trans (hN a)
      · exact (integral_prod (k ∘ T) hi).symm.trans (hT.integral_comp hTemb k)
    obtain ⟨hfib, hfmarg, hfeq⟩ := prep hf hfint hfnonneg hfbdd hfc
    obtain ⟨hgib, hgmarg, hgeq⟩ := prep hg hgint hgnonneg hgbdd hgc
    obtain ⟨hhib, hhmarg, hheq⟩ := prep hh hhint hhnonneg hhbdd hhc
    have hpoint (a b : ℝ) :
        (∫ y, f (T (a, y))) ^ (1 - t) * (∫ y, g (T (b, y))) ^ t ≤
          ∫ y, h (T ((1 - t) * a + t * b, y)) := by
      apply ih (hfib a).1 (hgib b).1 (hhib _).1
        (hfib a).2.1 (hgib b).2.1 (hhib _).2.1
        (fun y => hfnonneg _) (fun y => hgnonneg _) (fun y => hhnonneg _)
        (hfib a).2.2.1 (hgib b).2.2.1 (hhib _).2.2.1
        (hfib a).2.2.2 (hgib b).2.2.2 (hhib _).2.2.2
      intro x y
      convert hfg (T (a, x)) (T (b, y)) using 1
      congr 1
      rw [← map_smul, ← map_smul, ← map_add]
      rfl
    have hfinal := prekopaLeindler_integral_le_of_bddAbove
      hfmarg.1 hgmarg.1 hhmarg.1 hfmarg.2.1 hgmarg.2.1 hhmarg.2.1
      (fun a => integral_nonneg (fun y => hfnonneg _))
      (fun a => integral_nonneg (fun y => hgnonneg _))
      (fun a => integral_nonneg (fun y => hhnonneg _))
      hfmarg.2.2 hgmarg.2.2 ht hpoint
    rwa [hfeq, hgeq, hheq] at hfinal
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
