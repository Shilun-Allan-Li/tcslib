/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Bases
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.Compact

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Subsequence compactness of bounded concave profiles

## Main definitions

No new definitions.

## Main results

* `exists_subseq_tendsto_of_concaveOn_of_uniform_bounds`: a uniformly
  bounded nonnegative concave sequence on the open unit interval has a
  pointwise convergent subsequence with a bounded concave limit.
* `le_two_mul_midpoint_of_nonneg_concaveOn_Icc`: twice the midpoint value
  bounds a nonnegative concave function on a closed interval.
* `exists_subseq_tendsto_of_concaveOn_of_midpoint_eq_one`: midpoint-normalized
  profiles have a nonzero normalized concave subsequential limit.
* `tendsto_integral_pow_mul_of_concaveOn_of_uniform_bounds`: powers of profiles
  converge against signed continuous tests.
* `pos_on_interior_of_nonneg_concaveOn`: one positive value gives positivity
  throughout the interior of a nonnegative concave profile’s domain.
* `le_one_add_abs_div_mul_of_nonneg_concaveOn`: two fixed anchors control
  profile growth relative to the center value.

## References

* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, proof of Claim 2, pp.380–381.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- A uniformly bounded sequence of nonnegative concave functions on the
open unit interval has a subsequence converging pointwise there to a
nonnegative concave function.
[LS93, Lemma 2.5, proof of Claim 2, p.380, compactness step]

All bounds and concavity conclusions concern the open interval. No
endpoint convergence or concavity of an extension outside the interval
is asserted.

**Proof sketch.** Replace each input by its extension by zero outside the
open interval. The family of all such bounded concave functions is a
closed subset of a compact product of closed bounded real intervals,
hence compact in the pointwise topology. Restriction to the rational
points of the open interval is continuous and injective: concave
functions are continuous on the open interval, so equality on its dense
rational subset implies equality throughout. This restriction embeds
the compact family into a countable product of real lines. It therefore
makes the family first countable. Extract a convergent subsequence in
that compact first-countable family and read its convergence pointwise. -/
theorem exists_subseq_tendsto_of_concaveOn_of_uniform_bounds
    (f : ℕ → ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hconcave : ∀ m : ℕ, ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (f m))
    (hbound : ∀ m : ℕ, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      f m x ∈ Set.Icc (0 : ℝ) M) :
    ∃ (φ : ℝ → ℝ) (u : ℕ → ℕ),
      StrictMono u ∧
      ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) φ ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, φ x ∈ Set.Icc (0 : ℝ) M) ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        Filter.Tendsto (fun m : ℕ => f (u m) x) Filter.atTop (nhds (φ x)) :=
  (by
  classical
  let I := Set.Ioo (0 : ℝ) 1
  let S : Set (ℝ → ℝ) := {g | (∀ x, x ∉ I → g x = 0) ∧
    (∀ x, g x ∈ Set.Icc (0 : ℝ) M) ∧ ConcaveOn ℝ I g}
  have hc : IsClosed {g : ℝ → ℝ | ConcaveOn ℝ I g} := by
    change IsClosed {g : ℝ → ℝ | Convex ℝ I ∧ ∀ x ∈ I, ∀ y ∈ I,
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        a • g x + b • g y ≤ g (a • x + b • y)}
    simp only [show Convex ℝ I from convex_Ioo _ _, true_and, Set.setOf_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun hx => isClosed_iInter fun y =>
      isClosed_iInter fun hy => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_iInter fun ha => isClosed_iInter fun hb => isClosed_iInter fun hab => ?_
    exact isClosed_le (((continuous_apply x).const_smul a).add
      ((continuous_apply y).const_smul b)) (continuous_apply (a • x + b • y))
  have hclosed : IsClosed S := by
    change IsClosed ({g : ℝ → ℝ | ∀ x, x ∉ I → g x = 0} ∩
      ({g : ℝ → ℝ | ∀ x, g x ∈ Set.Icc (0 : ℝ) M} ∩ {g | ConcaveOn ℝ I g}))
    refine IsClosed.inter ?_ (IsClosed.inter ?_ hc)
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply x) continuous_const
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_apply x)
  have hcompact : IsCompact S :=
    (isCompact_pi_infinite fun _ : ℝ => isCompact_Icc (a := (0 : ℝ)) (b := M)).of_isClosed_subset
      hclosed (fun g hg => hg.2.1)
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  let QI := {q : ℚ // (q : ℝ) ∈ I}
  let R (g : S) (q : QI) : ℝ := g.val (q.val : ℝ)
  have hR : Continuous R :=
    continuous_pi fun q => (continuous_apply (q.val : ℝ)).comp continuous_subtype_val
  have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  have hdense : I ⊆ closure (Set.range ((↑) : ℚ → ℝ) ∩ I) := by
    intro x hx
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hd.exists_mem_open (hU.inter isOpen_Ioo) ⟨x, hxU, hx⟩
    exact ⟨(q : ℝ), hq.1, ⟨⟨q, rfl⟩, hq.2⟩⟩
  have hinj : Function.Injective R := by
    intro g h hgh
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ I
    · have heq : Set.EqOn g.val h.val (Set.range ((↑) : ℚ → ℝ) ∩ I) := by
        rintro y ⟨⟨q, rfl⟩, hq⟩
        exact congrFun hgh (⟨q, hq⟩ : QI)
      exact heq.of_subset_closure
        (ConcaveOn.continuousOn isOpen_Ioo g.property.2.2)
        (ConcaveOn.continuousOn isOpen_Ioo h.property.2.2)
        Set.inter_subset_right hdense hx
    · rw [g.property.1 x hx, h.property.1 x hx]
  letI : FirstCountableTopology S := (hR.isClosedEmbedding hinj).isEmbedding.firstCountableTopology
  have hseq (m : ℕ) : I.indicator (f m) ∈ S := by
    refine ⟨?_, ?_, (hconcave m).congr ?_⟩
    · intro x hx
      exact Set.indicator_of_notMem hx _
    · intro x
      by_cases hx : x ∈ I
      · simpa only [Set.indicator_of_mem hx] using hbound m x hx
      · simpa only [Set.indicator_of_notMem hx, Set.mem_Icc, le_refl, true_and] using hM
    · intro x hx
      exact (Set.indicator_of_mem hx _).symm
  let seq (m : ℕ) : S := ⟨I.indicator (f m), hseq m⟩
  obtain ⟨φ, u, hu, hlim⟩ := CompactSpace.tendsto_subseq seq
  refine ⟨φ.val, u, hu, φ.property.2.2, fun x hx => φ.property.2.1 x, ?_⟩
  intro x hx
  have hev := (((continuous_apply x).comp continuous_subtype_val).tendsto φ).comp hlim
  change Filter.Tendsto (fun m => I.indicator (f (u m)) x) Filter.atTop (nhds (φ.val x)) at hev
  have hxI : x ∈ I := hx
  simpa only [Set.indicator_of_mem hxI] using hev
)

/-- A nonnegative concave function on a closed real interval is bounded
above there by twice its value at the midpoint.
[LS93, Lemma 2.5, proof of Claim 2, normalization prerequisite]

No continuity or strict positivity assumption is needed. In particular,
on the unit interval, midpoint normalization to one gives the uniform
upper bound two.

**Proof sketch.** Reflect the chosen point `x` across the midpoint to
`a + b - x`, which also lies in the interval. Concavity with equal
weights bounds the average of the two function values by the midpoint
value. Nonnegativity of the reflected value gives the result. -/
theorem le_two_mul_midpoint_of_nonneg_concaveOn_Icc
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc a b) f)
    (hnonneg : ∀ y ∈ Set.Icc a b, 0 ≤ f y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    f x ≤ 2 * f ((a + b) / 2) :=
  (by
  have hy : a + b - x ∈ Set.Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hmid := hf.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have heq : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (a + b - x) = (a + b) / 2 := by
    simp only [smul_eq_mul]
    ring
  rw [heq] at hmid
  simp only [smul_eq_mul] at hmid
  linarith [hnonneg _ hy]
)

/-- Nonnegative concave profiles on the closed unit interval, normalized
to one at the midpoint, admit a subsequence converging at every interior
point to a bounded nonnegative concave profile with the same midpoint
normalization.
[LS93, Lemma 2.5, proof of Claim 2, p.380, normalized compactness step]

The limit is nonzero because its midpoint value is one. Endpoint
convergence is unnecessary and is not asserted.

**Proof sketch.** The midpoint bound places every profile between zero
and two on the unit interval. Restrict concavity to the open interval
and apply bounded concave-profile subsequence compactness with bound
two. Evaluate the convergence at the midpoint: all sequence values are
one, so uniqueness of limits gives midpoint value one for the limit. -/
theorem exists_subseq_tendsto_of_concaveOn_of_midpoint_eq_one
    (f : ℕ → ℝ → ℝ)
    (hconcave : ∀ m : ℕ, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (f m))
    (hnonneg : ∀ m : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f m x)
    (hnorm : ∀ m : ℕ, f m (1 / 2 : ℝ) = 1) :
    ∃ (φ : ℝ → ℝ) (u : ℕ → ℕ),
      StrictMono u ∧
      ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) φ ∧
      φ (1 / 2 : ℝ) = 1 ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, φ x ∈ Set.Icc (0 : ℝ) 2) ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        Filter.Tendsto (fun m : ℕ => f (u m) x) Filter.atTop (nhds (φ x)) :=
  (by
  have hbound (m : ℕ) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      f m x ∈ Set.Icc (0 : ℝ) 2 := by
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    refine ⟨hnonneg m x hx', ?_⟩
    have h := le_two_mul_midpoint_of_nonneg_concaveOn_Icc (hconcave m) (hnonneg m) hx'
    norm_num only [zero_add, hnorm, mul_one] at h
    exact h
  obtain ⟨φ, u, hu, hφc, hφb, hlim⟩ :=
    exists_subseq_tendsto_of_concaveOn_of_uniform_bounds f (by norm_num : (0 : ℝ) ≤ 2)
      (fun m => (hconcave m).subset Set.Ioo_subset_Icc_self (convex_Ioo _ _)) hbound
  refine ⟨φ, u, hu, hφc, ?_, hφb, hlim⟩
  have hmid := hlim (1 / 2 : ℝ) (by constructor <;> norm_num)
  have hconst : Filter.Tendsto (fun m : ℕ => f (u m) (1 / 2 : ℝ))
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [hnorm] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1))
  exact tendsto_nhds_unique hmid hconst
)

/-- Weighted integrals of bounded nonnegative concave profiles converge
under pointwise interior convergence, for every natural power and every
continuous real test function on the closed unit interval.
[LS93, Lemma 2.5, proof of Claim 2, pp.380–381, fixed-interval limit step]

The test function may have either sign. No regularity assumption on the
limit is needed: the existing dominated-convergence theorem handles the
limit integrand from the pointwise convergence and domination hypotheses.

**Proof sketch.** Concavity makes each approximating profile continuous
on the open interval, so its power times the test function is measurable
for the restricted measure. The continuous test function is bounded on
the closed interval. The common profile bound therefore bounds every
integrand in absolute value by one constant, which is integrable on the
open unit interval. Pointwise convergence passes through natural powers
and multiplication. Apply dominated convergence. -/
theorem tendsto_integral_pow_mul_of_concaveOn_of_uniform_bounds
    (f : ℕ → ℝ → ℝ) (φ F : ℝ → ℝ) (d : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hconcave : ∀ m : ℕ, ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (f m))
    (hbound : ∀ m : ℕ, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      f m x ∈ Set.Icc (0 : ℝ) M)
    (hlim : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Filter.Tendsto (fun m : ℕ => f m x) Filter.atTop (nhds (φ x)))
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) :
    Filter.Tendsto
      (fun m : ℕ => ∫ x in Set.Ioo (0 : ℝ) 1, (f m x) ^ d * F x)
      Filter.atTop
      (nhds (∫ x in Set.Ioo (0 : ℝ) 1, (φ x) ^ d * F x)) :=
  (by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => M ^ d * B)
  · intro m
    exact ((ConcaveOn.continuousOn isOpen_Ioo (hconcave m)).pow d |>.mul
      (hF.mono Set.Ioo_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioo
  · exact integrable_const _
  · intro m
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    calc
      ‖(f m x) ^ d * F x‖ = (f m x) ^ d * ‖F x‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg (hbound m x hx).1]
      _ ≤ M ^ d * B := mul_le_mul
        (pow_le_pow_left₀ (hbound m x hx).1 (hbound m x hx).2 d)
        (hB x ⟨hx.1.le, hx.2.le⟩) (norm_nonneg _) (pow_nonneg hM d)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ((hlim x hx).pow d).mul_const (F x)
)

/-- A nonnegative concave real function that is positive somewhere on
its domain is positive at every interior point of that domain.
[LS93, Lemma 2.5, proof of Claim 2, profile-normalization prerequisite]

No continuity, closedness or boundedness assumption on the domain is
needed. Concavity already includes convexity of the domain.

**Proof sketch.** Fix an interior point and a point with positive
function value. If they differ, choose a domain point just beyond the
interior point in the direction away from the positive point. The
interior point is a strictly weighted convex combination of these two
points. Concavity, positivity at the first point and nonnegativity at
the second give a strictly positive value at the interior point. -/
theorem pos_on_interior_of_nonneg_concaveOn
    {D : Set ℝ} {φ : ℝ → ℝ}
    (hconcave : ConcaveOn ℝ D φ)
    (hnonneg : ∀ x ∈ D, 0 ≤ φ x)
    (hpos : ∃ y ∈ D, 0 < φ y) :
    ∀ x ∈ interior D, 0 < φ x :=
  (by
  obtain ⟨y, hy, hφy⟩ := hpos
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let δ := r / (|x - y| + 1)
  have hden : 0 < |x - y| + 1 := by positivity
  have hδ : 0 < δ := div_pos hr hden
  have hz : x + δ * (x - y) ∈ D := hball (by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hδ]
    change r / (|x - y| + 1) * |x - y| < r
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith)
  have hwden : 0 < δ + 1 := by linarith
  have hα : 0 < δ / (δ + 1) := div_pos hδ hwden
  have hβ : 0 ≤ 1 / (δ + 1) := (one_div_pos.mpr hwden).le
  have hsum : δ / (δ + 1) + 1 / (δ + 1) = 1 := by
    field_simp
  have heq : (δ / (δ + 1)) • y + (1 / (δ + 1) : ℝ) • (x + δ * (x - y)) = x := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have h := hconcave.2 hy hz hα.le hβ hsum
  rw [heq] at h
  simp only [smul_eq_mul] at h
  exact lt_of_lt_of_le
    (add_pos_of_pos_of_nonneg (mul_pos hα hφy) (mul_nonneg hβ (hnonneg _ hz))) h
)

/-- A nonnegative concave function with two domain anchors at equal
positive distances from a center has at most linear growth relative to
its value at that center.
[LS93, Lemma 2.5, proof of Claim 2, normalized-profile bound]

Only membership of the two anchors and the evaluation point is
required; no closedness, boundedness or interval representation of the
domain is assumed. The estimate is homogeneous in the function value.

**Proof sketch.** If the evaluation point lies to the right of the
center, express the center as a convex combination of that point and
the left anchor. The coefficient of the evaluation point is
`r / (r + |x - c|)`. Concavity and nonnegativity at the anchor give
the bound after division by this positive coefficient. For points to
the left use the right anchor in the same way. -/
theorem le_one_add_abs_div_mul_of_nonneg_concaveOn
    {D : Set ℝ} {φ : ℝ → ℝ}
    (hconcave : ConcaveOn ℝ D φ)
    (hnonneg : ∀ y ∈ D, 0 ≤ φ y)
    {c r x : ℝ} (hr : 0 < r)
    (hleft : c - r ∈ D) (hright : c + r ∈ D) (hx : x ∈ D) :
    φ x ≤ (1 + |x - c| / r) * φ c :=
  (by
  let d := |x - c|
  have hd : 0 ≤ d := abs_nonneg _
  have hden : 0 < r + d := add_pos_of_pos_of_nonneg hr hd
  have hα : 0 < r / (r + d) := div_pos hr hden
  have hβ : 0 ≤ d / (r + d) := div_nonneg hd hden.le
  have hsum : r / (r + d) + d / (r + d) = 1 := by
    field_simp
  obtain ⟨z, hz, heq⟩ : ∃ z ∈ D,
      (r / (r + d)) • x + (d / (r + d)) • z = c := by
    by_cases hcx : c ≤ x
    · refine ⟨c - r, hleft, ?_⟩
      have hd' : d = x - c := abs_of_nonneg (sub_nonneg.mpr hcx)
      simp only [smul_eq_mul]
      field_simp [ne_of_gt hden]
      rw [hd']
      ring
    · refine ⟨c + r, hright, ?_⟩
      have hd' : d = c - x := by
        dsimp [d]
        rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hcx)), neg_sub]
      simp only [smul_eq_mul]
      field_simp [ne_of_gt hden]
      rw [hd']
      ring
  have h := hconcave.2 hx hz hα.le hβ hsum
  rw [heq] at h
  simp only [smul_eq_mul] at h
  have hmain : r / (r + d) * φ x ≤ φ c :=
    le_trans (le_add_of_nonneg_right (mul_nonneg hβ (hnonneg z hz))) h
  have hbound := (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using hmain)
  calc
    φ x ≤ φ c / (r / (r + d)) := hbound
    _ = (1 + |x - c| / r) * φ c := by
      field_simp [ne_of_gt hr, ne_of_gt hden]
      dsimp [d]
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
