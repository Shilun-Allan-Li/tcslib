/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exponential envelopes for bounded log-concave densities

## Main definitions

No new definitions.

## Main results

* `concaveOn_log_indicator_pow_mul_exp_div`: log-concavity of zero-extended profile weights.

* `min_mul_abs_sub_le_integral_of_log_concave`: endpoint heights of a
  nonnegative integrable log-concave function control interval length
  through its total integral.
* `concave_le_sub_abs_div_of_boundary_drop`: a boundary drop controls both tails.
* `exists_exp_abs_upper_bound_of_log_concave`: every bounded log-concave probability
  density has a shifted and scaled exponential envelope.

## References

* [LV05] László Lovász and Santosh Vempala, *The Geometry of Logconcave
  Functions and Sampling Algorithms*, manuscript revised March 2005,
  §5.2, proof of Lemma 5.6(a). The results here isolate elementary
  interval-mass and secant prerequisites for exponential envelopes.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- A positive concave profile raised to a natural power, multiplied
by the exponential of a concave exponent, and divided by a positive
constant has a concave logarithm on its support after extension by
zero outside the original convex domain.

This is the elementary log-concavity closure rule behind the
support-and-log formulation in [LV05, §2.1]. The positive divisor may
later be chosen as the integral of the weight; no normalization or
integrability is required for this structural statement.

**Proof sketch.** On the domain the weight is positive, and outside
it the indicator is zero, so the support is exactly that domain.
Monotonicity and concavity of the logarithm make the logarithm of
the positive concave profile concave. On the domain, the logarithm
of the weight is the natural exponent times this profile logarithm,
plus the given concave exponent, minus the logarithm of the positive
divisor. Nonnegative scalar multiplication, addition and a constant
shift preserve concavity. -/
theorem concaveOn_log_indicator_pow_mul_exp_div
    (D : Set ℝ) (φ g : ℝ → ℝ)
    (hφ : ConcaveOn ℝ D φ) (hφpos : ∀ t ∈ D, 0 < φ t)
    (hg : ConcaveOn ℝ D g) (m : ℕ) (Z : ℝ) (hZ : 0 < Z) :
    ConcaveOn ℝ
      (Function.support (D.indicator (fun t : ℝ => (φ t) ^ m * Real.exp (g t) / Z)))
      (fun t : ℝ =>
        Real.log (D.indicator (fun u : ℝ => (φ u) ^ m * Real.exp (g u) / Z) t)) :=
  (by
  have hw (t : ℝ) (ht : t ∈ D) : 0 < (φ t) ^ m * Real.exp (g t) / Z :=
    div_pos (mul_pos (pow_pos (hφpos t ht) m) (Real.exp_pos _)) hZ
  have hsupp : Function.support (D.indicator (fun t : ℝ =>
      (φ t) ^ m * Real.exp (g t) / Z)) = D := by
    ext t
    change D.indicator (fun u : ℝ => (φ u) ^ m * Real.exp (g u) / Z) t ≠ 0 ↔ t ∈ D
    by_cases ht : t ∈ D
    · rw [Set.indicator_of_mem ht]
      exact iff_of_true (hw t ht).ne' ht
    · rw [Set.indicator_of_notMem ht]
      simp only [ne_eq, not_true_eq_false, false_iff]
      exact ht
  have hlogφ : ConcaveOn ℝ D (fun t => Real.log (φ t)) := by
    refine ⟨hφ.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hpos : 0 < a • φ x + b • φ y :=
      (convex_Ioi (0 : ℝ)) (hφpos x hx) (hφpos y hy) ha hb hab
    exact (strictConcaveOn_log_Ioi.concaveOn.2
      (hφpos x hx) (hφpos y hy) ha hb hab).trans
        (Real.log_le_log hpos (hφ.2 hx hy ha hb hab))
  rw [hsupp]
  apply ((hlogφ.smul (Nat.cast_nonneg m)).add hg).add_const (-Real.log Z) |>.congr
  intro t ht
  change ((m : ℝ) • Real.log (φ t) + g t) + -Real.log Z =
    Real.log (D.indicator (fun u : ℝ => (φ u) ^ m * Real.exp (g u) / Z) t)
  rw [Set.indicator_of_mem ht, Real.log_div
    (mul_ne_zero (pow_ne_zero _ (hφpos t ht).ne') (Real.exp_ne_zero _)) hZ.ne',
    Real.log_mul (pow_ne_zero _ (hφpos t ht).ne') (Real.exp_ne_zero _),
    Real.log_pow, Real.log_exp]
  simp only [smul_eq_mul]
  ring
)


/-- The smaller endpoint value of a nonnegative integrable
log-concave function, multiplied by the distance between the endpoints,
is at most its integral over the whole real line.

This is the elementary interval-mass comparison underlying the
exponential comparison in [LV05, §5.2, proof of Lemma 5.6(a)],
stated without normalization or boundedness assumptions.

**Proof sketch.** If an endpoint value is zero, nonnegativity gives
the result. Otherwise both endpoints lie in the positive support.
Convexity of the support and concavity of the logarithm show that
the function is at least the smaller endpoint value on the whole
joining interval. Integrate this constant lower bound on that interval,
then bound the interval integral by the full nonnegative integral. -/
theorem min_mul_abs_sub_le_integral_of_log_concave
    (w : ℝ → ℝ) (hnonneg : ∀ x : ℝ, 0 ≤ w x)
    (hlog : ConcaveOn ℝ (Function.support w) (fun x : ℝ => Real.log (w x)))
    (hw : Integrable w volume) (a b : ℝ) :
    min (w a) (w b) * |b - a| ≤ ∫ x : ℝ, w x :=
  (by
    by_cases ha : w a = 0
    · simpa only [ha, min_eq_left (hnonneg b), zero_mul] using
        integral_nonneg hnonneg
    by_cases hb : w b = 0
    · simpa only [hb, min_eq_right (hnonneg a), zero_mul] using
        integral_nonneg hnonneg
    have hapos : 0 < w a := lt_of_le_of_ne (hnonneg a) (Ne.symm ha)
    have hbpos : 0 < w b := lt_of_le_of_ne (hnonneg b) (Ne.symm hb)
    have hpoint : ∀ x ∈ Set.uIcc a b, min (w a) (w b) ≤ w x := by
      intro x hx
      have hseg : x ∈ segment ℝ a b := (segment_eq_uIcc a b).symm ▸ hx
      have hxmem := hlog.1.segment_subset ha hb hseg
      have hxpos : 0 < w x := lt_of_le_of_ne (hnonneg x) (Ne.symm hxmem)
      have hg := hlog.ge_on_segment ha hb hseg
      rcases le_total (w a) (w b) with hab | hba
      · rw [min_eq_left hab]
        rw [min_eq_left (Real.log_le_log hapos hab)] at hg
        exact (Real.log_le_log_iff hapos hxpos).mp hg
      · rw [min_eq_right hba]
        rw [min_eq_right (Real.log_le_log hbpos hba)] at hg
        exact (Real.log_le_log_iff hbpos hxpos).mp hg
    calc
      _ = min (w a) (w b) * volume.real (Set.uIcc a b) := by
        rw [Real.volume_real_interval]
      _ ≤ ∫ x in Set.uIcc a b, w x :=
        setIntegral_ge_of_const_le measurableSet_uIcc
          (isCompact_uIcc.measure_lt_top.ne) hpoint hw.integrableOn
      _ ≤ ∫ x : ℝ, w x := setIntegral_le_integral hw (Filter.Eventually.of_forall hnonneg)

)

/-- A concave real function on a convex domain drops at least
linearly with distance from a center beyond radius `r > 0`,
if it has dropped by at least one at every domain point exactly
that distance from the center.

This isolates the one-dimensional secant comparison used in
[LV05, §5.2, proof of Lemma 5.6(a)]. No differentiability, domain
closedness or two-sided neighborhood hypothesis is required.

**Proof sketch.** The point at distance `r` along the segment from
the center to the evaluation point belongs to the convex domain.
The boundary-drop hypothesis bounds the function there by its
center value minus one. Concavity between the center and evaluation
point then bounds the latter value by the center value minus the
ratio of its distance to `r`. -/
theorem concave_le_sub_abs_div_of_boundary_drop
    {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f)
    {a x r : ℝ} (ha : a ∈ s) (hx : x ∈ s) (hr : 0 < r)
    (hdist : r ≤ |x - a|)
    (hdrop : ∀ b ∈ s, |b - a| = r → f b ≤ f a - 1) :
    f x ≤ f a - |x - a| / r :=
  (by
    let t := r / |x - a|
    have hdistpos : 0 < |x - a| := hr.trans_le hdist
    have htpos : 0 < t := div_pos hr hdistpos
    have htone : t ≤ 1 := (div_le_one hdistpos).mpr hdist
    have htdist : t * |x - a| = r := div_mul_cancel₀ r hdistpos.ne'
    let b := (1 - t) * a + t * x
    have hb : b ∈ s := hf.1 ha hx (sub_nonneg.mpr htone) htpos.le (by ring)
    have hbabs : |b - a| = r := by
      have heq : b - a = t * (x - a) := by dsimp only [b]; ring
      rw [heq, abs_mul, abs_of_pos htpos, htdist]
    have hconc := hf.2 ha hx (sub_nonneg.mpr htone) htpos.le (by ring)
    simp only [smul_eq_mul] at hconc
    have hkey : t * (f x - f a) ≤ -1 := by
      have hbnd := hdrop b hb hbabs
      change (1 - t) * f a + t * f x ≤ f b at hconc
      nlinarith
    have hscaled : r * (f x - f a) ≤ -|x - a| := by
      calc
        _ = |x - a| * (t * (f x - f a)) := by rw [← htdist]; ring
        _ ≤ |x - a| * (-1) := mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
        _ = _ := by ring
    have hquot : f x - f a ≤ -|x - a| / r :=
      (le_div_iff₀ hr).mpr (by nlinarith [hscaled])
    rw [neg_div] at hquot
    linarith only [hquot]

)


/-- A bounded nonnegative real probability density whose logarithm is
concave on its support admits a shifted exponential envelope:
for some center `a` and positive scale `k`, its value at every `x`
is at most `4 * exp 2 * k * exp(-k * |x-a|)`.

The argument follows the exponential-secant comparison in
[LV05, §5.2, proof of Lemma 5.6(a)]. This explicit pointwise envelope
uses an approximate maximizer, so no attainment, continuity or
upper semicontinuity assumption is required. The displayed constant
and scale normalization are a coarse technical formulation here.

**Proof sketch.** Let `M` be the positive supremum of the density and
choose `a` where its value exceeds `M/2`. Put `r = 4 * exp 1 / M`.
At either endpoint `a ± r`, the density is at most `M/(2 * exp 1)`:
otherwise concavity of its logarithm keeps it above that level
throughout an interval whose integral would be at least two.
For a point farther along either tail and belonging to the support,
support convexity puts the intervening endpoint in the support.
The logarithm has dropped by at least one there, so decreasing
secant slopes give decay at rate `1/r`. Outside the support the
density is zero. Within distance `r`, its supremum bound is absorbed
by a factor `exp 1`. Taking `k = 1/r` gives the asserted envelope. -/
theorem exists_exp_abs_upper_bound_of_log_concave
    (w : ℝ → ℝ) (hnonneg : ∀ x : ℝ, 0 ≤ w x)
    (hbounded : BddAbove (Set.range w))
    (hlog : ConcaveOn ℝ (Function.support w) (fun x : ℝ => Real.log (w x)))
    (hnorm : (∫ x : ℝ, w x ∂volume) = 1) :
    ∃ a k : ℝ, 0 < k ∧
      ∀ x : ℝ, w x ≤
        4 * Real.exp 2 * k * Real.exp (-k * |x - a|) :=
  (by
    have hw : Integrable w volume := Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
    have hex : ∃ x, 0 < w x := by
      by_contra hn
      push_neg at hn
      have hz : w = 0 := funext fun x => le_antisymm (hn x) (hnonneg x)
      rw [hz] at hnorm
      change (∫ _x : ℝ, (0 : ℝ)) = 1 at hnorm
      rw [integral_zero] at hnorm
      norm_num at hnorm
    let M := sSup (Set.range w)
    have hM : ∀ x, w x ≤ M := fun x => le_csSup hbounded (Set.mem_range_self x)
    obtain ⟨z, hz⟩ := hex
    have hMpos : 0 < M := hz.trans_le (hM z)
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := exists_lt_of_lt_csSup (Set.range_nonempty w)
      (show M / 2 < sSup (Set.range w) by change M / 2 < M; linarith)
    have hapos : 0 < w a := (half_pos hMpos).trans ha
    let r := 4 * Real.exp 1 / M
    let c := M / (2 * Real.exp 1)
    have hr : 0 < r := div_pos (by positivity) hMpos
    have he : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff).mpr (by norm_num)
    have hca : c < w a := lt_of_le_of_lt
      (div_le_div_of_nonneg_left hMpos.le (by norm_num) (by nlinarith [he])) ha
    have hcr : c * r = 2 := by
      dsimp only [c, r]
      field_simp
      ring
    have hboundary : ∀ b, |b - a| = r → w b ≤ c := by
      intro b hb
      by_contra hn
      have hbc : c < w b := lt_of_not_ge hn
      have hmass := min_mul_abs_sub_le_integral_of_log_concave w hnonneg hlog hw a b
      have hle : c * r ≤ 1 := calc
        _ ≤ min (w a) (w b) * r := mul_le_mul_of_nonneg_right
          (le_min hca.le hbc.le) hr.le
        _ = min (w a) (w b) * |b - a| := by rw [hb]
        _ ≤ ∫ x, w x := hmass
        _ = 1 := hnorm
      linarith only [hle, hcr]
    have hdrop : ∀ b ∈ Function.support w, |b - a| = r →
        Real.log (w b) ≤ Real.log (w a) - 1 := by
      intro b hb hbr
      have hbpos : 0 < w b := lt_of_le_of_ne (hnonneg b) (Ne.symm hb)
      have hratio : w b ≤ w a / Real.exp 1 := calc
        _ ≤ c := hboundary b hbr
        _ = (M / 2) / Real.exp 1 := by dsimp only [c]; ring
        _ ≤ w a / Real.exp 1 := div_le_div_of_nonneg_right ha.le (Real.exp_pos 1).le
      have := Real.log_le_log hbpos hratio
      rwa [Real.log_div hapos.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
    have henv : ∀ x, w x ≤ Real.exp 1 * M * Real.exp (-|x - a| / r) := by
      intro x
      by_cases hcentral : |x - a| ≤ r
      · have hrate : -1 ≤ -|x - a| / r := (le_div_iff₀ hr).mpr (by linarith)
        have hexp : 1 ≤ Real.exp 1 * Real.exp (-|x - a| / r) := by
          calc
            1 = Real.exp 0 := Real.exp_zero.symm
            _ ≤ Real.exp (1 + -|x - a| / r) := Real.exp_le_exp.mpr (by linarith)
            _ = _ := Real.exp_add _ _
        calc
          w x ≤ M := hM x
          _ ≤ M * (Real.exp 1 * Real.exp (-|x - a| / r)) :=
            le_mul_of_one_le_right hMpos.le hexp
          _ = _ := by ring
      · by_cases hx : w x = 0
        · rw [hx]
          positivity
        have hlogbound := concave_le_sub_abs_div_of_boundary_drop hlog
          hapos.ne' hx hr (le_of_not_ge hcentral) hdrop
        have htail : w x ≤ w a * Real.exp (-|x - a| / r) := by
          have := Real.exp_le_exp.mpr hlogbound
          rw [Real.exp_log (lt_of_le_of_ne (hnonneg x) (Ne.symm hx)), Real.exp_sub,
            Real.exp_log hapos] at this
          rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
          exact this
        calc
          _ ≤ w a * Real.exp (-|x - a| / r) := htail
          _ ≤ M * Real.exp (-|x - a| / r) :=
            mul_le_mul_of_nonneg_right (hM a) (Real.exp_pos _).le
          _ ≤ Real.exp 1 * (M * Real.exp (-|x - a| / r)) :=
            le_mul_of_one_le_left (by positivity) he
          _ = _ := by ring
    refine ⟨a, 1 / r, one_div_pos.mpr hr, fun x => ?_⟩
    convert henv x using 1
    · dsimp only [r]
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      field_simp


)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
