/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Radial crossing integrals

## Main definitions

Crossings are expressed by disagreement of two quadratic sublevel tests.

## Main results

* `scalar_disagreement_limit`: the infinitesimal radial crossing integral.
* `radial_disagreement_bound`: a uniform bound for dominated convergence.

The auxiliary interval and calculus statements are technical lemmas for the
Gaussian ball computation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Example 11.50 and Exercise 11.17.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace BooleanAnalysis.GaussianSpace.RadialCrossings

/-- Quadratic disagreement lies in the closed interval between its radial roots. -/
private theorem quadratic_disagreement_closed (x A d : ℝ)
    (hx : 0 < x) (hA : 0 ≤ A) (hd : 0 ≤ d) :
    (¬ (((x-A)^2 ≤ d) ↔ ((x+A)^2 ≤ d))) →
    |A - Real.sqrt d| ≤ x ∧ x ≤ A + Real.sqrt d := by
  intro h
  have hs := Real.sqrt_nonneg d
  have hsq := Real.sq_sqrt hd
  have horder : (x-A)^2 ≤ (x+A)^2 := by
    nlinarith [mul_nonneg hx.le hA]
  have hm : (x-A)^2 ≤ d := by
    by_contra hm
    exact h ⟨fun hh => (hm hh).elim,
      fun hh => (hm (horder.trans hh)).elim⟩
  have hp : d < (x+A)^2 := by
    by_contra hp
    exact h ⟨fun _ => le_of_not_gt hp, fun _ => hm⟩
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩ <;> nlinarith

/-- The open interval between the radial roots consists of disagreement points. -/
private theorem quadratic_disagreement_open (x A d : ℝ)
    (hd : 0 ≤ d) (hlo : |A - Real.sqrt d| < x)
    (hhi : x < A + Real.sqrt d) :
    ¬ (((x-A)^2 ≤ d) ↔ ((x+A)^2 ≤ d)) := by
  have hs := Real.sqrt_nonneg d
  have hsq := Real.sq_sqrt hd
  obtain ⟨hl, hr⟩ := abs_lt.mp hlo
  have hm : (x-A)^2 ≤ d := by nlinarith
  have hp : d < (x+A)^2 := by nlinarith
  exact fun h => (not_le.mpr hp) (h.mp hm)

/-- The radial-root interval has nonnegative endpoints and width at most twice the offset. -/
private theorem quadratic_interval_width (A d : ℝ) (hA : 0 ≤ A) :
    0 ≤ |A - Real.sqrt d| ∧ |A - Real.sqrt d| ≤ A + Real.sqrt d ∧
    A + Real.sqrt d - |A - Real.sqrt d| ≤ 2*A := by
  have hs := Real.sqrt_nonneg d
  refine ⟨abs_nonneg _, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have h := neg_abs_le (A - Real.sqrt d)
  linarith

/-- A negative discriminant makes both quadratic sublevel tests false. -/
private theorem quadratic_agreement_of_negative (x A d : ℝ) (hd : d < 0) :
    (((x-A)^2 ≤ d) ↔ ((x+A)^2 ≤ d)) := by
  constructor <;> intro h <;>
    nlinarith [sq_nonneg (x-A), sq_nonneg (x+A)]

/-- An event squeezed between an open and closed interval has the same Lebesgue integral as that interval.

**Proof sketch.** The possible differences lie at the two endpoints, which are null. -/
private theorem integral_sandwich {f : ℝ → ℝ} {P : ℝ → Prop} [DecidablePred P]
    {L H : ℝ} (hL : 0 ≤ L) (hLH : L ≤ H)
    (hin : ∀ x, x ∈ Ioo L H → P x)
    (hout : ∀ x, 0 < x → P x → x ∈ Icc L H) :
    (∫ x in Ioi 0, if P x then f x else 0) = ∫ x in L..H, f x := by
  rw [← integral_indicator measurableSet_Ioi, intervalIntegral.integral_of_le hLH,
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [Ioo_ae_eq_Icc (μ := volume) (a := L) (b := H)] with x hx
  have hxiff : x ∈ Ioo L H ↔ x ∈ Icc L H := iff_of_eq hx
  by_cases hx0 : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx0]
    by_cases hp : P x
    · rw [if_pos hp, indicator_of_mem (hout x hx0 hp)]
    · rw [if_neg hp, indicator_of_notMem]
      exact fun h => hp (hin x (hxiff.mpr h))
  · rw [indicator_of_notMem hx0, indicator_of_notMem]
    intro h
    have hh := hxiff.mpr h
    exact hx0 (lt_of_le_of_lt hL hh.1)

/-- A density bounded by M on positive radii has interval integral bounded by M times its width. -/
private theorem interval_density_bound {f : ℝ → ℝ} {L H M : ℝ}
    (hL : 0 ≤ L) (hLH : L ≤ H) (hf : ∀ x, 0 < x → |f x| ≤ M) :
    |∫ x in L..H, f x| ≤ M * (H-L) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := L) (b := H) (C := M) (f := f) (fun x hx => by
      rw [uIoc_of_le hLH] at hx
      simpa only [Real.norm_eq_abs] using hf x (lt_of_le_of_lt hL hx.1))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hLH)] using h

/-- Completing the squares rewrites the quadratic crossing event in terms of an absolute offset.

**Proof sketch.** Expand the squares and distinguish the sign of the offset; reversing the two endpoint tests preserves disagreement. -/
private theorem quadratic_event_equiv (c s r a b R : ℝ) :
    (¬((c^2*R^2+s^2*b+2*c*s*R*a≤r^2) ↔
       (c^2*R^2+s^2*b-2*c*s*R*a≤r^2))) ↔
    (¬(((c*R-|s*a|)^2≤r^2-s^2*(b-a^2)) ↔
       ((c*R+|s*a|)^2≤r^2-s^2*(b-a^2)))) := by
  have hm : (c*R-s*a)^2 - (r^2-s^2*(b-a^2)) =
      (c^2*R^2+s^2*b-2*c*s*R*a)-r^2 := by ring
  have hp : (c*R+s*a)^2 - (r^2-s^2*(b-a^2)) =
      (c^2*R^2+s^2*b+2*c*s*R*a)-r^2 := by ring
  have hmi : (c*R-s*a)^2≤r^2-s^2*(b-a^2) ↔
      c^2*R^2+s^2*b-2*c*s*R*a≤r^2 := by
    constructor <;> intro h <;> linarith only [hm,h]
  have hpi : (c*R+s*a)^2≤r^2-s^2*(b-a^2) ↔
      c^2*R^2+s^2*b+2*c*s*R*a≤r^2 := by
    constructor <;> intro h <;> linarith only [hp,h]
  by_cases hsa : 0 ≤ s*a
  · rw [abs_of_nonneg hsa,hmi,hpi]
    tauto
  · simp only [abs_of_neg (lt_of_not_ge hsa), sub_neg_eq_add, ← sub_eq_add_neg]
    rw [hmi,hpi]

/-- For a nonnegative discriminant, the radial disagreement integral is the integral between the two radial roots.

**Proof sketch.** The open-root interval implies disagreement, and disagreement implies membership in the closed-root interval. The endpoints have zero Lebesgue measure. -/
private theorem scalar_disagreement_integral {f : ℝ → ℝ} {c s r a b : ℝ}
    (hc : 0 < c) (hd : 0 ≤ r^2-s^2*(b-a^2)) :
    (∫ R in Ioi 0, if ¬((c^2*R^2+s^2*b+2*c*s*R*a≤r^2) ↔
       (c^2*R^2+s^2*b-2*c*s*R*a≤r^2)) then f R else 0) =
    ∫ R in (abs (abs (s*a) - Real.sqrt (r^2-s^2*(b-a^2))) / c)..
      ((|s*a| + Real.sqrt (r^2-s^2*(b-a^2))) / c), f R := by
  classical
  have hw := quadratic_interval_width |s*a| (r^2-s^2*(b-a^2)) (abs_nonneg _)
  apply integral_sandwich (div_nonneg hw.1 hc.le)
    (div_le_div_of_nonneg_right hw.2.1 hc.le)
  · intro R hR
    apply (quadratic_event_equiv c s r a b R).mpr
    apply quadratic_disagreement_open _ _ _ hd
    · have h := (div_lt_iff₀ hc).mp hR.1
      simpa only [mul_comm] using h
    · have h := (lt_div_iff₀ hc).mp hR.2
      simpa only [mul_comm] using h
  · intro R hR h
    have hh := quadratic_disagreement_closed (c*R) |s*a| (r^2-s^2*(b-a^2))
      (mul_pos hc hR) (abs_nonneg _) hd ((quadratic_event_equiv c s r a b R).mp h)
    constructor
    · apply (div_le_iff₀ hc).mpr
      simpa only [mul_comm] using hh.1
    · apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hh.2

/-- A negative discriminant gives zero disagreement integral. -/
private theorem scalar_disagreement_integral_negative {f : ℝ → ℝ} {c s r a b : ℝ}
    (hd : r^2-s^2*(b-a^2) < 0) :
    (∫ R in Ioi 0, if ¬((c^2*R^2+s^2*b+2*c*s*R*a≤r^2) ↔
       (c^2*R^2+s^2*b-2*c*s*R*a≤r^2)) then f R else 0) = 0 := by
  have hzero : (fun R : ℝ => if ¬((c^2*R^2+s^2*b+2*c*s*R*a≤r^2) ↔
       (c^2*R^2+s^2*b-2*c*s*R*a≤r^2)) then f R else 0) = 0 := by
    funext R
    have h := quadratic_agreement_of_negative (c*R) |s*a| _ hd
    have hn : ¬ ¬((c^2*R^2+s^2*b+2*c*s*R*a≤r^2) ↔
       (c^2*R^2+s^2*b-2*c*s*R*a≤r^2)) :=
      fun hn => ((quadratic_event_equiv c s r a b R).mp hn) h
    exact if_neg hn
  rw [hzero]
  exact integral_zero _ _

/-- The radial disagreement quotient is bounded by twice the density bound times the absolute directional coordinate.

**Proof sketch.** If the discriminant is negative the integral is zero. Otherwise bound the density integral by the radial-root interval width and then bound that width by twice the offset. -/
private theorem scalar_disagreement_bound {f : ℝ → ℝ} {c s r a b t M : ℝ}
    (hc : 0 < c) (ht : 0 < t) (hM : 0 ≤ M)
    (hf : ∀ x, 0 < x → |f x| ≤ M)
    (hfac : (2*|s|/c)/t ≤ 2) :
    |(∫ R in Ioi 0, if ¬((c^2*R^2+s^2*b+2*c*s*R*a≤r^2) ↔
       (c^2*R^2+s^2*b-2*c*s*R*a≤r^2)) then f R else 0)/t| ≤ 2*M*|a| := by
  by_cases hd : 0 ≤ r^2-s^2*(b-a^2)
  · rw [scalar_disagreement_integral hc hd, abs_div, abs_of_pos ht]
    have hw := quadratic_interval_width |s*a| (r^2-s^2*(b-a^2)) (abs_nonneg _)
    have hwc : (|s*a| + Real.sqrt (r^2-s^2*(b-a^2)))/c -
        abs (abs (s*a) - Real.sqrt (r^2-s^2*(b-a^2)))/c ≤ 2*|s*a|/c := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right hw.2.2 hc.le
    have hb := interval_density_bound (div_nonneg hw.1 hc.le)
      (div_le_div_of_nonneg_right hw.2.1 hc.le) hf
    calc
      _ ≤ (M*((|s*a| + Real.sqrt (r^2-s^2*(b-a^2)))/c -
          abs (abs (s*a) - Real.sqrt (r^2-s^2*(b-a^2)))/c))/t :=
        div_le_div_of_nonneg_right hb ht.le
      _ ≤ (M*(2*|s*a|/c))/t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwc hM) ht.le
      _ = M*|a| *((2*|s|/c)/t) := by rw [abs_mul]; ring
      _ ≤ M*|a| *2 := mul_le_mul_of_nonneg_left hfac (mul_nonneg hM (abs_nonneg _))
      _ = 2*M*|a| := by ring
  · rw [scalar_disagreement_integral_negative (lt_of_not_ge hd), zero_div, abs_zero]
    positivity

/-- For a density continuous near a positive radius, a shrinking interval quotient tends to the density value times the limiting width quotient.

**Proof sketch.** The fundamental theorem of calculus makes the integration error little-o of the interval width. The convergent width quotient makes this error vanish after division by the parameter. -/
private theorem shrinking_interval_quotient {f L H : ℝ → ℝ} {r d : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (Set.Ioi 0))
    (hL : Tendsto L (𝓝[>] 0) (𝓝 r)) (hH : Tendsto H (𝓝[>] 0) (𝓝 r))
    (hd : Tendsto (fun t => (H t - L t) / t) (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun t => (∫ x in L t..H t, f x) / t) (𝓝[>] 0) (𝓝 (f r * d)) := by
  have hmeas : StronglyMeasurableAtFilter f (𝓝 r) volume :=
    hf.stronglyMeasurableAtFilter isOpen_Ioi r hr
  have hcont : ContinuousAt f r := hf.continuousAt (isOpen_Ioi.mem_nhds hr)
  have he := intervalIntegral.integral_sub_linear_isLittleO_of_tendsto_ae
    hmeas (hcont.mono_left inf_le_left) hL hH
  have hw : (fun t => H t - L t) =O[𝓝[>] 0] (fun t : ℝ => t) :=
    Asymptotics.isBigO_of_div_tendsto_nhds
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact fun ht0 => (ne_of_gt ht ht0).elim)
      d hd
  have hz := (he.trans_isBigO hw).tendsto_div_nhds_zero
  have hh := hz.add (hd.mul_const (f r))
  convert hh using 1
  · funext t
    simp only [smul_eq_mul]
    ring
  · simp only [zero_add, mul_comm]

/-- At angles between zero and one, the cosine half-angle is positive and the normalized crossing width factor is at most two. -/
private theorem half_angle_width_bound {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < Real.cos (t/2) ∧ (2 * |Real.sin (t/2)| / Real.cos (t/2)) / t ≤ 2 := by
  have hsq : t^2 ≤ 1 := by
    nlinarith [mul_nonneg (le_of_lt ht) (sub_nonneg.mpr (le_of_lt ht1))]
  have hc : (1/2 : ℝ) ≤ Real.cos (t/2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t/2)]
  have hcpos : 0 < Real.cos (t/2) := lt_of_lt_of_le (by norm_num) hc
  refine ⟨hcpos, ?_⟩
  have hs : |Real.sin (t/2)| ≤ t/2 := by
    simpa only [abs_of_pos (half_pos ht)] using (Real.abs_sin_le_abs (x := t/2))
  apply (div_le_iff₀ ht).mpr
  apply (div_le_iff₀ hcpos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hc (le_of_lt ht)]

/-- The radial quadratic crossing quotient tends to the density at the radius times the absolute directional coordinate.

**Proof sketch.** Complete the squares. For sufficiently small positive angles, the radial endpoints converge to the radius and their separation divided by the angle tends to the absolute directional coordinate. Apply the shrinking-interval integral limit. -/
theorem scalar_disagreement_limit {f : ℝ → ℝ} {r a b : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (Ioi 0)) :
    Tendsto (fun t : ℝ =>
      (∫ R in Ioi 0, if ¬((Real.cos (t/2)^2*R^2+Real.sin (t/2)^2*b+
        2*Real.cos (t/2)*Real.sin (t/2)*R*a≤r^2) ↔
        (Real.cos (t/2)^2*R^2+Real.sin (t/2)^2*b-
        2*Real.cos (t/2)*Real.sin (t/2)*R*a≤r^2)) then f R else 0)/t)
      (𝓝[>] 0) (𝓝 (f r * |a|)) := by
  let D : ℝ → ℝ := fun t => r^2-Real.sin (t/2)^2*(b-a^2)
  let A : ℝ → ℝ := fun t => |Real.sin (t/2)*a|
  let L : ℝ → ℝ := fun t => (Real.sqrt (D t)-A t)/Real.cos (t/2)
  let H : ℝ → ℝ := fun t => (Real.sqrt (D t)+A t)/Real.cos (t/2)
  have hL : Tendsto L (𝓝[>] 0) (𝓝 r) := by
    have hc : ContinuousAt L 0 := by
      dsimp only [L,D,A]
      fun_prop (disch := norm_num)
    simpa [L,D,A,Real.sqrt_sq_eq_abs,abs_of_pos hr] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hH : Tendsto H (𝓝[>] 0) (𝓝 r) := by
    have hc : ContinuousAt H 0 := by
      dsimp only [H,D,A]
      fun_prop (disch := norm_num)
    simpa [H,D,A,Real.sqrt_sq_eq_abs,abs_of_pos hr] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun t : ℝ => Real.sin (t/2)/t)
      (𝓝[>] 0) (𝓝 (1/2 : ℝ)) := by
    have hd :=
      (((hasDerivAt_id (0 : ℝ)).div_const 2).sin).tendsto_slope_zero_right
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have hc : Tendsto (fun t : ℝ => Real.cos (t/2)) (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun t : ℝ => Real.cos (t/2)) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hw : Tendsto (fun t => (H t-L t)/t) (𝓝[>] 0) (𝓝 |a|) := by
    have hh := (hs.abs.mul_const (2*|a|)).div hc (by norm_num)
    have hh' : Tendsto
        (fun t => (|Real.sin (t/2)/t| *(2*|a|))/Real.cos (t/2))
        (𝓝[>] 0) (𝓝 |a|) := by
      convert hh using 1 <;> norm_num <;> ring
    apply hh'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    dsimp only [L,H,A]
    simp only [abs_div,abs_mul,abs_of_pos ht]
    simp only [div_eq_mul_inv]
    ring
  have hlimit := shrinking_interval_quotient hr hf hL hH hw
  have hD : Tendsto D (𝓝[>] 0) (𝓝 (r^2)) := by
    have h : ContinuousAt D 0 := by dsimp only [D]; fun_prop
    simpa [D] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hmid : Tendsto (fun t => Real.sqrt (D t)-A t)
      (𝓝[>] 0) (𝓝 r) := by
    have h : ContinuousAt (fun t => Real.sqrt (D t)-A t) 0 := by
      dsimp only [D,A]
      fun_prop
    simpa [D,A,Real.sqrt_sq_eq_abs,abs_of_pos hr] using
      h.tendsto.mono_left nhdsWithin_le_nhds
  have hevD : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < D t :=
    hD.eventually (eventually_gt_nhds (sq_pos_of_pos hr))
  have hevMid : ∀ᶠ t in 𝓝[>] (0:ℝ), A t < Real.sqrt (D t) := by
    simpa only [sub_pos] using hmid.eventually (eventually_gt_nhds hr)
  have ht1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t<1 :=
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin,ht1,hevD,hevMid] with t ht ht1 hd hm
  have hct := (half_angle_width_bound ht ht1).1
  rw [scalar_disagreement_integral hct hd.le]
  have habs : abs (A t-Real.sqrt (D t))=Real.sqrt (D t)-A t := by
    rw [abs_of_neg (sub_neg.mpr hm)]
    ring
  change (∫ R in L t..H t,f R)/t =
    (∫ R in abs (A t-Real.sqrt (D t))/Real.cos (t/2)..
      (A t+Real.sqrt (D t))/Real.cos (t/2), f R)/t
  rw [habs]
  congr 2
  dsimp only [H]
  congr 1
  ring

/-- For angles between zero and one, the radial crossing quotient is bounded by twice a positive-radius density bound times the absolute directional coordinate. -/
theorem radial_disagreement_bound {f : ℝ → ℝ} {r a b t M : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hM : 0 ≤ M)
    (hf : ∀ x, 0 < x → |f x| ≤ M) :
    |(∫ R in Ioi 0, if ¬((Real.cos (t/2)^2*R^2+Real.sin (t/2)^2*b+
        2*Real.cos (t/2)*Real.sin (t/2)*R*a≤r^2) ↔
        (Real.cos (t/2)^2*R^2+Real.sin (t/2)^2*b-
        2*Real.cos (t/2)*Real.sin (t/2)*R*a≤r^2)) then f R else 0)/t| ≤
      2*M*|a| := (by
  exact scalar_disagreement_bound (half_angle_width_bound ht ht1).1 ht hM hf
    (half_angle_width_bound ht ht1).2
)

end BooleanAnalysis.GaussianSpace.RadialCrossings
