/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.LIntegral

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exponential mass and polynomial moments

## Main definitions

No new definitions.

## Main results

* `lintegral_exp_neg_Ici_eq_one`: the nonnegative half-line exponential mass is one.

* `lintegral_exp_neg_eq_lintegral_volume_initial`: expresses the exponential
  mass of a measurable subset of the nonnegative half-line as a mixture of
  its initial-interval volumes.
* `lintegral_exp_neg_mul_one_add_eq_two`: the exponential density integrates
  the weight `1 + t` to two.
* `lintegral_exp_neg_le_of_volume_initial_le`: initial-volume bounds control
  exponential mass with constant two.
* `lintegral_one_add_pow_mul_exp_neg_le`: the shifted exponential moment
  of order `q` is at most `exp 1 * q!`.
* `lintegral_exp_neg_Icc`: the mass of `[0, L]` is `1 - exp (-L)`.
* `one_le_of_bound_of_lintegral_sq_exp_neg_eq`: normalized square integral
  one forces any nonnegative uniform bound to be at least one.

* `lintegral_mul_exp_neg_mul_Icc_eq`: affine substitution for decreasing exponential weights.

## References

* Mathlib, `Mathlib.MeasureTheory.Measure.Prod`: Tonelli's theorem.
* Mathlib, `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`:
  the integral of the exponential tail.
* Mathlib, `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`:
  the gamma integral and its values at positive integers.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- The exponential mass of a measurable subset of the nonnegative half-line
equals the exponentially weighted integral of its initial-interval volumes.

This is technical integration glue for the weighted anticoncentration argument.

**Proof sketch.** Express the exponential weight at each nonnegative point as
the integral of the exponential density over the tail starting at that point.
Tonelli's theorem exchanges the point and tail-parameter integrals. For a fixed
tail parameter, the eligible points form the intersection of the original set
with the initial interval ending at that parameter. -/
theorem lintegral_exp_neg_eq_lintegral_volume_initial
    (E : Set ℝ) (hE : MeasurableSet E) (hnonneg : E ⊆ Ici 0) :
    (∫⁻ x in E, ENNReal.ofReal (Real.exp (-x)) ∂volume) =
      ∫⁻ t in Ici (0 : ℝ),
        ENNReal.ofReal (Real.exp (-t)) * volume (E ∩ Iic t) ∂volume :=
  (by
  let w : ℝ → ENNReal := fun t => ENNReal.ofReal (Real.exp (-t))
  have hw : Measurable w := by fun_prop
  have htail (x : ℝ) (hx : 0 ≤ x) :
      (∫⁻ t in Ici (0 : ℝ), (Ici x).indicator w t) = w x := by
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      Ici_inter_Ici, max_eq_left hx, ← restrict_Ioi_eq_restrict_Ici]
    change (∫⁻ t in Ioi x, ENNReal.ofReal (Real.exp (-t))) = _
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi x)
      (Filter.Eventually.of_forall (fun t => (Real.exp_pos (-t)).le)),
      integral_exp_neg_Ioi]
  have hmeas : Measurable (fun z : ℝ × ℝ =>
      (Ici z.1).indicator w z.2) := by
    change Measurable ({z : ℝ × ℝ | z.1 ≤ z.2}.indicator (fun z => w z.2))
    exact (hw.comp measurable_snd).indicator (measurableSet_le measurable_fst measurable_snd)
  calc
    _ = ∫⁻ x in E, ∫⁻ t in Ici (0 : ℝ), (Ici x).indicator w t := by
      apply setLIntegral_congr_fun hE
      intro x hx
      exact (htail x (hnonneg hx)).symm
    _ = ∫⁻ t in Ici (0 : ℝ), ∫⁻ x in E, (Ici x).indicator w t :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro t
      have heq : (fun x : ℝ => (Ici x).indicator w t) =
          (Iic t).indicator (fun _ : ℝ => w t) := by
        funext x
        rfl
      rw [heq, lintegral_indicator_const measurableSet_Iic,
        Measure.restrict_apply measurableSet_Iic, inter_comm]
)


/-- The raw exponential density has total mass one on the nonnegative
half-line.

This is shared technical normalization glue for the exponential and
Laplace estimates, obtained directly from the existing improper
integral of `exp(-t)`.

**Proof sketch.** The open and closed nonnegative half-lines agree
almost everywhere. Convert the nonnegative Lebesgue integral on the
open half-line to the Bochner integral, using the known integrability
of the exponential, and apply its exact improper-integral formula. -/
theorem lintegral_exp_neg_Ici_eq_one :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) ∂volume) = 1 :=
  (by
  rw [← restrict_Ioi_eq_restrict_Ici,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
      (Filter.Eventually.of_forall (fun t => (Real.exp_pos (-t)).le)),
    integral_exp_neg_Ioi]
  simp
)


/-- The exponential density on the nonnegative half-line integrates the
weight `1 + t` to two.

This is technical normalization glue for the weighted anticoncentration bound.

**Proof sketch.** The exponential density has total mass one. Apply the
initial-interval volume identity to the entire nonnegative half-line: its
initial-interval volume at a nonnegative parameter is that parameter, so the
first moment of the exponential density is also one. Split the weighted
integrand into these two nonnegative integrands and add their integrals. -/
theorem lintegral_exp_neg_mul_one_add_eq_two :
    (∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (1 + t) ∂volume) = 2 :=
  (by
  have hmass : (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-t))) = 1 :=
    lintegral_exp_neg_Ici_eq_one
  have hmoment : (∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal t) = 1 := by
    rw [← hmass]
    symm
    calc
      _ = ∫⁻ t in Ici (0 : ℝ),
          ENNReal.ofReal (Real.exp (-t)) * volume (Ici (0 : ℝ) ∩ Iic t) :=
        lintegral_exp_neg_eq_lintegral_volume_initial (Ici 0) measurableSet_Ici
          (Subset.refl _)
      _ = _ := by
        apply setLIntegral_congr_fun measurableSet_Ici
        intro t ht
        dsimp only
        rw [Ici_inter_Iic, Real.volume_Icc, sub_zero]
  calc
    _ = ∫⁻ t in Ici (0 : ℝ),
        (ENNReal.ofReal (Real.exp (-t)) +
          ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal t) := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro t ht
      dsimp only
      rw [ENNReal.ofReal_add (by positivity) ht, ENNReal.ofReal_one, mul_add, mul_one]
    _ = _ := by
      rw [lintegral_add_left (by fun_prop), hmass, hmoment]
      norm_num
)



/-- If every initial-interval volume of a measurable subset of the nonnegative
half-line is at most `c * (1 + t)`, then its exponential mass is at most `2 * c`.

This is technical integration glue for the weighted anticoncentration bound.

**Proof sketch.** Express the exponential mass using the initial-interval
volume identity. Apply the assumed bound pointwise at each nonnegative
parameter, factor the constant out of the nonnegative integral, and use that
the exponential density integrates the weight `1 + t` to two. -/
theorem lintegral_exp_neg_le_of_volume_initial_le
    (E : Set ℝ) (hE : MeasurableSet E) (hnonneg : E ⊆ Ici 0)
    (c : ENNReal)
    (hvolume : ∀ t : ℝ, 0 ≤ t →
      volume (E ∩ Iic t) ≤ c * ENNReal.ofReal (1 + t)) :
    (∫⁻ x in E, ENNReal.ofReal (Real.exp (-x)) ∂volume) ≤ 2 * c :=
  (by
  rw [lintegral_exp_neg_eq_lintegral_volume_initial E hE hnonneg]
  calc
    _ ≤ ∫⁻ t in Ici (0 : ℝ),
        c * (ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (1 + t)) := by
      apply setLIntegral_mono' measurableSet_Ici
      intro t ht
      calc
        _ ≤ ENNReal.ofReal (Real.exp (-t)) * (c * ENNReal.ofReal (1 + t)) :=
          mul_le_mul_left' (hvolume t ht) _
        _ = _ := by ac_rfl
    _ = c * 2 := by
      rw [lintegral_const_mul c (by fun_prop), lintegral_exp_neg_mul_one_add_eq_two]
    _ = 2 * c := mul_comm _ _
)


/-- The `q`-th moment of `1 + t` under the exponential density on the
nonnegative half-line is at most `exp 1 * q!`.

This is technical moment-estimation glue for the weighted polynomial bound.

**Proof sketch.** Translate by one, writing `u = t + 1`. The integral becomes
`exp 1` times the integral of `u ^ q * exp (-u)` over `u ≥ 1`. Enlarge that
domain to the nonnegative half-line. The resulting integral equals `q!`
by the integral representation of the gamma function and its value at
the positive integer `q + 1`. -/
theorem lintegral_one_add_pow_mul_exp_neg_le (q : ℕ) :
    (∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal ((1 + t) ^ q) *
        ENNReal.ofReal (Real.exp (-t)) ∂volume) ≤
      ENNReal.ofReal (Real.exp 1 * (q.factorial : ℝ)) :=
  (by
  let g : ℝ → ENNReal := fun u =>
    ENNReal.ofReal (u ^ q) * ENNReal.ofReal (Real.exp (-u))
  have hgamma : (∫⁻ t in Ici (0 : ℝ), g t) =
      ENNReal.ofReal (q.factorial : ℝ) := by
    have hi : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ q) (Ioi 0) := by
      simpa using
        (Real.GammaIntegral_convergent (s := (q : ℝ) + 1) (by positivity))
    change (∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal (t ^ q) * ENNReal.ofReal (Real.exp (-t))) = _
    rw [← restrict_Ioi_eq_restrict_Ici]
    simp_rw [← ENNReal.ofReal_mul' (by positivity : 0 ≤ Real.exp (-_))]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hi.congr (Filter.Eventually.of_forall (fun t => mul_comm _ _)))]
    · congr 1
      rw [← Real.Gamma_nat_eq_factorial q,
        Real.Gamma_eq_integral (by positivity : (0 : ℝ) < (q : ℝ) + 1)]
      simp only [add_sub_cancel_right, Real.rpow_natCast, mul_comm]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le
  have hshift : (∫⁻ t in Ici (0 : ℝ), g (1 + t)) =
      ∫⁻ u in Ici (1 : ℝ), g u := by
    rw [← lintegral_indicator measurableSet_Ici,
      ← lintegral_indicator measurableSet_Ici]
    calc
      _ = ∫⁻ t : ℝ, (Ici (1 : ℝ)).indicator g (1 + t) := by
        apply lintegral_congr
        intro t
        by_cases ht : 0 ≤ t
        · rw [indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht),
            indicator_of_mem (show 1 + t ∈ Ici (1 : ℝ) by
              change 1 ≤ 1 + t
              linarith)]
        · rw [indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht),
            indicator_of_notMem (show 1 + t ∉ Ici (1 : ℝ) by
              change ¬ 1 ≤ 1 + t
              linarith)]
      _ = _ := lintegral_add_left_eq_self _ 1
  have hfactor :
      (∫⁻ t in Ici (0 : ℝ),
        ENNReal.ofReal ((1 + t) ^ q) * ENNReal.ofReal (Real.exp (-t))) =
        ENNReal.ofReal (Real.exp 1) * ∫⁻ t in Ici (0 : ℝ), g (1 + t) := by
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply setLIntegral_congr_fun measurableSet_Ici
    intro t ht
    dsimp only [g]
    have he : Real.exp (-t) = Real.exp 1 * Real.exp (-(1 + t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, ENNReal.ofReal_mul (Real.exp_pos 1).le]
    ac_rfl
  rw [hfactor, hshift, ENNReal.ofReal_mul (Real.exp_pos 1).le]
  apply mul_le_mul_left'
  rw [← hgamma]
  exact lintegral_mono_set (fun u hu =>
    (show (0 : ℝ) ≤ u by linarith [show (1 : ℝ) ≤ u from hu]))
)


/-- The exponential density has mass `1 - exp (-L)` on `[0, L]` whenever
`L ≥ 0`.

This is technical normalization glue for the finite-interval exponential
small-ball bound.

**Proof sketch.** Partition the nonnegative half-line into `[0, L]` and
`(L, ∞)`. The exponential density has total mass one on the half-line and
mass `exp (-L)` on the tail. Both masses are finite, so subtraction gives
the stated interval mass. -/
theorem lintegral_exp_neg_Icc (L : ℝ) (hL : 0 ≤ L) :
    (∫⁻ x in Icc (0 : ℝ) L,
      ENNReal.ofReal (Real.exp (-x)) ∂volume) =
        ENNReal.ofReal (1 - Real.exp (-L)) :=
  (by
  have htail (c : ℝ) :
      (∫⁻ x in Ioi c, ENNReal.ofReal (Real.exp (-x))) =
        ENNReal.ofReal (Real.exp (-c)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi c)
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-x)).le)),
      integral_exp_neg_Ioi]
  have htotal : (∫⁻ x in Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-x))) = 1 := by
    rw [← restrict_Ioi_eq_restrict_Ici, htail]
    simp
  have hdis : Disjoint (Icc (0 : ℝ) L) (Ioi L) := by
    exact disjoint_left.mpr (fun x hx hx' => not_lt_of_ge hx.2 hx')
  have hsplit := lintegral_union (μ := volume)
    (f := fun x : ℝ => ENNReal.ofReal (Real.exp (-x))) measurableSet_Ioi hdis
  rw [Icc_union_Ioi_eq_Ici hL, htotal, htail] at hsplit
  rw [ENNReal.ofReal_sub 1 (Real.exp_pos (-L)).le, ENNReal.ofReal_one]
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hsplit.symm
)


/-- A nonnegative uniform bound `B` for a real-valued function on `[0, L]`,
where `L > 0`, is at least one if the function has square integral one
against the normalized exponential density on that interval.

This is technical normalization glue; no measurability assumption on the
function is needed for the pointwise comparison of nonnegative integrals.

**Proof sketch.** The pointwise bound implies `f x ^ 2 ≤ B ^ 2`.
Multiply by the nonnegative exponential density and integrate on `[0, L]`.
Its mass is `Z = 1 - exp (-L) > 0`, so the assumed normalization gives
`Z ≤ B ^ 2 * Z`. Cancel `Z` to obtain `1 ≤ B ^ 2`; since `B ≥ 0`,
this implies `1 ≤ B`. -/
theorem one_le_of_bound_of_lintegral_sq_exp_neg_eq
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc (0 : ℝ) L, |f x| ≤ B)
    (hnorm :
      (∫⁻ x in Icc (0 : ℝ) L,
        ENNReal.ofReal ((f x) ^ 2) *
          ENNReal.ofReal (Real.exp (-x)) ∂volume) =
        ENNReal.ofReal (1 - Real.exp (-L))) :
    1 ≤ B :=
  (by
  have hZ : 0 < 1 - Real.exp (-L) := by
    have h := Real.exp_lt_one_iff.mpr (show -L < 0 by linarith)
    linarith
  have hle : ENNReal.ofReal (1 - Real.exp (-L)) ≤
      ENNReal.ofReal (B ^ 2 * (1 - Real.exp (-L))) := by
    rw [← hnorm, ENNReal.ofReal_mul (sq_nonneg B),
      ← lintegral_exp_neg_Icc L hL.le, ← lintegral_const_mul _ (by fun_prop)]
    apply setLIntegral_mono' measurableSet_Icc
    intro x hx
    exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (by
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg (f x)) (hbound x hx) 2)) _
  have hreal : 1 - Real.exp (-L) ≤ B ^ 2 * (1 - Real.exp (-L)) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg B) hZ.le)).mp hle
  have hsq : 1 ≤ B ^ 2 := by nlinarith
  nlinarith
)


/-- A decreasing exponential integral on `[a, b]` transforms under
`u = r * (x - a)`, for `r > 0`, into an integral against `exp (-u)` on
`[0, r * (b - a)]`, with constant factor `exp (-r * a) / r`.

This is technical change-of-variables glue for exponential needles.

**Proof sketch.** Apply the affine change of variables
`x = u / r + a`. Its Jacobian is `1 / r` and it maps the transformed
interval onto `[a, b]`. The exponential weight factors as
`exp (-r * a) * exp (-u)`; extract the constant factor. -/
theorem lintegral_mul_exp_neg_mul_Icc_eq
    (f : ℝ → ENNReal) (hf : Measurable f)
    (a b r : ℝ) (hab : a ≤ b) (hr : 0 < r) :
    (∫⁻ x in Icc a b,
      f x * ENNReal.ofReal (Real.exp (-r * x)) ∂volume) =
      ENNReal.ofReal (Real.exp (-r * a) / r) *
        ∫⁻ u in Icc (0 : ℝ) (r * (b - a)),
          f (u / r + a) *
            ENNReal.ofReal (Real.exp (-u)) ∂volume :=
  (by
  let G : ℝ → ENNReal := fun u =>
    f (u / r + a) * ENNReal.ofReal (Real.exp (-u))
  have hG : Measurable G := (hf.comp (by fun_prop)).mul (by fun_prop)
  have hmap : Measure.map (fun x : ℝ => r * (x - a)) volume =
      ENNReal.ofReal |r⁻¹| • volume := by
    calc
      _ = Measure.map (fun x : ℝ => r * x)
          (Measure.map (fun x : ℝ => x - a) volume) :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
      _ = _ := by rw [map_sub_right_eq_self, Real.map_volume_mul_left hr.ne']
  have hpre : (fun x : ℝ => r * (x - a)) ⁻¹' Icc (0 : ℝ) (r * (b - a)) =
      Icc a b := by
    ext x
    change (0 ≤ r * (x - a) ∧ r * (x - a) ≤ r * (b - a)) ↔ a ≤ x ∧ x ≤ b
    constructor
    · rintro ⟨h₀, h₁⟩
      constructor <;> nlinarith
    · rintro ⟨h₀, h₁⟩
      constructor <;> nlinarith
  have hs := setLIntegral_map (μ := volume) (s := Icc (0 : ℝ) (r * (b - a)))
    (g := fun x : ℝ => r * (x - a)) measurableSet_Icc hG (by fun_prop)
  rw [hmap, Measure.restrict_smul, lintegral_smul_measure,
    smul_eq_mul, hpre, abs_of_pos (inv_pos.mpr hr)] at hs
  have hGc : Measurable (fun x : ℝ => G (r * (x - a))) := hG.comp (by fun_prop)
  calc
    _ = ENNReal.ofReal (Real.exp (-r * a)) *
        ∫⁻ x in Icc a b, G (r * (x - a)) := by
      rw [← lintegral_const_mul _ hGc]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only [G]
      rw [mul_div_cancel_left₀ _ hr.ne', sub_add_cancel]
      have he : Real.exp (-r * x) =
          Real.exp (-r * a) * Real.exp (-(r * (x - a))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le]
      ac_rfl
    _ = _ := by
      rw [← hs, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
