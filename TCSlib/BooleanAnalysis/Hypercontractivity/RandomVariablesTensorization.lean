/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Analysis.SpecificLimits.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Product-law tensorization of affine contractions

Integral Minkowski exchanges mixed norms in the proof of hypercontractive
tensorization. An essential-supremum limit argument extends the resulting
product-law contraction to infinite exponents.

## Main definitions

This file introduces no new definitions.

## Main results

* `BooleanAnalysis.Hypercontractivity.Tensorization.lintegral_minkowski`:
  for a jointly measurable nonnegative extended-real function on two probability
  spaces and a real exponent `r ≥ 1`, the `L^r` norm of its integral in the first
  coordinate is bounded by the integral of its sectional `L^r` norms.
* `BooleanAnalysis.Hypercontractivity.Tensorization.mixed_lintegral_le`:
  exchange of the order of finite positive section norms.
* `BooleanAnalysis.Hypercontractivity.Tensorization.affine_sum_le_of_ne_top`:
  affine contractions on two laws give a contraction on their product for finite `q`.
* `BooleanAnalysis.Hypercontractivity.Tensorization.eLpNorm_top_le_of_forall_nat`:
  uniformly bounded high finite norms bound the essential supremum.
* `BooleanAnalysis.Hypercontractivity.Tensorization.affine_sum_le`:
  affine contractions on two laws give a contraction on their product for all exponents.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014; May 2021 arXiv edition, §9.2, Proposition 9.15 and its proof.
-/

open MeasureTheory
open scoped ENNReal

namespace BooleanAnalysis.Hypercontractivity

namespace Tensorization

/-- Taking the `L^r` norm after integrating a jointly measurable nonnegative
extended-real function in the first coordinate is bounded by integrating its
sectional `L^r` norms, for two probability measures and a real exponent `r ≥ 1`.

This is the technical integral Minkowski inequality used for exchanging mixed
norms in [OD14, Prop. 9.15 (proof)]; it is not Proposition 9.15 itself. The
inequality includes `r = 1` and zero or infinite values of the extended integrals,
without integrability or finite-value hypotheses.

**Proof sketch.** For `r = 1`, Tonelli's theorem gives equality. Otherwise put
`H(y) = ∫ f(x,y) dμ(x)` and let `T` be the integral of the sectional `L^r` norms.
If `T` is infinite, the inequality is immediate. For a finite truncation level
`M`, set `H_M = min(H,M)`, `g = H_M^(r-1)`, and `C = ∫ H_M^r dν`. The probability
hypothesis makes `C` finite. Since `H_M ≤ H`, Tonelli and Hölder give
`C ≤ ∫ H g dν = ∫ ∫ f g dν dμ ≤ T C^((r-1)/r)`. If `C = 0`, the desired
truncated bound is immediate; otherwise cancellation gives `C^(1/r) ≤ T`.
Monotone convergence as `M` tends to infinity gives the stated inequality. -/
theorem lintegral_minkowski
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f))
    (r : ℝ) (hr : 1 ≤ r) :
    (∫⁻ y, (∫⁻ x, f x y ∂μ) ^ r ∂ν) ^ (1 / r) ≤
      ∫⁻ x, (∫⁻ y, (f x y) ^ r ∂ν) ^ (1 / r) ∂μ := by
  rcases eq_or_lt_of_le hr with hr | hr
  · subst r
    simpa only [one_div_one, ENNReal.rpow_one] using
      (lintegral_lintegral_swap hf.aemeasurable).symm.le
  · have hr0 : 0 < r := lt_trans zero_lt_one hr
    have hri : 0 < 1 / r := by
      simpa only [one_div] using inv_pos.mpr hr0
    let q : ℝ := r.conjExponent
    have hpq : r.HolderConjugate q :=
      Real.HolderConjugate.conjExponent hr
    let H : β → ℝ≥0∞ := fun y => ∫⁻ x, f x y ∂μ
    let U : ℕ → β → ℝ≥0∞ := fun n y => min (H y) (n : ℝ≥0∞)
    let C : ℕ → ℝ≥0∞ := fun n => ∫⁻ y, U n y ^ r ∂ν
    let T : ℝ≥0∞ :=
      ∫⁻ x, (∫⁻ y, f x y ^ r ∂ν) ^ (1 / r) ∂μ
    have hH : Measurable H := hf.lintegral_prod_left
    have hU (n : ℕ) : Measurable (U n) := hH.min measurable_const
    have hnorm : Measurable
        (fun x => (∫⁻ y, f x y ^ r ∂ν) ^ (1 / r)) :=
      ((hf.pow_const r).lintegral_prod_right).pow_const (1 / r)

    -- Truncation makes the auxiliary moment finite.
    have hCtop (n : ℕ) : C n ≠ ⊤ := by
      have hbound : C n ≤ (n : ℝ≥0∞) ^ r := by
        calc
          C n ≤ ∫⁻ y, (n : ℝ≥0∞) ^ r ∂ν :=
            lintegral_mono fun y =>
              ENNReal.rpow_le_rpow (min_le_right (H y) (n : ℝ≥0∞)) hr0.le
          _ = (n : ℝ≥0∞) ^ r := by simp
      have hNtop : (n : ℝ≥0∞) ^ r ≠ ⊤ := by
        simp [ENNReal.rpow_eq_top_iff, not_lt.mpr hr0.le]
      exact ne_of_lt (lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hNtop))

    have hCnorm (n : ℕ) : C n ^ (1 / r) ≤ T := by
      let g : β → ℝ≥0∞ := fun y => U n y ^ (r - 1)
      have hg : Measurable g := (hU n).pow_const (r - 1)
      have hgp : (∫⁻ y, g y ^ q ∂ν) = C n := by
        dsimp only [g, C]
        simp only [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
      have hfg : Measurable
          (Function.uncurry (fun x y => f x y * g y)) :=
        hf.mul (hg.comp measurable_snd)
      have hswap :
          (∫⁻ y, H y * g y ∂ν) =
            ∫⁻ x, ∫⁻ y, f x y * g y ∂ν ∂μ := by
        calc
          (∫⁻ y, H y * g y ∂ν) =
              ∫⁻ y, ∫⁻ x, f x y * g y ∂μ ∂ν := by
            congr 1
            funext y
            exact
              (lintegral_mul_const (g y)
                (hf.comp (measurable_id.prodMk measurable_const))).symm
          _ = _ := (lintegral_lintegral_swap hfg.aemeasurable).symm
      have hHolder (x : α) :
          (∫⁻ y, f x y * g y ∂ν) ≤
            (∫⁻ y, f x y ^ r ∂ν) ^ (1 / r) * C n ^ (1 / q) := by
        simpa only [Pi.mul_apply, hgp] using
          ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq
            (f := f x) (g := g)
            (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable
            hg.aemeasurable

      -- Hölder and Tonelli bound the truncated moment.
      have hC_le : C n ≤ ∫⁻ y, H y * g y ∂ν := by
        apply lintegral_mono
        intro y
        calc
          U n y ^ r = U n y ^ (1 + (r - 1)) := by
            congr 1
            ring
          _ = U n y ^ (1 : ℝ) * U n y ^ (r - 1) :=
            ENNReal.rpow_add_of_nonneg 1 (r - 1)
              zero_le_one (sub_nonneg.mpr hr.le)
          _ = U n y * g y := by simp only [ENNReal.rpow_one, g]
          _ ≤ H y * g y :=
            mul_le_mul_right' (min_le_left (H y) (n : ℝ≥0∞)) (g y)
      have hCineq : C n ≤ T * C n ^ (1 / q) := by
        calc
          C n ≤ ∫⁻ y, H y * g y ∂ν := hC_le
          _ = ∫⁻ x, ∫⁻ y, f x y * g y ∂ν ∂μ := hswap
          _ ≤ ∫⁻ x,
              (∫⁻ y, f x y ^ r ∂ν) ^ (1 / r) * C n ^ (1 / q) ∂μ :=
            lintegral_mono hHolder
          _ = T * C n ^ (1 / q) :=
            lintegral_mul_const _ hnorm
      by_cases hC0 : C n = 0
      · have hz : C n ^ (1 / r) = 0 :=
          ENNReal.rpow_eq_zero_iff.mpr (Or.inl ⟨hC0, hri⟩)
        rw [hz]
        exact bot_le
      · have hcq0 : C n ^ (1 / q) ≠ 0 := by
          simp [ENNReal.rpow_eq_zero_iff, hC0, hCtop n]
        have hcqtop : C n ^ (1 / q) ≠ ⊤ := by
          simp [ENNReal.rpow_eq_top_iff, hC0, hCtop n]
        have hsplit : C n ^ (1 / r) * C n ^ (1 / q) = C n := by
          rw [← ENNReal.rpow_add (1 / r) (1 / q) hC0 (hCtop n)]
          simp only [one_div, hpq.inv_add_inv_eq_one, ENNReal.rpow_one]
        apply (ENNReal.mul_le_mul_right hcq0 hcqtop).mp
        rw [hsplit]
        exact hCineq

    have hCpow (n : ℕ) : C n ≤ T ^ r :=
      (ENNReal.rpow_inv_le_iff hr0).mp
        (by simpa only [one_div] using hCnorm n)

    -- Monotone convergence removes the truncation.
    have hsup (y : β) : (⨆ n : ℕ, U n y ^ r) = H y ^ r := by
      have hsupU : (⨆ n : ℕ, U n y) = H y := by
        calc
          (⨆ n : ℕ, U n y) =
              ⨆ n : ℕ, H y ⊓ (n : ℝ≥0∞) := by
            rfl
          _ = H y ⊓ (⨆ n : ℕ, (n : ℝ≥0∞)) :=
            (inf_iSup_eq _ _).symm
          _ = H y := by rw [ENNReal.iSup_natCast, inf_top_eq]
      have hpowers :=
        (ENNReal.orderIsoRpow r hr0).map_iSup (fun n : ℕ => U n y)
      change (⨆ n : ℕ, U n y) ^ r = ⨆ n : ℕ, U n y ^ r at hpowers
      rw [hsupU] at hpowers
      exact hpowers.symm
    have hmono : Monotone (fun n : ℕ => fun y => U n y ^ r) := by
      intro m n hmn y
      apply ENNReal.rpow_le_rpow _ hr0.le
      exact min_le_min le_rfl (by exact_mod_cast hmn)
    have hfull : (∫⁻ y, H y ^ r ∂ν) = ⨆ n : ℕ, C n := by
      calc
        (∫⁻ y, H y ^ r ∂ν) =
            ∫⁻ y, ⨆ n : ℕ, U n y ^ r ∂ν := by simp only [hsup]
        _ = ⨆ n : ℕ, C n :=
          lintegral_iSup (fun n => (hU n).pow_const r) hmono
    have hpowbound : (∫⁻ y, H y ^ r ∂ν) ≤ T ^ r := by
      rw [hfull]
      exact iSup_le hCpow
    change (∫⁻ y, H y ^ r ∂ν) ^ (1 / r) ≤ T
    simpa only [one_div] using
      (ENNReal.rpow_inv_le_iff hr0).mpr hpowbound

/-- For `0 < p ≤ q`, the `L^q(ν)` norm of the `L^p(μ)` section norms of a jointly
measurable nonnegative extended-real function is at most the `L^p(μ)` norm of its
`L^q(ν)` section norms. Zero and infinite values are allowed.

This is the technical mixed-integral step for finite positive exponents derived from
[OD14, Prop. 9.15 (proof)].

**Proof sketch.** Apply the integral Minkowski inequality to `g ^ p` with exponent
`q / p ≥ 1`. Raise both sides to the positive power `1 / p`, then simplify the
products of exponents. -/
theorem mixed_lintegral_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : α → β → ℝ≥0∞) (hg : Measurable (Function.uncurry g))
    (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    (∫⁻ y, (∫⁻ x, g x y ^ p ∂μ) ^ (q / p) ∂ν) ^ (1 / q) ≤
      (∫⁻ x, (∫⁻ y, g x y ^ q ∂ν) ^ (p / q) ∂μ) ^ (1 / p) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hmul : p * (q / p) = q := by
    field_simp [hp.ne']
    <;> ring
  have hinv : 1 / (q / p) = p / q := by
    field_simp [hp.ne', hq.ne']
    <;> ring
  have hexp : (p / q) * (1 / p) = 1 / q := by
    field_simp [hp.ne', hq.ne']
    <;> ring
  simpa only [← ENNReal.rpow_mul, hmul, hinv, hexp] using
    ENNReal.rpow_le_rpow
      (lintegral_minkowski μ ν (fun x y => g x y ^ p) (hg.pow_const p)
        (q / p) ((one_le_div hp).2 hpq))
      (show 0 ≤ (1 : ℝ) / p by positivity)

/-- Affine `Lᵖ`-to-`Lᑫ` contractions for two probability measures also contract affine
functions of the sum under their product measure, whenever `1 ≤ p ≤ q < ∞`.

This is the finite-`q` product-law technical step in [OD14, Prop. 9.15 (proof)].
Its hypotheses are the two affine norm inequalities themselves, so no separate
bound on `ρ` or finite-moment assumption is required.

**Proof sketch.** Tonelli expresses the output `Lᑫ` norm as the outer `Lᑫ` norm
of the `Lᑫ` norms of its sections. Apply the contraction for `μ` with constant
term `a + ρ * b * y`, exchange the mixed `Lᵖ` norm in `x` and `Lᑫ` norm in `y`
by Minkowski, then apply the contraction for `ν` with constant term `a + b * x`.
Tonelli identifies the resulting norm with the input `Lᵖ` norm. All norms are
extended-valued, so sections with infinite norm require no conversion to real norms. -/
theorem affine_sum_le_of_ne_top
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≠ ∞)
    (ρ : ℝ)
    (hμ : ∀ a b : ℝ,
      eLpNorm (fun x : ℝ => a + ρ * b * x) q μ ≤
        eLpNorm (fun x : ℝ => a + b * x) p μ)
    (hν : ∀ a b : ℝ,
      eLpNorm (fun y : ℝ => a + ρ * b * y) q ν ≤
        eLpNorm (fun y : ℝ => a + b * y) p ν) :
    ∀ a b : ℝ,
      eLpNorm (fun z : ℝ × ℝ => a + ρ * b * (z.1 + z.2)) q (μ.prod ν) ≤
        eLpNorm (fun z : ℝ × ℝ => a + b * (z.1 + z.2)) p (μ.prod ν) := by
  have hp_top : p ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hpq (lt_top_iff_ne_top.mpr hq))
  have hp_zero : p ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hq_zero : q ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (hp.trans hpq))
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
  have hqR : 0 < q.toReal := ENNReal.toReal_pos hq_zero hq
  have hpqR : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  intro a b
  have hF : Measurable
      (fun z : ℝ × ℝ => a + ρ * b * (z.1 + z.2)) := by
    fun_prop
  have hG : Measurable
      (fun z : ℝ × ℝ => a + b * z.1 + ρ * b * z.2) := by
    fun_prop
  have hH : Measurable
      (fun z : ℝ × ℝ => a + b * (z.1 + z.2)) := by
    fun_prop
  -- Contract the first affine section.
  have hfirst (y : ℝ) :
      (∫⁻ x, ‖a + ρ * b * (x + y)‖ₑ ^ q.toReal ∂μ) ≤
        (∫⁻ x, ‖a + b * x + ρ * b * y‖ₑ ^ p.toReal ∂μ) ^
          (q.toReal / p.toReal) := by
    have hf :
        (fun x : ℝ => a + ρ * b * (x + y)) =
          (fun x : ℝ => (a + ρ * b * y) + ρ * b * x) := by
      funext x
      ring
    have hg :
        (fun x : ℝ => a + b * x + ρ * b * y) =
          (fun x : ℝ => (a + ρ * b * y) + b * x) := by
      funext x
      ring
    have hc := hμ (a + ρ * b * y) b
    rw [← hf, ← hg,
      eLpNorm_eq_lintegral_rpow_enorm hq_zero hq,
      eLpNorm_eq_lintegral_rpow_enorm hp_zero hp_top] at hc
    have hr := ENNReal.rpow_le_rpow hc hqR.le
    simp only [one_div] at hr
    rw [ENNReal.rpow_inv_rpow hqR.ne', ← ENNReal.rpow_mul] at hr
    simpa only [div_eq_mul_inv, mul_comm] using hr
  -- Contract the second affine section.
  have hsecond (x : ℝ) :
      (∫⁻ y, ‖a + b * x + ρ * b * y‖ₑ ^ q.toReal ∂ν) ^
          (p.toReal / q.toReal) ≤
        ∫⁻ y, ‖a + b * (x + y)‖ₑ ^ p.toReal ∂ν := by
    have hh :
        (fun y : ℝ => a + b * (x + y)) =
          (fun y : ℝ => (a + b * x) + b * y) := by
      funext y
      ring
    have hc := hν (a + b * x) b
    rw [← hh,
      eLpNorm_eq_lintegral_rpow_enorm hq_zero hq,
      eLpNorm_eq_lintegral_rpow_enorm hp_zero hp_top] at hc
    have hr := ENNReal.rpow_le_rpow hc hpR.le
    simp only [one_div] at hr
    rw [ENNReal.rpow_inv_rpow hpR.ne', ← ENNReal.rpow_mul] at hr
    simpa only [div_eq_mul_inv, mul_comm] using hr
  rw [eLpNorm_eq_lintegral_rpow_enorm hq_zero hq,
    eLpNorm_eq_lintegral_rpow_enorm hp_zero hp_top]
  calc
    (∫⁻ z : ℝ × ℝ, ‖a + ρ * b * (z.1 + z.2)‖ₑ ^ q.toReal
        ∂(μ.prod ν)) ^ (1 / q.toReal)
      = (∫⁻ y, ∫⁻ x, ‖a + ρ * b * (x + y)‖ₑ ^ q.toReal
          ∂μ ∂ν) ^ (1 / q.toReal) := by
        rw [lintegral_prod _ (hF.enorm.pow_const _).aemeasurable,
          lintegral_lintegral_swap
            (f := fun x y : ℝ => ‖a + ρ * b * (x + y)‖ₑ ^ q.toReal)
            (hF.enorm.pow_const _).aemeasurable]
    _ ≤ (∫⁻ y, (∫⁻ x, ‖a + b * x + ρ * b * y‖ₑ ^ p.toReal ∂μ) ^
          (q.toReal / p.toReal) ∂ν) ^ (1 / q.toReal) :=
        ENNReal.rpow_le_rpow (lintegral_mono hfirst)
          (le_of_lt (one_div_pos.mpr hqR))
    -- Exchange the order of the mixed norms.
    _ ≤ (∫⁻ x, (∫⁻ y, ‖a + b * x + ρ * b * y‖ₑ ^ q.toReal ∂ν) ^
          (p.toReal / q.toReal) ∂μ) ^ (1 / p.toReal) :=
        mixed_lintegral_le μ ν
          (fun x y : ℝ => ‖a + b * x + ρ * b * y‖ₑ)
          hG.enorm p.toReal q.toReal hpR hpqR
    _ ≤ (∫⁻ x, ∫⁻ y, ‖a + b * (x + y)‖ₑ ^ p.toReal
          ∂ν ∂μ) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow (lintegral_mono hsecond)
          (le_of_lt (one_div_pos.mpr hpR))
    _ = (∫⁻ z : ℝ × ℝ, ‖a + b * (z.1 + z.2)‖ₑ ^ p.toReal
          ∂(μ.prod ν)) ^ (1 / p.toReal) := by
        rw [lintegral_prod _ (hH.enorm.pow_const _).aemeasurable]

/-- Uniform bounds on all sufficiently large natural-exponent `eLpNorm`s bound the
infinite-exponent `eLpNorm` of an almost-everywhere strongly measurable real function.

This technical limiting lemma isolates the infinite-exponent passage in
[OD14, Prop. 9.15 (proof)]. The statement extends that argument to an arbitrary
measure and requires bounds only beyond a natural cutoff; it is not the
statement of Proposition 9.15 itself.

**Proof sketch.** If `C = ∞`, the conclusion is immediate. Otherwise, for each
finite threshold `ε > C`, Chebyshev's inequality bounds the measure of
`{x | ε ≤ |f x|}` by `(C / ε)^n` for all sufficiently large natural `n`.
These geometric powers tend to zero, so the level set has measure zero.
Thus `|f| < ε` almost everywhere for every finite `ε > C`, which bounds
the essential supremum by `C`. This argument also includes `C = 0`. -/
theorem eLpNorm_top_le_of_forall_nat
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    {C : ℝ≥0∞} {N : ℕ}
    (hC : ∀ n : ℕ, N ≤ n → eLpNorm f (n : ℝ≥0∞) μ ≤ C) :
    eLpNorm f ∞ μ ≤ C := by
  by_cases hCtop : C = ⊤
  · rw [hCtop]
    exact le_top
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  by_cases hεtop : ε = ⊤
  · rw [hεtop]
    exact le_top
  have hε0 : ε ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hε)
  have hr : C / ε < 1 :=
    (ENNReal.div_lt_iff (Or.inl hε0) (Or.inl hεtop)).2 (by simpa using hε)
  have hmeasure : μ {x | ε ≤ enorm (f x)} ≤ 0 := by
    apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr)
    filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn
    have hn0 : n ≠ 0 := by omega
    calc
      μ {x | ε ≤ enorm (f x)}
          ≤ ε⁻¹ ^ n * eLpNorm f (n : ℝ≥0∞) μ ^ n := by
        simpa only [ENNReal.toReal_natCast, ENNReal.rpow_natCast] using
          (meas_ge_le_mul_pow_eLpNorm_enorm (p := (n : ℝ≥0∞)) μ
            (by exact_mod_cast hn0) (ENNReal.natCast_ne_top n) hf hε0
            (by intro h; exact (hεtop h).elim))
      _ ≤ ε⁻¹ ^ n * C ^ n :=
        mul_le_mul_left'
          (pow_le_pow_left' (hC n (le_trans (le_max_left N 1) hn)) n) _
      _ = (C / ε) ^ n := by
        simp only [div_eq_mul_inv, mul_pow]
        exact mul_comm _ _
  have hAE : ∀ᵐ x ∂μ, enorm (f x) < ε := by
    rw [ae_iff]
    simpa only [not_lt] using (le_antisymm hmeasure bot_le)
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_enorm_bound (hAE.mono fun _ hx => le_of_lt hx)

/--
Affine hypercontractive estimates for two probability laws are preserved by summing
independent random variables.

This law-level tensorization step follows [OD14, Proposition 9.15 (proof)].
It extends the source's finite-exponent argument to allow infinite exponents;
the extended-valued norms require no additional moment assumptions.

**Proof sketch.** For finite `q`, apply `affine_sum_le_of_ne_top`. For infinite
`q` and finite `p`, monotonicity gives the assumed contractions at every sufficiently
large natural exponent. Apply the finite-exponent product estimate at each such
exponent, then use `eLpNorm_top_le_of_forall_nat`. When both exponents are infinite,
Fubini bounds almost every section of the input by its full essential supremum.
Contract the second variable, interchange the almost-everywhere quantifiers using
measurability of the joint affine bound, and contract the first variable. The resulting
almost-everywhere output bound controls its essential supremum.
-/
theorem affine_sum_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q) (ρ : ℝ)
    (hμ : ∀ a b : ℝ,
      eLpNorm (fun x : ℝ => a + ρ * b * x) q μ ≤
        eLpNorm (fun x : ℝ => a + b * x) p μ)
    (hν : ∀ a b : ℝ,
      eLpNorm (fun y : ℝ => a + ρ * b * y) q ν ≤
        eLpNorm (fun y : ℝ => a + b * y) p ν) :
    ∀ a b : ℝ,
      eLpNorm (fun z : ℝ × ℝ => a + ρ * b * (z.1 + z.2)) q (μ.prod ν) ≤
        eLpNorm (fun z : ℝ × ℝ => a + b * (z.1 + z.2)) p (μ.prod ν) := by
  by_cases hq : q = ∞
  · subst q
    by_cases hpt : p = ∞
    · subst p
      intro a b
      let C := eLpNorm (fun z : ℝ × ℝ => a + b * (z.1 + z.2)) ∞ (μ.prod ν)
      have affine_ae (θ : Measure ℝ)
          (hθ : ∀ c d : ℝ,
            eLpNorm (fun t : ℝ => c + ρ * d * t) ∞ θ ≤
              eLpNorm (fun t : ℝ => c + d * t) ∞ θ)
          (c d : ℝ) (hin : ∀ᵐ t ∂θ, ‖c + d * t‖ₑ ≤ C) :
          ∀ᵐ t ∂θ, ‖c + ρ * d * t‖ₑ ≤ C := by
        have hinorm : eLpNorm (fun t : ℝ => c + d * t) ∞ θ ≤ C := by
          rw [eLpNorm_exponent_top]
          exact eLpNormEssSup_le_of_ae_enorm_bound hin
        have hout : eLpNormEssSup (fun t : ℝ => c + ρ * d * t) θ ≤ C := by
          rw [← eLpNorm_exponent_top]
          exact (hθ c d).trans hinorm
        filter_upwards [enorm_ae_le_eLpNormEssSup
          (fun t : ℝ => c + ρ * d * t) θ] with t ht
        exact ht.trans hout
      have hinput :
          ∀ᵐ z ∂μ.prod ν, ‖a + b * (z.1 + z.2)‖ₑ ≤ C := by
        simpa only [C, eLpNorm_exponent_top] using
          enorm_ae_le_eLpNormEssSup
            (fun z : ℝ × ℝ => a + b * (z.1 + z.2)) (μ.prod ν)
      have hsections :
          ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ‖(a + b * x) + b * y‖ₑ ≤ C := by
        simpa only [mul_add, ← add_assoc] using
          Measure.ae_ae_of_ae_prod hinput
      have hmiddle :
          ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ‖a + ρ * b * y + b * x‖ₑ ≤ C := by
        filter_upwards [hsections] with x hx
        simpa only [add_assoc, add_left_comm, add_comm] using
          affine_ae ν hν (a + b * x) b hx
      have hmiddle_meas :
          MeasurableSet {z : ℝ × ℝ | ‖a + ρ * b * z.2 + b * z.1‖ₑ ≤ C} := by
        exact measurableSet_le
          ((by fun_prop :
            Measurable (fun z : ℝ × ℝ => a + ρ * b * z.2 + b * z.1)).enorm)
          measurable_const
      have hmiddle_rev :
          ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, ‖a + ρ * b * y + b * x‖ₑ ≤ C :=
        (Measure.ae_ae_comm hmiddle_meas).mp hmiddle
      have hfinal_rev :
          ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, ‖a + ρ * b * (x + y)‖ₑ ≤ C := by
        filter_upwards [hmiddle_rev] with y hy
        have hout := affine_ae μ hμ (a + ρ * b * y) b hy
        have hreassoc (x : ℝ) :
            (a + ρ * b * y) + ρ * b * x = a + ρ * b * (x + y) := by
          ring
        simpa only [hreassoc] using hout
      have hfinal_meas :
          MeasurableSet {z : ℝ × ℝ | ‖a + ρ * b * (z.1 + z.2)‖ₑ ≤ C} := by
        exact measurableSet_le
          ((by fun_prop :
            Measurable (fun z : ℝ × ℝ => a + ρ * b * (z.1 + z.2))).enorm)
          measurable_const
      have hfinal :
          ∀ᵐ z ∂μ.prod ν, ‖a + ρ * b * (z.1 + z.2)‖ₑ ≤ C :=
        (Measure.ae_prod_iff_ae_ae hfinal_meas).mpr
          ((Measure.ae_ae_comm hfinal_meas).mpr hfinal_rev)
      change eLpNorm (fun z : ℝ × ℝ => a + ρ * b * (z.1 + z.2)) ∞
        (μ.prod ν) ≤ C
      rw [eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_enorm_bound hfinal
    · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hpt
      intro a b
      apply eLpNorm_top_le_of_forall_nat
        ((by fun_prop :
          Measurable (fun z : ℝ × ℝ => a + ρ * b * (z.1 + z.2))).aestronglyMeasurable)
        (N := N)
      intro n hn
      have hpn : p ≤ (n : ℝ≥0∞) := hN.le.trans (by exact_mod_cast hn)
      refine affine_sum_le_of_ne_top μ ν hp hpn (by simp) ρ ?_ ?_ a b
      · intro c d
        calc
          eLpNorm (fun x : ℝ => c + ρ * d * x) (n : ℝ≥0∞) μ ≤
              eLpNorm (fun x : ℝ => c + ρ * d * x) ∞ μ :=
            eLpNorm_le_eLpNorm_of_exponent_le le_top
              ((by fun_prop :
                Measurable (fun x : ℝ => c + ρ * d * x)).aestronglyMeasurable)
          _ ≤ eLpNorm (fun x : ℝ => c + d * x) p μ := hμ c d
      · intro c d
        calc
          eLpNorm (fun y : ℝ => c + ρ * d * y) (n : ℝ≥0∞) ν ≤
              eLpNorm (fun y : ℝ => c + ρ * d * y) ∞ ν :=
            eLpNorm_le_eLpNorm_of_exponent_le le_top
              ((by fun_prop :
                Measurable (fun y : ℝ => c + ρ * d * y)).aestronglyMeasurable)
          _ ≤ eLpNorm (fun y : ℝ => c + d * y) p ν := hν c d
  · exact affine_sum_le_of_ne_top μ ν hp hpq hq ρ hμ hν

end Tensorization

end BooleanAnalysis.Hypercontractivity
