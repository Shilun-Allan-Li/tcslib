/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.OneBit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hypercontractivity of symmetric random variables

## Main definitions

The probability-space definitions are in `RandomVariablesBasic`.

## Main results

* `symmetric_hypercontractive_four_iff`: the exact second-to-fourth norm criterion.
* `symmetric_hypercontractive`: the general second-to-`q` norm bound.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §10.2, Proposition 10.12 and Theorem 10.13.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.Hypercontractivity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A symmetric variable of second norm one and fourth norm `C` is `(2,4,ρ)`-hypercontractive
exactly for `ρ ≤ min(1/√3,1/C)`, within `0 ≤ ρ < 1`. [OD14, Prop. 10.12]

**Proof sketch.** Expand fourth moments of affine perturbations. Symmetry removes the odd
terms; comparing the quadratic and quartic terms proves sufficiency. Small and large
perturbations give the two necessary bounds. -/
theorem symmetric_hypercontractive_four_iff (X : Ω → ℝ) (C ρ : ℝ)
    (hsym : IsSymmetricRV X μ) (hmem : MemLp X 4 μ)
    (hsecond : rvLpNorm X μ 2 = 1) (hC : rvLpNorm X μ 4 = C) (hCpos : 0 < C)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    IsHypercontractive X μ 2 4 ρ ↔ ρ ≤ min (1 / Real.sqrt 3) (1 / C) := (by
  change IdentDistrib X (fun ω => -X ω) μ μ at hsym
  let A (a b : ℝ) : Ω → ℝ := fun ω => a + b * X ω
  have hA (a b : ℝ) : MemLp (A a b) 4 μ :=
    (memLp_const a).add (hmem.const_mul b)
  have hpint (Y : Ω → ℝ) (n : ℕ) (hY : MemLp Y n μ) :
      Integrable (fun ω => Y ω ^ n) μ :=
    (integrable_norm_iff (hY.1.pow n)).mp
      (by simpa only [Pi.pow_apply, norm_pow] using hY.integrable_norm_pow')
  have hmom (Y : Ω → ℝ) (n : ℕ) (hn : n ≠ 0) (he : Even n)
      (hY : MemLp Y n μ) :
      rvLpNorm Y μ n ^ n = ∫ ω, Y ω ^ n ∂μ := by
    have hp := congrArg ENNReal.toReal
      (eLpNorm_nnreal_pow_eq_lintegral (f := Y) (μ := μ) (p := (n : NNReal))
        (by exact_mod_cast hn))
    simp only [NNReal.coe_natCast, ENNReal.coe_natCast] at hp
    simp_rw [← ENNReal.toReal_rpow, Real.rpow_natCast,
      ← ofReal_norm_eq_enorm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (Nat.cast_nonneg _),
      Real.rpow_natCast, Real.norm_eq_abs, he.pow_abs] at hp
    rw [← integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => he.pow_nonneg (Y ω)) (hY.1.pow n)] at hp
    simpa [rvLpNorm] using hp
  have hmem2 : MemLp X 2 μ := hmem.mono_exponent (by norm_num)
  have hX2 := hmem2.integrable_sq
  have hX4 := hpint X 4 hmem
  have h2 : ∫ ω, X ω ^ 2 ∂μ = 1 := by
    simpa [hsecond] using (hmom X 2 (by norm_num) (by norm_num) hmem2).symm
  have h4 : ∫ ω, X ω ^ 4 ∂μ = C ^ 4 := by
    simpa [hC] using (hmom X 4 (by norm_num) (by norm_num) hmem).symm
  have hsymint (a b : ℝ) (n : ℕ) :
      (∫ ω, A a b ω ^ n ∂μ) = ∫ ω, A a (-b) ω ^ n ∂μ := by
    simpa [A, Function.comp_def, mul_neg, neg_mul] using
      ((hsym.comp (show Measurable (fun x : ℝ => a + b * x) from
        measurable_const.add (measurable_const.mul measurable_id))).pow (n := n)).integral_eq
  have hform2 (a b : ℝ) : rvLpNorm (A a b) μ 2 ^ 2 = a ^ 2 + b ^ 2 := by
    have hm := hmom (A a b) 2 (by norm_num) (by norm_num)
      ((hA a b).mono_exponent (by norm_num))
    norm_num only [Nat.cast_ofNat] at hm
    rw [hm]
    have havg :
        (∫ ω, A a b ω ^ 2 ∂μ) + (∫ ω, A a (-b) ω ^ 2 ∂μ) =
          2 * (a ^ 2 + b ^ 2) := by
      calc
        _ = ∫ ω, A a b ω ^ 2 + A a (-b) ω ^ 2 ∂μ :=
          (integral_add
            (hpint _ 2 ((hA a b).mono_exponent (by norm_num)))
            (hpint _ 2 ((hA a (-b)).mono_exponent (by norm_num)))).symm
        _ = ∫ ω, 2 * a ^ 2 + 2 * b ^ 2 * X ω ^ 2 ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by dsimp [A]; ring)
        _ = 2 * (a ^ 2 + b ^ 2) := by
          rw [integral_add (integrable_const _) (hX2.const_mul _)]
          simp [integral_const_mul, h2] <;> ring
    rw [← hsymint a b 2] at havg
    linarith
  have hform4 (a b : ℝ) :
      rvLpNorm (A a b) μ 4 ^ 4 = a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4 * C ^ 4 := by
    have hm := hmom (A a b) 4 (by norm_num) (by norm_num) (hA a b)
    norm_num only [Nat.cast_ofNat] at hm
    rw [hm]
    have havg :
        (∫ ω, A a b ω ^ 4 ∂μ) + (∫ ω, A a (-b) ω ^ 4 ∂μ) =
          2 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4 * C ^ 4) := by
      calc
        _ = ∫ ω, A a b ω ^ 4 + A a (-b) ω ^ 4 ∂μ :=
          (integral_add (hpint _ 4 (hA a b)) (hpint _ 4 (hA a (-b)))).symm
        _ = ∫ ω, 2 * a ^ 4 + 12 * a ^ 2 * b ^ 2 * X ω ^ 2 +
            2 * b ^ 4 * X ω ^ 4 ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by dsimp [A]; ring)
        _ = 2 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4 * C ^ 4) := by
          calc
            (∫ ω, 2 * a ^ 4 + 12 * a ^ 2 * b ^ 2 * X ω ^ 2 +
                2 * b ^ 4 * X ω ^ 4 ∂μ) =
                (∫ ω, 2 * a ^ 4 + 12 * a ^ 2 * b ^ 2 * X ω ^ 2 ∂μ) +
                  (∫ ω, 2 * b ^ 4 * X ω ^ 4 ∂μ) := by
              simpa only [Pi.add_apply] using
                integral_add
                  ((integrable_const (2 * a ^ 4)).add (hX2.const_mul (12 * a ^ 2 * b ^ 2)))
                  (hX4.const_mul (2 * b ^ 4))
            _ = ((∫ ω, 2 * a ^ 4 ∂μ) +
                  (∫ ω, 12 * a ^ 2 * b ^ 2 * X ω ^ 2 ∂μ)) +
                  (∫ ω, 2 * b ^ 4 * X ω ^ 4 ∂μ) := by
              simpa only [Pi.add_apply] using
                congrArg (fun t : ℝ => t + ∫ ω, 2 * b ^ 4 * X ω ^ 4 ∂μ)
                  (integral_add (integrable_const (2 * a ^ 4))
                    (hX2.const_mul (12 * a ^ 2 * b ^ 2)))
            _ = 2 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4 * C ^ 4) := by
              simp [integral_const_mul, h2, h4] <;> ring
    rw [← hsymint a b 4] at havg
    linarith
  have hnormiff (a b : ℝ) :
      eLpNorm (A a (ρ * b)) 4 μ ≤ eLpNorm (A a b) 2 μ ↔
        a ^ 4 + 6 * a ^ 2 * ρ ^ 2 * b ^ 2 + ρ ^ 4 * b ^ 4 * C ^ 4 ≤
          (a ^ 2 + b ^ 2) ^ 2 := by
    rw [← ENNReal.toReal_le_toReal (hA a (ρ * b)).2.ne
      ((hA a b).mono_exponent (by norm_num) : MemLp (A a b) 2 μ).2.ne,
      ← pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        (by norm_num : (4 : ℕ) ≠ 0)]
    have hp2 := hform2 a b
    have hp4 := hform4 a (ρ * b)
    simp only [rvLpNorm, ENNReal.ofReal_ofNat] at hp2 hp4
    have hp2four : (eLpNorm (A a b) 2 μ).toReal ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by
      calc
        _ = ((eLpNorm (A a b) 2 μ).toReal ^ 2) ^ 2 := by ring
        _ = (a ^ 2 + b ^ 2) ^ 2 := by rw [hp2]
    rw [hp4, hp2four]
    constructor <;> intro h <;> nlinarith [h]
  constructor
  · intro h
    have hp (a b : ℝ) := (hnormiff a b).1 (h.2.2.2.2.2 a b)
    have hquartic : (ρ * C) ^ 4 ≤ 1 := by
      simpa [mul_pow] using hp 0 1
    have hCbound : ρ ≤ 1 / C := by
      apply (le_div_iff₀ hCpos).2
      exact (pow_le_pow_iff_left₀ (mul_nonneg hρ0 hCpos.le) zero_le_one
        (by norm_num : (4 : ℕ) ≠ 0)).1 (by simpa using hquartic)
    have hsquare : 6 * ρ ^ 2 ≤ 2 := by
      by_contra hn
      let d := 6 * ρ ^ 2 - 2
      have hd : 0 < d := by dsimp [d]; linarith
      let a := 1 / d + 1
      have ha : 1 ≤ a := by
        dsimp [a]
        have : 0 ≤ 1 / d := by positivity
        linarith
      have hda : d * a = 1 + d := by
        dsimp [a]
        field_simp [hd.ne'] <;> ring
      have hmul : 0 ≤ d * (a ^ 2 - a) := mul_nonneg hd.le (by nlinarith)
      have hi := hp a 1
      dsimp [d] at hd hda hmul
      nlinarith [mul_nonneg (pow_nonneg hρ0 4) (pow_nonneg hCpos.le 4)]
    refine le_min ?_ hCbound
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).2
    have hprod : (ρ * Real.sqrt 3) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      nlinarith
    nlinarith [mul_nonneg hρ0 (Real.sqrt_nonneg 3)]
  · intro hr
    have hsquare : 6 * ρ ^ 2 ≤ 2 := by
      have hs : ρ * Real.sqrt 3 ≤ 1 :=
        (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).1 (le_min_iff.mp hr).1
      have hs2 := pow_le_pow_left₀ (mul_nonneg hρ0 (Real.sqrt_nonneg 3)) hs 2
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hs2
      nlinarith
    have hquartic : ρ ^ 4 * C ^ 4 ≤ 1 := by
      have hc : ρ * C ≤ 1 := (le_div_iff₀ hCpos).1 (le_min_iff.mp hr).2
      simpa [mul_pow] using pow_le_pow_left₀ (mul_nonneg hρ0 hCpos.le) hc 4
    refine ⟨by norm_num, by norm_num, hρ0, hρ1, hmem, ?_⟩
    intro a b
    apply (hnormiff a b).2
    have hmix := mul_le_mul_of_nonneg_right hsquare
      (by positivity : 0 ≤ a ^ 2 * b ^ 2)
    have hfour := mul_le_mul_of_nonneg_right hquartic (by positivity : 0 ≤ b ^ 4)
    nlinarith
)

/-- A symmetric variable of second norm one and finite `q`-norm `C` is hypercontractive
at radius `1/(C√(q-1))` for `q>2`. [OD14, Thm. 10.13]

**Proof sketch.** Average the moments of the two affine perturbations using symmetry.
Apply the existing one-bit inequality pointwise, then the triangle inequality in `L^(q/2)`
to the constant square plus the random square. The second-moment identity supplies the
input norm, and substituting the radius cancels the coefficient of the random square. -/
theorem symmetric_hypercontractive (X : Ω → ℝ) (q C : ℝ) (hq : 2 < q)
    (hsym : IsSymmetricRV X μ) (hmem : MemLp X (ENNReal.ofReal q) μ)
    (hsecond : rvLpNorm X μ 2 = 1) (hC : rvLpNorm X μ q = C) (hCpos : 0 < C) :
    IsHypercontractive X μ 2 (ENNReal.ofReal q) (1 / (C * Real.sqrt (q - 1))) := (by
  classical
  change IdentDistrib X (fun ω => -X ω) μ μ at hsym
  have hq0 : 0 < q := by linarith
  have hqh : 0 < q / 2 := by linarith
  have hQ2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq.le
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (q / 2) := by
    simpa using ENNReal.ofReal_le_ofReal
      (show (1 : ℝ) ≤ q / 2 by linarith)
  let s := Real.sqrt (q - 1)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = q - 1 := Real.sq_sqrt (by linarith)
  let A (a b : ℝ) : Ω → ℝ := fun ω => a + b * X ω
  have hA (a b : ℝ) : MemLp (A a b) (ENNReal.ofReal q) μ :=
    (memLp_const a).add (hmem.const_mul b)
  have hmem2 : MemLp X 2 μ := hmem.mono_exponent hQ2
  have hA2 (a b : ℝ) : MemLp (A a b) 2 μ :=
    (hA a b).mono_exponent hQ2
  have hmean : (∫ ω, X ω ∂μ) = 0 := by
    have hi := hsym.integral_eq
    rw [integral_neg] at hi
    linarith
  have hC1 : 1 ≤ C := by
    have hi : rvLpNorm X μ 2 ≤ rvLpNorm X μ q := by
      simpa [rvLpNorm] using
        ENNReal.toReal_mono hmem.2.ne
          (eLpNorm_le_eLpNorm_of_exponent_le hQ2 hmem.1)
    simpa only [hsecond, hC] using hi
  
  have hsymmoment (a t : ℝ) :
      (∫ ω, |A a t ω| ^ q ∂μ) =
        ∫ ω, |A a (-t) ω| ^ q ∂μ := by
    simpa only [A, Function.comp_def, mul_neg, neg_mul, Real.norm_eq_abs] using
      (((hsym.comp
        (show Measurable (fun x : ℝ => a + t * x) from by fun_prop)).norm).comp
        (show Measurable (fun x : ℝ => x ^ q) from by fun_prop)).integral_eq
  have hAi (a t : ℝ) : Integrable (fun ω => |A a t ω| ^ q) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq0.le] using
      (hA a t).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top
  have hXsq : MemLp (fun ω => X ω ^ 2) (ENNReal.ofReal (q / 2)) μ := by
    simpa [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ)),
      Real.rpow_two, Real.norm_eq_abs, sq_abs] using hmem.norm_rpow_div 2
  have hPQ :
      ENNReal.ofReal (q / 2) * ENNReal.ofReal 2 = ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_mul hqh.le]
    congr 1
    ring
  have hpow :
      eLpNorm (fun ω => X ω ^ 2) (ENNReal.ofReal (q / 2)) μ =
        eLpNorm X (ENNReal.ofReal q) μ ^ (2 : ℝ) := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, hPQ] using
      eLpNorm_norm_rpow (p := ENNReal.ofReal (q / 2)) (μ := μ)
        X (by norm_num : 0 < (2 : ℝ))
  
  -- Symmetry averages the two affine moments; Minkowski controls the quadratic bound.
  have hbound (a t : ℝ) :
      rvLpNorm (A a t) μ q ^ 2 ≤ a ^ 2 + (q - 1) * t ^ 2 * C ^ 2 := by
    let d := (q - 1) * t ^ 2
    let K : Ω → ℝ := fun ω => a ^ 2 + d * X ω ^ 2
    have hd : 0 ≤ d :=
      mul_nonneg (by linarith) (sq_nonneg t)
    have hKconst : MemLp (fun _ : Ω => a ^ 2) (ENNReal.ofReal (q / 2)) μ :=
      memLp_const _
    have hK : MemLp K (ENNReal.ofReal (q / 2)) μ :=
      hKconst.add (hXsq.const_mul d)
    have hKi : Integrable (fun ω => |K ω| ^ (q / 2)) μ := by
      simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hqh.le] using
        hK.integrable_norm_rpow
          (ENNReal.ofReal_pos.mpr hqh).ne' ENNReal.ofReal_ne_top
    have hmoment :
        rvLpNorm (A a t) μ q ^ q ≤ rvLpNorm K μ (q / 2) ^ (q / 2) := by
      rw [rvLpNorm_rpow _ _ _ hq0 (hA a t),
        rvLpNorm_rpow _ _ _ hqh hK]
      calc
        _ = ∫ ω, (|A a t ω| ^ q + |A a (-t) ω| ^ q) / 2 ∂μ := by
          rw [integral_div, integral_add (hAi a t) (hAi a (-t)),
            ← hsymmoment a t]
          ring
        _ ≤ _ := integral_mono
          ((hAi a t).add (hAi a (-t)) |>.div_const 2) hKi
          (fun ω => by
            change (|a + t * X ω| ^ q + |a + (-t) * X ω| ^ q) / 2 ≤
              |a ^ 2 + d * X ω ^ 2| ^ (q / 2)
            rw [neg_mul, ← sub_eq_add_neg,
              abs_of_nonneg
                (add_nonneg (sq_nonneg a) (mul_nonneg hd (sq_nonneg (X ω))))]
            simpa only [d, mul_pow, mul_assoc] using two_point_rpow_le q hq.le a (t * X ω))
    have hKn := eLpNorm_add_le hKconst.1 (hXsq.const_mul d).1 hP1
    have hKr := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hKconst.2.ne, (hXsq.const_mul d).2.ne⟩) hKn
    change rvLpNorm K μ (q / 2) ≤
      (eLpNorm (fun _ : Ω => a ^ 2) (ENNReal.ofReal (q / 2)) μ +
        eLpNorm (d • (fun ω => X ω ^ 2)) (ENNReal.ofReal (q / 2)) μ).toReal at hKr
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hqh).ne' (NeZero.ne μ),
      eLpNorm_const_smul, hpow] at hKr
    simp only [measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_eq_ofReal (sq_nonneg a), Real.enorm_eq_ofReal hd] at hKr
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hmem.2.ne)),
      ENNReal.toReal_ofReal (sq_nonneg a), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hd, ← ENNReal.toReal_rpow, Real.rpow_two] at hKr
    change rvLpNorm K μ (q / 2) ≤ a ^ 2 + d * rvLpNorm X μ q ^ 2 at hKr
    rw [hC] at hKr
    calc
      _ ≤ rvLpNorm K μ (q / 2) := by
        apply (Real.rpow_le_rpow_iff (sq_nonneg _) ENNReal.toReal_nonneg hqh).1
        rw [← Real.rpow_two,
          ← Real.rpow_mul (show 0 ≤ rvLpNorm (A a t) μ q from ENNReal.toReal_nonneg),
          show (2 : ℝ) * (q / 2) = q by ring]
        exact hmoment
      _ ≤ _ := hKr
  
  have hform2 (a b : ℝ) : rvLpNorm (A a b) μ 2 ^ 2 = a ^ 2 + b ^ 2 := by
    simpa [A, hsecond] using rvLpNorm_affine_sq X μ hmem2 hmean a b
  
  let ρ := 1 / (C * s)
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    apply (div_lt_one (mul_pos hCpos hs)).2
    have hs1 : 1 < s := by nlinarith [hs2]
    nlinarith [mul_le_mul_of_nonneg_right hC1 hs.le]
  have hρsq : (q - 1) * ρ ^ 2 * C ^ 2 = 1 := by
    dsimp [ρ]
    rw [div_pow, mul_pow, hs2]
    field_simp [hCpos.ne', show q - 1 ≠ 0 by linarith]
    <;> ring
  refine ⟨by norm_num, hQ2,
    by change 0 ≤ ρ; dsimp [ρ]; positivity,
    hρ1, hmem, ?_⟩
  intro a b
  rw [← ENNReal.toReal_le_toReal (hA a (ρ * b)).2.ne (hA2 a b).2.ne]
  apply (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (by norm_num : (2 : ℕ) ≠ 0)).1
  have hfinal :
      rvLpNorm (A a (ρ * b)) μ q ^ 2 ≤ rvLpNorm (A a b) μ 2 ^ 2 := by
    rw [hform2]
    calc
      _ ≤ a ^ 2 + (q - 1) * (ρ * b) ^ 2 * C ^ 2 := hbound a (ρ * b)
      _ = a ^ 2 + ((q - 1) * ρ ^ 2 * C ^ 2) * b ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [hρsq]; ring
  simpa only [rvLpNorm, ENNReal.ofReal_ofNat] using hfinal
)


end BooleanAnalysis.Hypercontractivity
