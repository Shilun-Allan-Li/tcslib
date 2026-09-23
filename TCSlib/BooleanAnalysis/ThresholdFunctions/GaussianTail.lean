import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian tail estimates and the isoperimetric profile near zero

This file develops the one-dimensional Gaussian analysis needed for
[OD14, Prop. 5.27]: the Mills-ratio bounds for the lower tail of the standard
Gaussian, the basic properties of the standard Gaussian cdf and its quantile
function, and the resulting asymptotics

`φ (Φ⁻¹ α) ∼ α * sqrt (2 * log (1 / α))`  as `α → 0⁺`.

## Main results

* `gaussTail_le`, `le_gaussTail`: the Mills-ratio bounds
  `(1 - 1/t²) * φ(t)/|t| ≤ Φ(t) ≤ φ(t)/|t|` for `t < 0`.
* `standardGaussianCDF_quantile`: `Φ (Φ⁻¹ α) = α` for `α ∈ (0,1)`.
* `gaussianIsoperimetric_equiv_at_zero`: the asymptotic equivalence above.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
  Chapter 5.
-/

open MeasureTheory ProbabilityTheory Filter

namespace BooleanAnalysis
namespace ThresholdFunctions

/-! ## Standard Gaussian notation -/

/-- The standard Gaussian probability measure `N(0,1)`.

[OD14, Notation 5.14] -/
noncomputable def standardGaussianMeasure : Measure ℝ :=
  gaussianReal 0 1

/-- The standard Gaussian probability density `φ`.

[OD14, Notation 5.14] -/
noncomputable def standardGaussianPDF : ℝ → ℝ :=
  gaussianPDFReal 0 1

/-- The standard Gaussian cumulative distribution function `Φ`.

[OD14, Notation 5.14] -/
noncomputable def standardGaussianCDF (t : ℝ) : ℝ :=
  cdf standardGaussianMeasure t

/-- The complementary standard Gaussian cdf `Φ̄(t) = 1 - Φ(t)`.

[OD14, Notation 5.14] -/
noncomputable def standardGaussianTail (t : ℝ) : ℝ :=
  1 - standardGaussianCDF t

/-- The lower quantile of the standard Gaussian distribution. This is a total real-valued
extension of the quantile used by O'Donnell on probabilities in `(0, 1)`.

[OD14, §5.4, Def. 5.26] -/
noncomputable def standardGaussianQuantile (α : ℝ) : ℝ :=
  sInf {t : ℝ | α ≤ standardGaussianCDF t}

/-- The Gaussian isoperimetric function `U = φ ∘ Φ⁻¹`. This is a total real-valued extension of
O'Donnell's function on `[0, 1]`; the Chapter 5 results below use it near zero from within `(0, 1)`.

[OD14, Def. 5.26] -/
noncomputable def gaussianIsoperimetric (α : ℝ) : ℝ :=
  standardGaussianPDF (standardGaussianQuantile α)

lemma continuous_standardGaussianPDF : Continuous standardGaussianPDF := by
  unfold standardGaussianPDF
  rw [gaussianPDFReal_def]
  fun_prop

lemma hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt standardGaussianPDF (-x * standardGaussianPDF x) x := by
  have hpdf : standardGaussianPDF =
      fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    funext y
    simp [standardGaussianPDF, gaussianPDFReal_def]
  rw [hpdf]
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have h := (hasDerivAt_pow 2 x).neg.div_const 2
    convert h using 1; push_cast; ring
  have h3 := ((Real.hasDerivAt_exp (-x ^ 2 / 2)).comp x h1).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert h3 using 1
  ring

lemma tendsto_sq_atBot : Tendsto (fun x : ℝ => x ^ 2) atBot atTop := by
  have habs : Tendsto (fun x : ℝ => |x|) atBot atTop := tendsto_abs_atBot_atTop
  refine (habs.atTop_mul_atTop₀ habs).congr fun x => ?_
  rw [abs_mul_abs_self]; ring

lemma tendsto_standardGaussianPDF_atBot : Tendsto standardGaussianPDF atBot (nhds 0) := by
  have hpdf : standardGaussianPDF =
      fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    funext x
    simp [standardGaussianPDF, gaussianPDFReal_def]
  rw [hpdf]
  have h : Tendsto (fun x : ℝ => -x ^ 2 / 2) atBot atBot :=
    Filter.Tendsto.atBot_div_const (by norm_num) (tendsto_neg_atTop_atBot.comp tendsto_sq_atBot)
  have h2 := (Real.tendsto_exp_atBot.comp h).const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  rw [mul_zero] at h2
  exact h2

lemma log_standardGaussianPDF (x : ℝ) :
    Real.log (standardGaussianPDF x) = -Real.log (Real.sqrt (2 * Real.pi)) - x ^ 2 / 2 := by
  rw [show standardGaussianPDF x =
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) by
      simp [standardGaussianPDF, gaussianPDFReal_def]]
  have h : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  rw [Real.log_mul (inv_ne_zero h) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  ring

/-! ## The cdf -/

lemma standardGaussianCDF_sub (a b : ℝ) :
    standardGaussianCDF b - standardGaussianCDF a =
      ∫ x in a..b, standardGaussianPDF x := by
  have hCDF_integral (t : ℝ) :
      standardGaussianCDF t = ∫ x in Set.Iic t, standardGaussianPDF x := by
    unfold standardGaussianCDF standardGaussianMeasure standardGaussianPDF
    rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal]
    exact integral_nonneg fun x ↦ gaussianPDFReal_nonneg 0 1 x
  rw [hCDF_integral, hCDF_integral]
  exact intervalIntegral.integral_Iic_sub_Iic
    (integrable_gaussianPDFReal 0 1).integrableOn
    (integrable_gaussianPDFReal 0 1).integrableOn

lemma hasDerivAt_standardGaussianCDF (t : ℝ) :
    HasDerivAt standardGaussianCDF (standardGaussianPDF t) t := by
  have h : HasDerivAt (fun b => ∫ x in (0 : ℝ)..b, standardGaussianPDF x)
      (standardGaussianPDF t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (integrable_gaussianPDFReal 0 1).intervalIntegrable
      (continuous_standardGaussianPDF.stronglyMeasurableAtFilter _ _)
      continuous_standardGaussianPDF.continuousAt
  have he : standardGaussianCDF =
      fun b => standardGaussianCDF 0 + ∫ x in (0 : ℝ)..b, standardGaussianPDF x := by
    funext b
    rw [← standardGaussianCDF_sub]
    ring
  rw [he]
  simpa using h.const_add (standardGaussianCDF 0)

lemma continuous_standardGaussianCDF : Continuous standardGaussianCDF :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_standardGaussianCDF t).continuousAt

lemma standardGaussianCDF_strictMono : StrictMono standardGaussianCDF :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_standardGaussianCDF x).deriv]
    exact gaussianPDFReal_pos 0 1 x one_ne_zero

lemma standardGaussianCDF_pos (t : ℝ) : 0 < standardGaussianCDF t :=
  lt_of_le_of_lt (by
    simpa [standardGaussianCDF] using cdf_nonneg standardGaussianMeasure (t - 1))
    (standardGaussianCDF_strictMono (by linarith))

lemma standardGaussianCDF_lt_one (t : ℝ) : standardGaussianCDF t < 1 :=
  lt_of_lt_of_le (standardGaussianCDF_strictMono (show t < t + 1 by linarith)) (by
    simpa [standardGaussianCDF] using cdf_le_one standardGaussianMeasure (t + 1))

/-! ## The quantile function -/

lemma exists_standardGaussianCDF_eq {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ∃ t : ℝ, standardGaussianCDF t = α := by
  have hbot : Tendsto standardGaussianCDF atBot (nhds 0) := by
    simpa [standardGaussianCDF] using tendsto_cdf_atBot standardGaussianMeasure
  have htop : Tendsto standardGaussianCDF atTop (nhds 1) := by
    simpa [standardGaussianCDF] using tendsto_cdf_atTop standardGaussianMeasure
  obtain ⟨a, ha⟩ := (hbot.eventually (eventually_lt_nhds h0)).exists
  obtain ⟨b, hb⟩ := (htop.eventually (eventually_gt_nhds h1)).exists
  have hab : a ≤ b := by
    by_contra hc
    exact absurd (standardGaussianCDF_strictMono (lt_of_not_ge hc)) (by push_neg; linarith)
  have hsub := intermediate_value_Icc hab continuous_standardGaussianCDF.continuousOn
  obtain ⟨t, _, ht⟩ := hsub ⟨le_of_lt ha, le_of_lt hb⟩
  exact ⟨t, ht⟩

lemma standardGaussianQuantile_eq {α t : ℝ} (ht : standardGaussianCDF t = α) :
    standardGaussianQuantile α = t := by
  have hset : {s : ℝ | α ≤ standardGaussianCDF s} = Set.Ici t := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_Ici, ← ht]
    exact ⟨fun h => standardGaussianCDF_strictMono.le_iff_le.1 h,
      fun h => standardGaussianCDF_strictMono.monotone h⟩
  rw [standardGaussianQuantile, hset, csInf_Ici]

lemma standardGaussianCDF_quantile {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    standardGaussianCDF (standardGaussianQuantile α) = α := by
  obtain ⟨t, ht⟩ := exists_standardGaussianCDF_eq h0 h1
  rw [standardGaussianQuantile_eq ht, ht]

/-! ## Mills-ratio bounds -/

lemma integrable_id_mul_standardGaussianPDF :
    Integrable (fun x : ℝ => x * standardGaussianPDF x) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [standardGaussianPDF, gaussianPDFReal_def]
  ring_nf

lemma integral_Iic_id_mul_standardGaussianPDF (t : ℝ) :
    ∫ x in Set.Iic t, x * standardGaussianPDF x = -standardGaussianPDF t := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto
    (f := fun x => -standardGaussianPDF x)
    (f' := fun x => x * standardGaussianPDF x) (a := t) (m := 0)
    continuous_standardGaussianPDF.neg.continuousWithinAt
    (fun x _ => by simpa using (hasDerivAt_standardGaussianPDF x).neg)
    integrable_id_mul_standardGaussianPDF.integrableOn
    (by simpa using tendsto_standardGaussianPDF_atBot.neg)
  simpa using h

/-- The upper Mills bound: `Φ(t) ≤ φ(t)/|t|` for `t < 0`. -/
lemma standardGaussianCDF_le_mills {t : ℝ} (ht : t < 0) :
    standardGaussianCDF t ≤ standardGaussianPDF t / (-t) := by
  have key : (∫ x in Set.Iic t, standardGaussianPDF x) ≤
      ∫ x in Set.Iic t, t⁻¹ * (x * standardGaussianPDF x) := by
    refine setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_id_mul_standardGaussianPDF.const_mul t⁻¹).integrableOn measurableSet_Iic ?_
    intro x hx
    have hxt : x ≤ t := hx
    have h1 : 1 ≤ x / t := by rw [le_div_iff_of_neg ht]; linarith
    calc standardGaussianPDF x = 1 * standardGaussianPDF x := (one_mul _).symm
      _ ≤ x / t * standardGaussianPDF x := mul_le_mul_of_nonneg_right h1 (by
        simpa [standardGaussianPDF] using (gaussianPDFReal_pos 0 1 x one_ne_zero).le)
      _ = t⁻¹ * (x * standardGaussianPDF x) := by field_simp
  have hCDF_integral :
      standardGaussianCDF t = ∫ x in Set.Iic t, standardGaussianPDF x := by
    unfold standardGaussianCDF standardGaussianMeasure standardGaussianPDF
    rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal]
    exact integral_nonneg fun x ↦ gaussianPDFReal_nonneg 0 1 x
  rw [integral_const_mul, integral_Iic_id_mul_standardGaussianPDF, ← hCDF_integral] at key
  refine key.trans (le_of_eq ?_)
  field_simp

/-- The antiderivative used for the lower Mills bound. -/
noncomputable def millsF (x : ℝ) : ℝ := standardGaussianPDF x * ((x ^ 3)⁻¹ - x⁻¹)

/-- The derivative of `millsF`. -/
noncomputable def millsF' (x : ℝ) : ℝ := standardGaussianPDF x * (1 - 3 * (x ^ 4)⁻¹)

lemma hasDerivAt_millsF {x : ℝ} (hx : x ≠ 0) : HasDerivAt millsF (millsF' x) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((y ^ 3)⁻¹ : ℝ)) (-(3 * x ^ 2) / (x ^ 3) ^ 2) x :=
    ((hasDerivAt_pow 3 x).inv (pow_ne_zero 3 hx)).congr_deriv (by push_cast; ring)
  have h2 : HasDerivAt (fun y : ℝ => (y⁻¹ : ℝ)) (-(1 : ℝ) / x ^ 2) x := by
    simpa using (hasDerivAt_id x).inv hx
  refine ((hasDerivAt_standardGaussianPDF x).mul (h1.sub h2)).congr_deriv ?_
  simp only [millsF', Pi.sub_apply]
  field_simp
  ring

lemma measurable_millsF' : Measurable millsF' := by
  unfold millsF'
  exact continuous_standardGaussianPDF.measurable.mul (by fun_prop)

lemma integrableOn_millsF' {t : ℝ} (ht : t < 0) : IntegrableOn millsF' (Set.Iic t) := by
  have htne : t ≠ 0 := ne_of_lt ht
  refine Integrable.mono'
    (((integrable_gaussianPDFReal 0 1).const_mul (1 + 3 * (t ^ 4)⁻¹)).integrableOn)
    measurable_millsF'.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  have hxt : x ≤ t := hx
  have hx0 : x < 0 := lt_of_le_of_lt hxt ht
  have hxne : x ≠ 0 := ne_of_lt hx0
  have h2 : t ^ 2 ≤ x ^ 2 := by nlinarith
  have hx4 : t ^ 4 ≤ x ^ 4 := by nlinarith [sq_nonneg t, sq_nonneg x]
  have ht4 : (0 : ℝ) < t ^ 4 := by positivity
  have hxx4 : (0 : ℝ) < x ^ 4 := by positivity
  have hinv : (x ^ 4)⁻¹ ≤ (t ^ 4)⁻¹ := inv_anti₀ ht4 hx4
  have h1 : |1 - 3 * (x ^ 4)⁻¹| ≤ 1 + 3 * (t ^ 4)⁻¹ := by
    rw [abs_le]
    exact ⟨by nlinarith [inv_pos.mpr hxx4, inv_pos.mpr ht4], by nlinarith [inv_pos.mpr hxx4]⟩
  have hxpdf : 0 < standardGaussianPDF x := by
    simpa [standardGaussianPDF] using gaussianPDFReal_pos 0 1 x one_ne_zero
  calc ‖millsF' x‖ = standardGaussianPDF x * |1 - 3 * (x ^ 4)⁻¹| := by
        simp [millsF', abs_of_pos hxpdf]
    _ ≤ standardGaussianPDF x * (1 + 3 * (t ^ 4)⁻¹) :=
      mul_le_mul_of_nonneg_left h1 hxpdf.le
    _ = (1 + 3 * (t ^ 4)⁻¹) * standardGaussianPDF x := by ring

lemma tendsto_cube_atBot : Tendsto (fun x : ℝ => x ^ 3) atBot atBot := by
  refine tendsto_atBot_mono' atBot ?_ tendsto_id
  filter_upwards [eventually_le_atBot (-1 : ℝ)] with x hx
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have h : x * (x ^ 2 - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp only [id]
  nlinarith

lemma tendsto_millsF_atBot : Tendsto millsF atBot (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => ((x ^ 3)⁻¹ : ℝ)) atBot (nhds 0) :=
    tendsto_inv_atBot_zero.comp tendsto_cube_atBot
  have h := tendsto_standardGaussianPDF_atBot.mul (h1.sub tendsto_inv_atBot_zero)
  simpa [millsF] using h

lemma continuousAt_millsF {t : ℝ} (ht : t ≠ 0) : ContinuousAt millsF t := by
  have h1 : ContinuousAt (fun y : ℝ => ((y ^ 3)⁻¹ : ℝ)) t :=
    ((continuous_pow 3).continuousAt).inv₀ (pow_ne_zero 3 ht)
  have h2 : ContinuousAt (fun y : ℝ => (y⁻¹ : ℝ)) t := continuousAt_inv₀ ht
  exact (continuous_standardGaussianPDF.continuousAt).mul (h1.sub h2)

/-- The lower Mills bound: `(1 - 1/t²) * φ(t)/|t| ≤ Φ(t)` for `t < 0`, in the form
`φ(t) * (1/t³ - 1/t) ≤ Φ(t)`. -/
lemma mills_le_standardGaussianCDF {t : ℝ} (ht : t < 0) : millsF t ≤ standardGaussianCDF t := by
  have hint : ∫ x in Set.Iic t, millsF' x = millsF t := by
    have h := integral_Iic_of_hasDerivAt_of_tendsto (f := millsF) (f' := millsF')
      (a := t) (m := 0) (continuousAt_millsF (ne_of_lt ht)).continuousWithinAt
      (fun x hx => hasDerivAt_millsF (ne_of_lt (lt_trans hx ht)))
      (integrableOn_millsF' ht) tendsto_millsF_atBot
    simpa using h
  have hmono : ∫ x in Set.Iic t, millsF' x ≤
      ∫ x in Set.Iic t, standardGaussianPDF x := by
    refine setIntegral_mono_on (integrableOn_millsF' ht)
      (integrable_gaussianPDFReal 0 1).integrableOn
      measurableSet_Iic ?_
    intro x hx
    have hx0 : x < 0 := lt_of_le_of_lt hx ht
    have hxne : x ≠ 0 := ne_of_lt hx0
    have h4 : (0 : ℝ) < x ^ 4 := by positivity
    have : (1 : ℝ) - 3 * (x ^ 4)⁻¹ ≤ 1 := by nlinarith [inv_pos.mpr h4]
    have hxpdf : 0 < standardGaussianPDF x := by
      simpa [standardGaussianPDF] using gaussianPDFReal_pos 0 1 x one_ne_zero
    calc millsF' x = standardGaussianPDF x * (1 - 3 * (x ^ 4)⁻¹) := rfl
      _ ≤ standardGaussianPDF x * 1 := mul_le_mul_of_nonneg_left this hxpdf.le
      _ = standardGaussianPDF x := mul_one _
  have hCDF_integral :
      standardGaussianCDF t = ∫ x in Set.Iic t, standardGaussianPDF x := by
    unfold standardGaussianCDF standardGaussianMeasure standardGaussianPDF
    rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal]
    exact integral_nonneg fun x ↦ gaussianPDFReal_nonneg 0 1 x
  rw [hint, ← hCDF_integral] at hmono
  exact hmono

/-! ## Asymptotics of the isoperimetric profile near zero -/

/-- The Mills ratio `Φ(t)·|t| / φ(t)`. -/
noncomputable def millsRatio (t : ℝ) : ℝ :=
  standardGaussianCDF t * (-t) / standardGaussianPDF t

lemma millsRatio_le_one {t : ℝ} (ht : t < 0) : millsRatio t ≤ 1 := by
  have hpdf : 0 < standardGaussianPDF t := by
    simpa [standardGaussianPDF] using gaussianPDFReal_pos 0 1 t one_ne_zero
  rw [millsRatio, div_le_one hpdf]
  have h := standardGaussianCDF_le_mills ht
  rw [le_div_iff₀ (by linarith)] at h
  exact h

lemma one_sub_le_millsRatio {t : ℝ} (ht : t < 0) : 1 - (t ^ 2)⁻¹ ≤ millsRatio t := by
  have htne : t ≠ 0 := ne_of_lt ht
  have hpdf : 0 < standardGaussianPDF t := by
    simpa [standardGaussianPDF] using gaussianPDFReal_pos 0 1 t one_ne_zero
  have h := mills_le_standardGaussianCDF ht
  rw [millsRatio, le_div_iff₀ hpdf]
  have hmul : (standardGaussianPDF t * ((t ^ 3)⁻¹ - t⁻¹)) * (-t) ≤
      standardGaussianCDF t * (-t) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  refine le_trans (le_of_eq ?_) hmul
  field_simp
  ring

lemma tendsto_inv_sq_atBot : Tendsto (fun t : ℝ => ((t ^ 2)⁻¹ : ℝ)) atBot (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_sq_atBot

lemma tendsto_millsRatio : Tendsto millsRatio atBot (nhds 1) := by
  have hlow : Tendsto (fun t : ℝ => 1 - (t ^ 2)⁻¹) atBot (nhds 1) := by
    simpa using tendsto_const_nhds.sub tendsto_inv_sq_atBot
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht using one_sub_le_millsRatio ht
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht using millsRatio_le_one ht

lemma millsRatio_pos {t : ℝ} (ht : t < 0) : 0 < millsRatio t :=
  div_pos (mul_pos (standardGaussianCDF_pos t) (by linarith)) (by
    simpa [standardGaussianPDF] using gaussianPDFReal_pos 0 1 t one_ne_zero)

/-- `2 log (1/Φ(t))`. -/
noncomputable def gLog (t : ℝ) : ℝ := 2 * Real.log (standardGaussianCDF t)⁻¹

lemma gLog_pos (t : ℝ) : 0 < gLog t := by
  have h1 : 1 < (standardGaussianCDF t)⁻¹ := by
    rw [one_lt_inv_iff₀]
    exact ⟨standardGaussianCDF_pos t, standardGaussianCDF_lt_one t⟩
  have h2 := Real.log_pos h1
  rw [gLog]
  linarith

lemma gLog_eq {t : ℝ} (ht : t < 0) :
    gLog t = (-2 * Real.log (millsRatio t) + 2 * Real.log (-t) +
      2 * Real.log (Real.sqrt (2 * Real.pi))) + t ^ 2 := by
  have h1 : Real.log (millsRatio t) =
      Real.log (standardGaussianCDF t) + Real.log (-t) -
        Real.log (standardGaussianPDF t) := by
    have hpdf : 0 < standardGaussianPDF t := by
      simpa [standardGaussianPDF] using gaussianPDFReal_pos 0 1 t one_ne_zero
    rw [millsRatio,
      Real.log_div (ne_of_gt (mul_pos (standardGaussianCDF_pos t) (by linarith)))
        (ne_of_gt hpdf),
      Real.log_mul (ne_of_gt (standardGaussianCDF_pos t)) (by linarith)]
  have h2 := log_standardGaussianPDF t
  have h3 : Real.log (standardGaussianCDF t)⁻¹ = -Real.log (standardGaussianCDF t) :=
    Real.log_inv _
  rw [gLog, h3, h1, h2]
  ring

lemma tendsto_log_neg_div_sq : Tendsto (fun t : ℝ => Real.log (-t) / t ^ 2) atBot (nhds 0) := by
  have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun u : ℝ => (u⁻¹ : ℝ)) atTop (nhds 0) := tendsto_inv_atTop_zero
  have h3 := h1.mul h2
  rw [mul_zero] at h3
  have h4 := h3.comp tendsto_neg_atBot_atTop
  refine h4.congr fun t => ?_
  simp only [Function.comp_apply]
  field_simp

lemma tendsto_gLog_div_sq : Tendsto (fun t : ℝ => gLog t / t ^ 2) atBot (nhds 1) := by
  have hA : Tendsto (fun t : ℝ => -2 * Real.log (millsRatio t) * (t ^ 2)⁻¹) atBot (nhds 0) := by
    have hlog : Tendsto (fun t : ℝ => Real.log (millsRatio t)) atBot (nhds 0) := by
      have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp tendsto_millsRatio
      simpa using h
    have h := (hlog.const_mul (-2 : ℝ)).mul tendsto_inv_sq_atBot
    simpa using h
  have hB : Tendsto (fun t : ℝ => 2 * Real.log (-t) * (t ^ 2)⁻¹) atBot (nhds 0) := by
    have h := tendsto_log_neg_div_sq.const_mul (2 : ℝ)
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    field_simp
  have hC : Tendsto (fun t : ℝ => 2 * Real.log (Real.sqrt (2 * Real.pi)) * (t ^ 2)⁻¹) atBot
      (nhds 0) := by
    have h := tendsto_inv_sq_atBot.const_mul (2 * Real.log (Real.sqrt (2 * Real.pi)))
    rw [mul_zero] at h
    exact h
  have hsum : Tendsto (fun t : ℝ =>
      (-2 * Real.log (millsRatio t) * (t ^ 2)⁻¹ + 2 * Real.log (-t) * (t ^ 2)⁻¹ +
        2 * Real.log (Real.sqrt (2 * Real.pi)) * (t ^ 2)⁻¹) + 1) atBot (nhds 1) := by
    simpa using ((hA.add hB).add hC).add_const (1 : ℝ)
  refine hsum.congr' ?_
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have htne : (t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_lt ht)
  rw [gLog_eq ht, add_div, div_self htne]
  ring

lemma tendsto_sqrt_gLog_div : Tendsto (fun t : ℝ => Real.sqrt (gLog t) / (-t)) atBot (nhds 1) := by
  have h : Tendsto (fun t : ℝ => Real.sqrt (gLog t / t ^ 2)) atBot (nhds 1) := by
    have := (Real.continuous_sqrt.continuousAt (x := (1 : ℝ))).tendsto.comp tendsto_gLog_div_sq
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  rw [Real.sqrt_div (gLog_pos t).le, Real.sqrt_sq_eq_abs, abs_of_neg ht]

/-- The key limit: `φ(t) / (Φ(t) · sqrt (2 log (1/Φ(t)))) → 1` as `t → -∞`. -/
theorem tendsto_standardGaussianPDF_div :
    Tendsto (fun t : ℝ => standardGaussianPDF t /
      (standardGaussianCDF t * Real.sqrt (gLog t))) atBot (nhds 1) := by
  have h1 : Tendsto (fun t : ℝ => (millsRatio t)⁻¹) atBot (nhds 1) := by
    simpa using tendsto_millsRatio.inv₀ (by norm_num)
  have h2 : Tendsto (fun t : ℝ => (Real.sqrt (gLog t) / (-t))⁻¹) atBot (nhds 1) := by
    simpa using tendsto_sqrt_gLog_div.inv₀ (by norm_num)
  have h := h1.mul h2
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  have h3 : Real.sqrt (gLog t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (gLog_pos t))
  have h4 : standardGaussianCDF t ≠ 0 := ne_of_gt (standardGaussianCDF_pos t)
  have h5 : standardGaussianPDF t ≠ 0 := ne_of_gt (by
    simpa [standardGaussianPDF] using gaussianPDFReal_pos 0 1 t one_ne_zero)
  have h6 : t ≠ 0 := ne_of_lt ht
  rw [millsRatio]
  field_simp

theorem tendsto_standardGaussianQuantile :
    Tendsto standardGaussianQuantile (nhdsWithin 0 (Set.Ioi 0)) atBot := by
  rw [tendsto_atBot]
  intro M
  have hc : (0 : ℝ) < min (standardGaussianCDF M) 1 :=
    lt_min (standardGaussianCDF_pos M) one_pos
  filter_upwards [Ioo_mem_nhdsGT_of_mem (Set.mem_Ico.2 ⟨le_refl (0 : ℝ), hc⟩)] with α hα
  obtain ⟨h0, h1⟩ := hα
  have hlt1 : α < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
  have hltM : α < standardGaussianCDF M := lt_of_lt_of_le h1 (min_le_left _ _)
  have : standardGaussianCDF (standardGaussianQuantile α) < standardGaussianCDF M := by
    rw [standardGaussianCDF_quantile h0 hlt1]
    exact hltM
  exact le_of_lt (standardGaussianCDF_strictMono.lt_iff_lt.1 this)

/-- Near zero, the Gaussian isoperimetric function is asymptotic to
`α * sqrt (2 * log (1 / α))`. [OD14, Prop. 5.27]

**Proof sketch.** Write `α = Φ(t)` with `t → -∞` and use the Gaussian tail equivalence
`Φ(t) ∼ φ(t)/|t|`. Taking logarithms gives `|t| ∼ sqrt (2 log (1/α))`; substituting this into
`U(α) = φ(t)` yields the result. -/
theorem gaussianIsoperimetric_equiv_at_zero :
    Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0)) gaussianIsoperimetric
      (fun α : ℝ => α * Real.sqrt (2 * Real.log α⁻¹)) := by
  have hv : ∀ᶠ α : ℝ in nhdsWithin 0 (Set.Ioi 0), α * Real.sqrt (2 * Real.log α⁻¹) ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT_of_mem (Set.mem_Ico.2 ⟨le_refl (0 : ℝ), one_pos⟩)] with α hα
    obtain ⟨h0, h1⟩ := hα
    have hlog : 0 < Real.log α⁻¹ := Real.log_pos (by rw [one_lt_inv_iff₀]; exact ⟨h0, h1⟩)
    have : 0 < Real.sqrt (2 * Real.log α⁻¹) := Real.sqrt_pos.2 (by linarith)
    positivity
  rw [Asymptotics.isEquivalent_iff_tendsto_one hv]
  have hcomp := tendsto_standardGaussianPDF_div.comp tendsto_standardGaussianQuantile
  refine hcomp.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT_of_mem (Set.mem_Ico.2 ⟨le_refl (0 : ℝ), one_pos⟩)] with α hα
  obtain ⟨h0, h1⟩ := hα
  have hq : standardGaussianCDF (standardGaussianQuantile α) = α :=
    standardGaussianCDF_quantile h0 h1
  simp only [gaussianIsoperimetric, Function.comp_apply, Pi.div_apply, gLog, hq]

end ThresholdFunctions
end BooleanAnalysis

#min_imports
