import Mathlib.Probability.Distributions.Gaussian.Real

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The two-dimensional standard Gaussian in polar coordinates

This file computes the measure of a planar cone under the two-dimensional standard Gaussian
distribution. It is the analytic core of Sheppard's formula for the quadrant probability of two
correlated standard Gaussians.

## Main definitions

* `gaussianDensity2`: the density `(2π)⁻¹ exp(-(x² + y²)/2)` of the standard Gaussian on `ℝ²`.

## Main results

* `gaussian_prod_apply`: the product of two standard Gaussian measures is the plane Lebesgue
  measure with density `gaussianDensity2`.
* `gaussian_cone_lintegral`: the Gaussian mass of a cone is `(2π)⁻¹` times the angular measure of
  the cone.
* `angular_measure_two_halfplanes`: the angular measure of the intersection of the two half-planes
  `cos θ ≤ 0` and `cos (θ - α) ≤ 0` is `π - α`.

## References

* [She99] W. F. Sheppard, On the application of the theory of error to cases of normal
  distribution and normal correlation, 1899.
* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, §5.2.
-/

open MeasureTheory ProbabilityTheory Filter Real

namespace BooleanAnalysis
namespace ThresholdFunctions

/-! ## The planar Gaussian density -/

/-- The density of the two-dimensional standard Gaussian with respect to Lebesgue measure. -/
noncomputable def gaussianDensity2 (z : ℝ × ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)

lemma gaussianPDF_mul (x y : ℝ) :
    gaussianPDF 0 1 x * gaussianPDF 0 1 y = ENNReal.ofReal (gaussianDensity2 (x, y)) := by
  have h1 : gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 y = gaussianDensity2 (x, y) := by
    unfold gaussianPDFReal gaussianDensity2
    push_cast
    field_simp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi), mul_assoc, ← Real.exp_add]
    have h : -((x - 0) ^ 2 / 2) + -((y - 0) ^ 2 / 2) = -((x ^ 2 + y ^ 2) / 2) := by ring
    rw [h]
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x), h1]

/-- The product of two standard Gaussian measures has density `gaussianDensity2` with respect to
the Lebesgue measure of the plane. -/
lemma gaussian_prod_apply {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) A
      = ∫⁻ z in A, ENNReal.ofReal (gaussianDensity2 z) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    MeasureTheory.prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    ← Measure.volume_eq_prod, withDensity_apply _ hA]
  refine setLIntegral_congr_fun hA ?_
  intro z _
  exact gaussianPDF_mul z.1 z.2

/-! ## The radial integral -/

lemma lintegral_radial :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * Real.exp (-r ^ 2 / 2)) = 1 := by
  have hint : IntegrableOn (fun r : ℝ ↦ r * Real.exp (-r ^ 2 / 2)) (Set.Ioi 0) := by
    have h := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn
      (s := Set.Ioi 0)
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    ring_nf
  have hintegral : ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2 / 2) = 1 := by
    rw [← RCLike.ofReal_inj (K := ℂ), ← integral_ofReal,
      ← RCLike.algebraMap_eq_ofReal, Complex.coe_algebraMap]
    change (∫ x in Set.Ioi (0 : ℝ), ((x * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ)) = (1 : ℂ)
    have h := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
    norm_num at h
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    push_cast
    congr 2
    ring
  have hnn : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ r * Real.exp (-r ^ 2 / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (le_of_lt hr) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hintegral]
  simp

/-! ## The Gaussian mass of a cone -/

/-- The Gaussian mass of a cone equals `(2π)⁻¹` times the measure of its set of angles. -/
lemma gaussian_cone_lintegral {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) {Θ : Set ℝ}
    (hΘ : MeasurableSet Θ)
    (hcone : ∀ r θ : ℝ, 0 < r → ((r * Real.cos θ, r * Real.sin θ) ∈ A ↔ θ ∈ Θ)) :
    ∫⁻ z in A, ENNReal.ofReal (gaussianDensity2 z)
      = ENNReal.ofReal ((2 * Real.pi)⁻¹) * volume (Θ ∩ Set.Ioo (-Real.pi) Real.pi) := by
  classical
  set F : ℝ → ENNReal := fun r ↦ ENNReal.ofReal (r * Real.exp (-r ^ 2 / 2)) with hF
  set G : ℝ → ENNReal := fun θ ↦ Θ.indicator (fun _ ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹)) θ with hG
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
  have hstep : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 •
          (A.indicator (fun z ↦ ENNReal.ofReal (gaussianDensity2 z)) (polarCoord.symm p))
        = F p.1 * G p.2 := by
    rintro ⟨r, θ⟩ hp
    rw [htarget] at hp
    obtain ⟨hr, -⟩ := hp
    simp only [Set.mem_Ioi] at hr
    rw [polarCoord_symm_apply]
    have hD : gaussianDensity2 (r * Real.cos θ, r * Real.sin θ)
        = (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2) := by
      unfold gaussianDensity2
      congr 2
      have hp2 : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      simp only []
      rw [hp2]
    by_cases hθ : θ ∈ Θ
    · rw [Set.indicator_of_mem ((hcone r θ hr).mpr hθ)]
      simp only [hF, hG, Set.indicator_of_mem hθ, hD, smul_eq_mul]
      rw [← ENNReal.ofReal_mul (le_of_lt hr), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    · rw [Set.indicator_of_notMem (fun hc ↦ hθ ((hcone r θ hr).mp hc))]
      simp only [hG, Set.indicator_of_notMem hθ, smul_zero, mul_zero]
  have hFm : AEMeasurable F (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Measurable.aemeasurable (by rw [hF]; exact ENNReal.measurable_ofReal.comp (by fun_prop))
  have hGm : AEMeasurable G (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    Measurable.aemeasurable (by rw [hG]; exact measurable_const.indicator hΘ)
  have hres : (volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)
      = (volume.restrict (Set.Ioi (0 : ℝ))).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [← lintegral_indicator hA, ← lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet hstep, htarget, hres,
    lintegral_prod_mul hFm hGm]
  simp only [hF, hG]
  rw [lintegral_radial, one_mul, lintegral_indicator hΘ, setLIntegral_const,
    Measure.restrict_apply hΘ]

/-! ## Angles at which the cosine is nonpositive -/

lemma cos_nonpos_iff_of_mem_Ioo {θ : ℝ} (h1 : -Real.pi < θ) (h2 : θ < Real.pi) :
    Real.cos θ ≤ 0 ↔ (θ ≤ -(Real.pi / 2) ∨ Real.pi / 2 ≤ θ) := by
  constructor
  · intro hc
    by_contra hcon
    push_neg at hcon
    have := Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨hcon.1, hcon.2⟩)
    linarith
  · rintro (h | h)
    · have hneg : Real.cos (-θ) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [Real.pi_pos])
      rwa [Real.cos_neg] at hneg
    · exact Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [Real.pi_pos])

lemma cos_nonpos_iff_of_le_neg_pi_div_two {u : ℝ} (h1 : -(2 * Real.pi) < u)
    (h2 : u ≤ -(Real.pi / 2)) : Real.cos u ≤ 0 ↔ -(3 * Real.pi / 2) ≤ u := by
  constructor
  · intro hc
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < Real.cos (u + 2 * Real.pi) := by
      refine Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    rw [Real.cos_add_two_pi] at hpos
    linarith
  · intro h
    have hneg : Real.cos (-u) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    rwa [Real.cos_neg] at hneg

lemma cos_nonpos_iff_of_neg_pi_div_two_le {u : ℝ} (h1 : -(Real.pi / 2) ≤ u) (h2 : u < Real.pi) :
    Real.cos u ≤ 0 ↔ (Real.pi / 2 ≤ u ∨ u = -(Real.pi / 2)) := by
  constructor
  · intro hc
    by_cases he : u = -(Real.pi / 2)
    · exact Or.inr he
    · refine Or.inl ?_
      by_contra hcon
      push_neg at hcon
      have : 0 < Real.cos u :=
        Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨lt_of_le_of_ne h1 (Ne.symm he), hcon⟩)
      linarith
  · rintro (h | rfl)
    · exact Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [Real.pi_pos])
    · simp

/-! ## The angular measure of an intersection of two half-planes -/

lemma measurableSet_twoHalfplaneAngles (α : ℝ) :
    MeasurableSet {θ : ℝ | Real.cos θ ≤ 0 ∧ Real.cos (θ - α) ≤ 0} := by
  apply MeasurableSet.inter
  · exact measurableSet_le Real.continuous_cos.measurable measurable_const
  · exact measurableSet_le
      ((Real.continuous_cos.comp (continuous_id.sub continuous_const)).measurable)
      measurable_const

/-- The set of angles `θ ∈ (-π, π)` with `cos θ ≤ 0` and `cos (θ - α) ≤ 0` has measure `π - α`,
for `α ∈ [0, π]`. -/
lemma angular_measure_two_halfplanes {α : ℝ} (h0 : 0 ≤ α) (hpi : α ≤ Real.pi) :
    volume ({θ : ℝ | Real.cos θ ≤ 0 ∧ Real.cos (θ - α) ≤ 0} ∩
        Set.Ioo (-Real.pi) Real.pi)
      = ENNReal.ofReal (Real.pi - α) := by
  have hpipos := Real.pi_pos
  set Θ : Set ℝ := {θ : ℝ | Real.cos θ ≤ 0 ∧ Real.cos (θ - α) ≤ 0} with hΘdef
  have hΘmeas : MeasurableSet Θ := measurableSet_twoHalfplaneAngles α
  set a1 : ℝ := max (-Real.pi) (α - 3 * Real.pi / 2) with ha1
  set a2 : ℝ := max (Real.pi / 2) (α + Real.pi / 2) with ha2
  have hsplit : Θ ∩ Set.Ioo (-Real.pi) Real.pi
      = (Θ ∩ Set.Ioc (-Real.pi) (-(Real.pi / 2))) ∪
        (Θ ∩ Set.Ico (Real.pi / 2) Real.pi) := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioc, Set.mem_Ico, Set.mem_union]
    constructor
    · rintro ⟨hθ, h1, h2⟩
      rcases (cos_nonpos_iff_of_mem_Ioo h1 h2).mp hθ.1 with h | h
      · exact Or.inl ⟨hθ, h1, h⟩
      · exact Or.inr ⟨hθ, h, h2⟩
    · rintro (⟨hθ, h1, h2⟩ | ⟨hθ, h1, h2⟩)
      · exact ⟨hθ, h1, by linarith⟩
      · exact ⟨hθ, by linarith, h2⟩
  have hP1 : volume (Θ ∩ Set.Ioc (-Real.pi) (-(Real.pi / 2)))
      = ENNReal.ofReal (-(Real.pi / 2) - a1) := by
    have hlow : Set.Ioc a1 (-(Real.pi / 2)) ⊆ Θ ∩ Set.Ioc (-Real.pi) (-(Real.pi / 2)) := by
      rintro θ ⟨hl, hr⟩
      rw [ha1, max_lt_iff] at hl
      refine ⟨⟨?_, ?_⟩, hl.1, hr⟩
      · exact (cos_nonpos_iff_of_mem_Ioo hl.1 (by linarith)).mpr (Or.inl hr)
      · exact (cos_nonpos_iff_of_le_neg_pi_div_two (by linarith) (by linarith)).mpr
          (by linarith [hl.2])
    have hhigh : Θ ∩ Set.Ioc (-Real.pi) (-(Real.pi / 2)) ⊆ Set.Icc a1 (-(Real.pi / 2)) := by
      rintro θ ⟨hθ, hl, hr⟩
      refine ⟨?_, hr⟩
      rw [ha1, max_le_iff]
      exact ⟨le_of_lt hl, by
        linarith [(cos_nonpos_iff_of_le_neg_pi_div_two (u := θ - α)
          (by linarith) (by linarith)).mp hθ.2]⟩
    refine le_antisymm ?_ ?_
    · calc volume (Θ ∩ Set.Ioc (-Real.pi) (-(Real.pi / 2)))
          ≤ volume (Set.Icc a1 (-(Real.pi / 2))) := measure_mono hhigh
        _ = ENNReal.ofReal (-(Real.pi / 2) - a1) := Real.volume_Icc
    · calc ENNReal.ofReal (-(Real.pi / 2) - a1) = volume (Set.Ioc a1 (-(Real.pi / 2))) :=
            Real.volume_Ioc.symm
        _ ≤ volume (Θ ∩ Set.Ioc (-Real.pi) (-(Real.pi / 2))) := measure_mono hlow
  have hP2 : volume (Θ ∩ Set.Ico (Real.pi / 2) Real.pi) = ENNReal.ofReal (Real.pi - a2) := by
    have hlow : Set.Ico a2 Real.pi ⊆ Θ ∩ Set.Ico (Real.pi / 2) Real.pi := by
      rintro θ ⟨hl, hr⟩
      rw [ha2, max_le_iff] at hl
      refine ⟨⟨?_, ?_⟩, hl.1, hr⟩
      · exact (cos_nonpos_iff_of_mem_Ioo (by linarith) hr).mpr (Or.inr hl.1)
      · exact (cos_nonpos_iff_of_neg_pi_div_two_le (by linarith) (by linarith)).mpr
          (Or.inl (by linarith [hl.2]))
    have hhigh : Θ ∩ Set.Ico (Real.pi / 2) Real.pi
        ⊆ Set.Ico a2 Real.pi ∪ {α - Real.pi / 2} := by
      rintro θ ⟨hθ, hl, hr⟩
      rcases (cos_nonpos_iff_of_neg_pi_div_two_le (u := θ - α)
        (by linarith) (by linarith)).mp hθ.2 with h | h
      · exact Or.inl ⟨by rw [ha2, max_le_iff]; exact ⟨hl, by linarith⟩, hr⟩
      · exact Or.inr (by simp; linarith)
    refine le_antisymm ?_ ?_
    · calc volume (Θ ∩ Set.Ico (Real.pi / 2) Real.pi)
          ≤ volume (Set.Ico a2 Real.pi ∪ {α - Real.pi / 2}) := measure_mono hhigh
        _ ≤ volume (Set.Ico a2 Real.pi) + volume ({α - Real.pi / 2} : Set ℝ) :=
            measure_union_le _ _
        _ = ENNReal.ofReal (Real.pi - a2) := by
            rw [Real.volume_Ico, measure_singleton, add_zero]
    · calc ENNReal.ofReal (Real.pi - a2) = volume (Set.Ico a2 Real.pi) := Real.volume_Ico.symm
        _ ≤ volume (Θ ∩ Set.Ico (Real.pi / 2) Real.pi) := measure_mono hlow
  have hdisj : Disjoint (Θ ∩ Set.Ioc (-Real.pi) (-(Real.pi / 2)))
      (Θ ∩ Set.Ico (Real.pi / 2) Real.pi) := by
    refine Set.disjoint_left.mpr ?_
    rintro θ ⟨-, -, h1⟩ ⟨-, h2, -⟩
    linarith
  rw [hsplit, measure_union hdisj (hΘmeas.inter measurableSet_Ico), hP1, hP2]
  rcases le_or_gt α (Real.pi / 2) with hc | hc
  · have e1 : a1 = -Real.pi := max_eq_left (by linarith)
    have e2 : a2 = α + Real.pi / 2 := max_eq_right (by linarith)
    rw [e1, e2, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  · have e1 : a1 = α - 3 * Real.pi / 2 := max_eq_right (by linarith)
    have e2 : a2 = α + Real.pi / 2 := max_eq_right (by linarith)
    rw [e1, e2,
      show ENNReal.ofReal (Real.pi - (α + Real.pi / 2)) = 0 from
        ENNReal.ofReal_eq_zero.mpr (by linarith), add_zero]
    congr 1
    ring

end ThresholdFunctions
end BooleanAnalysis

#min_imports
