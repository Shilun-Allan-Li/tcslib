/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Polynomial
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Tensorization
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Norms
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Symmetric
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.TwoPointLaw
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteLaw

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# General random-variable hypercontractivity

Independent sums and the norm-ratio sufficient condition for centered random variables.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `IsHypercontractive.add_independent`.
* `mean_zero_hypercontractive`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Propositions 9.15 and 10.16.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Independent hypercontractive variables remain hypercontractive when added, including
infinite exponents. [OD14, Prop. 9.15]

**Proof sketch.** Write the independent joint law as a product. Apply contraction in one
variable, interchange mixed norms by Minkowski, and apply contraction in the other variable.
For infinite exponents, use essential-supremum bounds and limits of finite norms.
Closure of `Lᑫ` under addition gives the required finite norm of the sum. -/
theorem IsHypercontractive.add_independent {X Y : Ω → ℝ} {p q : ℝ≥0∞} {ρ : ℝ}
    (hX : IsHypercontractive X μ p q ρ) (hY : IsHypercontractive Y μ p q ρ)
    (hindep : IndepFun X Y μ) : IsHypercontractive (fun ω => X ω + Y ω) μ p q ρ := by
  rcases hX with ⟨hp, hpq, hρ0, hρ1, hXmem, hX⟩
  rcases hY with ⟨_, _, _, _, hYmem, hY⟩
  refine ⟨hp, hpq, hρ0, hρ1, hXmem.add hYmem, ?_⟩
  intro a b
  letI : IsProbabilityMeasure (μ.map X) :=
    Measure.isProbabilityMeasure_map hXmem.aemeasurable
  letI : IsProbabilityMeasure (μ.map Y) :=
    Measure.isProbabilityMeasure_map hYmem.aemeasurable
  have hnorm (Z : Ω → ℝ) (hZ : AEMeasurable Z μ)
      (c d : ℝ) (r : ℝ≥0∞) :
      eLpNorm (fun x : ℝ => c + d * x) r (μ.map Z) =
        eLpNorm (fun ω => c + d * Z ω) r μ := by
    exact eLpNorm_map_measure
      ((by fun_prop : Measurable (fun x : ℝ => c + d * x)).aestronglyMeasurable) hZ
  have hν : ∀ c d : ℝ,
      eLpNorm (fun x : ℝ => c + ρ * d * x) q (μ.map X) ≤
        eLpNorm (fun x : ℝ => c + d * x) p (μ.map X) := by
    intro c d
    rw [hnorm X hXmem.aemeasurable c (ρ * d) q,
      hnorm X hXmem.aemeasurable c d p]
    exact hX c d
  have hκ : ∀ c d : ℝ,
      eLpNorm (fun x : ℝ => c + ρ * d * x) q (μ.map Y) ≤
        eLpNorm (fun x : ℝ => c + d * x) p (μ.map Y) := by
    intro c d
    rw [hnorm Y hYmem.aemeasurable c (ρ * d) q,
      hnorm Y hYmem.aemeasurable c d p]
    exact hY c d
  have h := Tensorization.affine_sum_le
    (μ.map X) (μ.map Y) p q hp hpq ρ hν hκ a b
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map
    hXmem.aemeasurable hYmem.aemeasurable).mp hindep
  rw [← hmap] at h
  rw [eLpNorm_map_measure
      ((by fun_prop :
        Measurable (fun z : ℝ × ℝ => a + ρ * b * (z.1 + z.2))).aestronglyMeasurable)
      (hXmem.aemeasurable.prodMk hYmem.aemeasurable),
    eLpNorm_map_measure
      ((by fun_prop :
        Measurable (fun z : ℝ × ℝ => a + b * (z.1 + z.2))).aestronglyMeasurable)
      (hXmem.aemeasurable.prodMk hYmem.aemeasurable)] at h
  simpa only [Function.comp_def] using h


/-- A centered variable of second norm one and finite `q`-norm `C` is hypercontractive
at radius `1/(2C√(q-1))` for `q>2`. [OD14, Thm. 10.16]
The symmetric improvement is `symmetric_hypercontractive`.

**Proof sketch.** Randomize with a uniform sign, which preserves the second and `q`-norms.
Apply the symmetric theorem, then transfer the inequality back using Lemma 10.15. -/
theorem mean_zero_hypercontractive (X : Ω → ℝ) (q C : ℝ) (hq : 2 < q)
    (hmem : MemLp X (ENNReal.ofReal q) μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (hsecond : rvLpNorm X μ 2 = 1) (hC : rvLpNorm X μ q = C) (hCpos : 0 < C) :
    IsHypercontractive X μ 2 (ENNReal.ofReal q) (1 / (2 * C * Real.sqrt (q - 1))) := by
  let ν : Measure ℝ := μ.map X
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hmem.aemeasurable
  let R : Measure ℝ :=
    (1 / 2 : ℝ≥0∞) • Measure.dirac 1 + (1 / 2 : ℝ≥0∞) • Measure.dirac (-1)
  letI : IsProbabilityMeasure R :=
    ⟨by simpa [R] using ENNReal.add_halves (1 : ℝ≥0∞)⟩
  let S : Measure (ℝ × ℝ) := ν.prod R
  letI : IsProbabilityMeasure S := inferInstance
  let Z : ℝ × ℝ → ℝ := fun z => z.2 * z.1
  let F : ℝ × ℝ → ℝ × ℝ := fun z => (z.1, -z.2)
  have hνmem : MemLp (fun x : ℝ => x) (ENNReal.ofReal q) ν := by
    simpa [ν, Function.comp_def] using
      (memLp_map_measure_iff measurable_id.aestronglyMeasurable
        hmem.aemeasurable).mpr hmem
  have hνmean : ∫ x : ℝ, x ∂ν = 0 := by
    calc
      (∫ x : ℝ, x ∂ν) = ∫ ω, X ω ∂μ := by
        simpa [ν, Function.comp_def] using
          integral_map hmem.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := hmean
  have hfst : MeasurePreserving Prod.fst S ν := measurePreserving_fst
  have hsnd : MeasurePreserving Prod.snd S R := measurePreserving_snd
  have hsign : ∀ᵐ y : ℝ ∂R, y = -1 ∨ y = 1 := by
    simp [R, ae_add_measure_iff,
      Measure.ae_smul_measure_iff (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0),
      MeasureTheory.ae_dirac_eq]
  have hSsign : ∀ᵐ z : ℝ × ℝ ∂S, z.2 = -1 ∨ z.2 = 1 :=
    hsnd.quasiMeasurePreserving.ae hsign
  have hRneg : R.map (fun y : ℝ => -y) = R := by
    simp [R, Measure.map_add _ _ measurable_neg, Measure.map_smul,
      Measure.map_dirac measurable_neg, add_comm]
  have hF : MeasurePreserving F S S := by
    refine ⟨measurable_fst.prodMk measurable_snd.neg, ?_⟩
    simpa [F, S, hRneg] using
      (Measure.map_prod_map ν R measurable_id measurable_neg).symm
  have hZmeas : Measurable Z := measurable_snd.mul measurable_fst
  have hsym : IsSymmetricRV Z S := by
    refine ⟨hZmeas.aemeasurable, hZmeas.neg.aemeasurable, ?_⟩
    calc
      S.map Z = (S.map F).map Z := by rw [hF.map_eq]
      _ = S.map (Z ∘ F) := Measure.map_map hZmeas hF.measurable
      _ = S.map (fun z => -Z z) := by
        congr 1
        funext z
        simp [Z, F, Function.comp_def]
  have hfstmem : MemLp (fun z : ℝ × ℝ => z.1) (ENNReal.ofReal q) S := by
    simpa [S, Function.comp_def] using hνmem.comp_fst R
  have hZnorm (p : ℝ≥0∞) :
      eLpNorm Z p S = eLpNorm (fun z : ℝ × ℝ => z.1) p S := by
    apply eLpNorm_congr_enorm_ae
    filter_upwards [hSsign] with z hz
    rcases hz with hz | hz <;> simp [Z, hz]
  have hZmem : MemLp Z (ENNReal.ofReal q) S :=
    ⟨hZmeas.aestronglyMeasurable, by
      rw [hZnorm]
      exact hfstmem.eLpNorm_lt_top⟩
  have hZLp (p : ℝ≥0∞) : eLpNorm Z p S = eLpNorm X p μ := by
    calc
      eLpNorm Z p S = eLpNorm (fun z : ℝ × ℝ => z.1) p S := hZnorm p
      _ = eLpNorm (fun x : ℝ => x) p ν :=
        eLpNorm_comp_measurePreserving measurable_id.aestronglyMeasurable hfst
      _ = eLpNorm X p μ := by
        simpa [ν, Function.comp_def] using
          eLpNorm_map_measure measurable_id.aestronglyMeasurable hmem.aemeasurable
  have hZsecond : rvLpNorm Z S 2 = 1 := by
    simpa [rvLpNorm, hZLp] using hsecond
  have hZC : rvLpNorm Z S q = C := by
    simpa [rvLpNorm, hZLp] using hC
  let ρ : ℝ := 1 / (C * Real.sqrt (q - 1))
  obtain ⟨hp, hpq, hρnonneg, hρlt, _, hsymineq⟩ :=
    symmetric_hypercontractive Z q C hq hsym hZmem hZsecond hZC hCpos
  have hρ : 1 / (2 * C * Real.sqrt (q - 1)) = ρ / 2 := by
    dsimp [ρ]
    have hsqrt : 0 < Real.sqrt (q - 1) := Real.sqrt_pos.mpr (by linarith)
    field_simp [ne_of_gt hCpos, ne_of_gt hsqrt]
    <;> ring
  have hqone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ q by linarith)
  have hr : IsRademacherRV (fun z : ℝ × ℝ => z.2) S := by
    refine ⟨measurable_snd, hSsign, ?_, ?_⟩
    · change S (Prod.snd ⁻¹' {1}) = (1 / 2 : ℝ≥0∞)
      rw [hsnd.measure_preimage (MeasurableSet.singleton 1).nullMeasurableSet]
      norm_num [R, Measure.dirac_apply, Set.indicator_apply]
    · change S (Prod.snd ⁻¹' {-1}) = (1 / 2 : ℝ≥0∞)
      rw [hsnd.measure_preimage (MeasurableSet.singleton (-1 : ℝ)).nullMeasurableSet]
      norm_num [R, Measure.dirac_apply, Set.indicator_apply]
  have hfstmean : ∫ z : ℝ × ℝ, z.1 ∂S = 0 := by
    calc
      (∫ z : ℝ × ℝ, z.1 ∂S) = ∫ x : ℝ, x ∂(S.map Prod.fst) := by
        simpa [Function.comp_def] using
          (integral_map hfst.measurable.aemeasurable
            measurable_id.aestronglyMeasurable).symm
      _ = ∫ x : ℝ, x ∂ν := by rw [hfst.map_eq]
      _ = 0 := hνmean
  have hZmean : ∫ z, Z z ∂S = 0 := by
    have h := hsym.integral_eq
    rw [integral_neg] at h
    linarith
  have hmem2 : MemLp X 2 μ := hmem.mono_exponent hpq
  have hZmem2 : MemLp Z 2 S := hZmem.mono_exponent hpq
  refine ⟨hp, hpq, ?_, ?_, hmem, ?_⟩
  · rw [hρ]
    exact div_nonneg hρnonneg (by norm_num)
  · rw [hρ]
    change ρ < 1 at hρlt
    change 0 ≤ ρ at hρnonneg
    linarith
  · intro a b
    let t : ℝ := ρ * b
    have htmem : MemLp (fun z : ℝ × ℝ => t * z.1) (ENNReal.ofReal q) S :=
      hfstmem.const_mul t
    have htmean : ∫ z : ℝ × ℝ, t * z.1 ∂S = 0 := by
      rw [integral_const_mul, hfstmean, mul_zero]
    have hindep : IndepFun (fun z : ℝ × ℝ => t * z.1) (fun z => z.2) S := by
      simpa [S] using
        (indepFun_prod (measurable_const.mul measurable_id) measurable_id :
          IndepFun (fun z : ℝ × ℝ => t * z.1) (fun z => z.2) (ν.prod R))
    have hrand :=
      randomization_norm_le (fun z : ℝ × ℝ => t * z.1)
        (fun z => z.2) (ENNReal.ofReal q) a hqone htmem
        htmean hr hindep
    have haffine (s : ℝ) :
        eLpNorm (fun z : ℝ × ℝ => a + s * z.1) (ENNReal.ofReal q) S =
          eLpNorm (fun ω => a + s * X ω) (ENNReal.ofReal q) μ := by
      calc
        _ = eLpNorm (fun x : ℝ => a + s * x) (ENNReal.ofReal q) ν :=
          eLpNorm_comp_measurePreserving
            (measurable_const.add (measurable_const.mul measurable_id)).aestronglyMeasurable
            hfst
        _ = _ := by
          simpa [ν, Function.comp_def] using
            eLpNorm_map_measure
              (measurable_const.add
                (measurable_const.mul measurable_id)).aestronglyMeasurable
              hmem.aemeasurable
    have hsq :
        rvLpNorm (fun z => a + b * Z z) S 2 ^ 2 =
          rvLpNorm (fun ω => a + b * X ω) μ 2 ^ 2 := by
      rw [rvLpNorm_affine_sq Z S hZmem2 hZmean a b,
        rvLpNorm_affine_sq X μ hmem2 hmean a b, hZsecond, hsecond]
    have hreal :
        rvLpNorm (fun z => a + b * Z z) S 2 =
          rvLpNorm (fun ω => a + b * X ω) μ 2 := by
      have hz : 0 ≤ rvLpNorm (fun z => a + b * Z z) S 2 :=
        ENNReal.toReal_nonneg
      have hx : 0 ≤ rvLpNorm (fun ω => a + b * X ω) μ 2 :=
        ENNReal.toReal_nonneg
      exact le_antisymm
        ((pow_le_pow_iff_left₀ hz hx (by norm_num : (2 : ℕ) ≠ 0)).mp hsq.le)
        ((pow_le_pow_iff_left₀ hx hz (by norm_num : (2 : ℕ) ≠ 0)).mp hsq.ge)
    have hL2 :
        eLpNorm (fun z => a + b * Z z) 2 S =
          eLpNorm (fun ω => a + b * X ω) 2 μ := by
      have hz : MemLp (fun z => a + b * Z z) 2 S :=
        (memLp_const a).add (hZmem2.const_mul b)
      have hx : MemLp (fun ω => a + b * X ω) 2 μ :=
        (memLp_const a).add (hmem2.const_mul b)
      apply (ENNReal.toReal_eq_toReal hz.eLpNorm_ne_top hx.eLpNorm_ne_top).mp
      simpa [rvLpNorm] using hreal
    calc
      eLpNorm (fun ω => a + (1 / (2 * C * Real.sqrt (q - 1))) * b * X ω)
          (ENNReal.ofReal q) μ =
          eLpNorm (fun z : ℝ × ℝ => a + (1 / 2 : ℝ) * (t * z.1))
            (ENNReal.ofReal q) S := by
        rw [hρ]
        have hf :
            (fun z : ℝ × ℝ => a + (1 / 2 : ℝ) * (t * z.1)) =
              (fun z => a + ((ρ / 2) * b) * z.1) := by
          funext z
          dsimp [t]
          ring
        rw [hf, haffine]
      _ ≤ eLpNorm (fun z : ℝ × ℝ => a + z.2 * (t * z.1))
          (ENNReal.ofReal q) S := hrand
      _ = eLpNorm (fun z => a + ρ * b * Z z) (ENNReal.ofReal q) S := by
        congr 1
        funext z
        dsimp [t, Z]
        ring
      _ ≤ eLpNorm (fun z => a + b * Z z) 2 S := hsymineq a b
      _ = eLpNorm (fun ω => a + b * X ω) 2 μ := hL2

end BooleanAnalysis.Hypercontractivity
