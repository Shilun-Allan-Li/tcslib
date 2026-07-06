/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy
import Mathlib.InformationTheory.KullbackLeibler.Basic
import PFR.Kullback

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# KL Divergence

## Main results

- `FiniteMeasureSpace.klDiv_eq_sum_llr`: on a finite measurable space, the KL divergence between
  finite measures equals the finite sum of the log-likelihood ratio against singleton masses
- `FiniteMeasureSpace.pmf_klDiv_eq_sum_llr`: on a finite measurable space, the KL divergence
  between PMFs is expressed as a finite sum over the PMF values

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace CommunicationComplexity

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between finite measures is the
finite sum of the log-likelihood ratio against the singleton masses, with Mathlib's finite-measure
correction term. -/
private theorem klDiv_eq_sum_llr_of_ac
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    InformationTheory.klDiv μ ν =
      ENNReal.ofReal
        (∑ ω : Ω, μ.real ({ω} : Set Ω) * llr μ ν ω + ν.real Set.univ - μ.real Set.univ) := by
  have h_int : Integrable (llr μ ν) μ := Integrable.of_finite
  rw [InformationTheory.klDiv_of_ac_of_integrable h_ac h_int]
  congr 1
  rw [MeasureTheory.integral_fintype (llr μ ν) h_int]
  simp [smul_eq_mul]

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between finite measures is `∞`
exactly in the displayed formula when some singleton has zero `ν`-mass and nonzero `μ`-mass;
otherwise it is the finite sum of the log-likelihood ratio against the singleton masses, with
Mathlib's finite-measure correction term. -/
theorem FiniteMeasureSpace.klDiv_eq_sum_llr
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv μ ν =
      if ∃ ω, ν ({ω} : Set Ω) = 0 ∧ μ ({ω} : Set Ω) ≠ 0 then ∞
      else ENNReal.ofReal
        (∑ ω : Ω, μ.real ({ω} : Set Ω) * llr μ ν ω + ν.real Set.univ - μ.real Set.univ) := by
  by_cases hbad : ∃ ω, ν ({ω} : Set Ω) = 0 ∧ μ ({ω} : Set Ω) ≠ 0
  · rw [if_pos hbad]
    apply InformationTheory.klDiv_of_not_ac
    intro h_ac
    rw [FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons] at h_ac
    rcases hbad with ⟨ω, hν, hμ⟩
    exact hμ (h_ac ω hν)
  · rw [if_neg hbad]
    have h_ac : μ ≪ ν := by
      rw [FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons]
      intro ω hν
      by_contra hμ
      exact hbad ⟨ω, hν, hμ⟩
    exact klDiv_eq_sum_llr_of_ac μ ν h_ac

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between PMFs is `∞` if some
point has zero `q`-mass and nonzero `p`-mass; otherwise it is a finite sum over the PMFs. -/
theorem FiniteMeasureSpace.pmf_klDiv_eq_sum_llr
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (p q : PMF Ω) :
    InformationTheory.klDiv p.toMeasure q.toMeasure =
      if ∃ ω, q ω = 0 ∧ p ω ≠ 0 then ∞
      else ENNReal.ofReal (∑ ω : Ω, (p ω).toReal * llr p.toMeasure q.toMeasure ω) := by
  rw [FiniteMeasureSpace.klDiv_eq_sum_llr p.toMeasure q.toMeasure]
  have hpω : ∀ ω : Ω, p.toMeasure {ω} = p ω :=
    fun ω => p.toMeasure_apply_singleton ω (MeasurableSet.singleton ω)
  have hqω : ∀ ω : Ω, q.toMeasure {ω} = q ω :=
    fun ω => q.toMeasure_apply_singleton ω (MeasurableSet.singleton ω)
  have hp : ∀ ω : Ω, p.toMeasure.real {ω} = (p ω).toReal :=
    fun ω => by show (p.toMeasure {ω}).toReal = _; rw [hpω]
  simp only [hp, hpω, hqω, measureReal_univ_eq_one, add_sub_cancel_right]

open Classical in
private theorem rnDeriv_toReal_eq_singleton_ratio
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) (ω : Ω)
    (hν : ν ({ω} : Set Ω) ≠ 0) :
    (μ.rnDeriv ν ω).toReal = μ.real ({ω} : Set Ω) / ν.real ({ω} : Set Ω) := by
  have hset := Measure.setIntegral_toReal_rnDeriv h_ac ({ω} : Set Ω)
  rw [MeasureTheory.integral_singleton] at hset
  change ν.real ({ω} : Set Ω) * (μ.rnDeriv ν ω).toReal =
    μ.real ({ω} : Set Ω) at hset
  have hνreal : ν.real ({ω} : Set Ω) ≠ 0 := by
    rwa [MeasureTheory.measureReal_ne_zero_iff (μ := ν) (s := ({ω} : Set Ω))]
  rw [eq_div_iff hνreal]
  rw [mul_comm]
  exact hset

open Classical in
private theorem singleton_mass_mul_llr_eq_log_ratio
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) (ω : Ω) :
    μ.real ({ω} : Set Ω) * llr μ ν ω =
      μ.real ({ω} : Set Ω) *
        Real.log (μ.real ({ω} : Set Ω) / ν.real ({ω} : Set Ω)) := by
  by_cases hμ : μ ({ω} : Set Ω) = 0
  · have hμreal : μ.real ({ω} : Set Ω) = 0 := by
      simp [Measure.real, hμ]
    simp [hμreal]
  · have hν : ν ({ω} : Set Ω) ≠ 0 := by
      intro hν
      exact hμ (h_ac hν)
    simp [llr_def, rnDeriv_toReal_eq_singleton_ratio h_ac ω hν]

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between finite measures is `∞`
if some singleton has zero `ν`-mass and nonzero `μ`-mass; otherwise it is the finite sum of
`μ {ω} * log (μ {ω} / ν {ω})`, with Mathlib's finite-measure correction term. -/
theorem FiniteMeasureSpace.klDiv_eq_sum_log
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv μ ν =
      if ∃ ω, ν ({ω} : Set Ω) = 0 ∧ μ ({ω} : Set Ω) ≠ 0 then ∞
      else ENNReal.ofReal
        (∑ ω : Ω,
          μ.real ({ω} : Set Ω) *
            Real.log (μ.real ({ω} : Set Ω) / ν.real ({ω} : Set Ω)) +
            ν.real Set.univ - μ.real Set.univ) := by
  rw [FiniteMeasureSpace.klDiv_eq_sum_llr μ ν]
  split_ifs with hbad
  · rfl
  · have h_ac : μ ≪ ν := by
      rw [FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons]
      intro ω hν
      by_contra hμ
      exact hbad ⟨ω, hν, hμ⟩
    congr 1
    congr 2
    apply Finset.sum_congr rfl
    intro ω _
    exact singleton_mass_mul_llr_eq_log_ratio h_ac ω

open Classical in
/-- On a finite space, KL divergence from a probability measure to a full-support probability
measure is finite, stated for measures with `IsProbabilityMeasure` instances. -/
theorem FiniteMeasureSpace.klDiv_ne_top_of_forall_toPMF_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ ω, ν.toPMF ω ≠ 0) :
    InformationTheory.klDiv μ ν ≠ ∞ := by
  rw [FiniteMeasureSpace.klDiv_eq_sum_log μ ν]
  rw [if_neg]
  · exact ENNReal.ofReal_ne_top
  · rintro ⟨ω, hνω, -⟩
    exact hν ω (by simpa [Measure.toPMF_apply] using hνω)

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between PMFs is `∞` if some
point has zero `q`-mass and nonzero `p`-mass; otherwise it is
`∑ ω, p ω * log (p ω / q ω)`. -/
theorem FiniteMeasureSpace.pmf_klDiv_eq_sum_log
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (p q : PMF Ω) :
    InformationTheory.klDiv p.toMeasure q.toMeasure =
      if ∃ ω, q ω = 0 ∧ p ω ≠ 0 then ∞
      else ENNReal.ofReal (∑ ω : Ω,
        (p ω).toReal * Real.log ((p ω).toReal / (q ω).toReal)) := by
  rw [FiniteMeasureSpace.klDiv_eq_sum_log p.toMeasure q.toMeasure]
  have hpω : ∀ ω : Ω, p.toMeasure {ω} = p ω :=
    fun ω => p.toMeasure_apply_singleton ω (MeasurableSet.singleton ω)
  have hqω : ∀ ω : Ω, q.toMeasure {ω} = q ω :=
    fun ω => q.toMeasure_apply_singleton ω (MeasurableSet.singleton ω)
  have hp : ∀ ω : Ω, p.toMeasure.real {ω} = (p ω).toReal :=
    fun ω => by show (p.toMeasure {ω}).toReal = _; rw [hpω]
  have hq : ∀ ω : Ω, q.toMeasure.real {ω} = (q ω).toReal :=
    fun ω => by show (q.toMeasure {ω}).toReal = _; rw [hqω]
  simp only [hp, hq, hpω, hqω, measureReal_univ_eq_one, add_sub_cancel_right]

end CommunicationComplexity

namespace ProbabilityTheory

open Classical in
/-- On one-bit probability measures, Mathlib's `klDiv` to any full-support bit law agrees with
the real-valued PFR `KLDiv` used by the entropy API. -/
theorem toReal_klDiv_bool_eq_KLDiv
    (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ b, ν.toPMF b ≠ 0) :
    (InformationTheory.klDiv μ ν).toReal =
      KL[id ; μ # id ; ν] := by
  have hnonneg :
      0 ≤ KL[id ; μ # id ; ν] := by
    exact KLDiv_nonneg (μ := μ) (μ' := ν)
      (X := id) (Y := id) Measurable.of_discrete Measurable.of_discrete
      (fun b hb => False.elim (hν b (by simpa [Measure.toPMF_apply] using hb)))
  rw [CommunicationComplexity.FiniteMeasureSpace.klDiv_eq_sum_log μ ν]
  rw [if_neg]
  · rw [ENNReal.toReal_ofReal]
    · rw [KLDiv_eq_sum]
      rw [measureReal_univ_eq_one, measureReal_univ_eq_one]
      simp [Measure.real]
    · rw [measureReal_univ_eq_one, measureReal_univ_eq_one]
      simpa [KLDiv_eq_sum, Measure.real] using hnonneg
  · rintro ⟨b, hb, -⟩
    exact hν b hb

open Classical in
/-- Positive conditional fibers let Mathlib's one-bit KL divergence from the law of a Boolean
random variable to any full-support reference bit law be read as the PFR real-valued `KLDiv` of
the corresponding random variable. -/
theorem toReal_klDiv_map_bool_eq_KLDiv_of_measureReal_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Bool) (S : Set Ω) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hX : Measurable X) (hS : μ.real S ≠ 0)
    (hν : ∀ b, ν.toPMF b ≠ 0) :
    (InformationTheory.klDiv (Measure.map X (μ[|S])) ν).toReal =
      KL[X ; μ[|S] # id ; ν] := by
  haveI : IsProbabilityMeasure (μ[|S]) :=
    ProbabilityTheory.cond_isProbabilityMeasure
      ((MeasureTheory.measureReal_ne_zero_iff (μ := μ) (s := S)).mp hS)
  haveI : IsProbabilityMeasure (Measure.map X (μ[|S])) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have h :=
    toReal_klDiv_bool_eq_KLDiv
      (Measure.map X (μ[|S])) ν hν
  simpa [KLDiv] using h

end ProbabilityTheory
