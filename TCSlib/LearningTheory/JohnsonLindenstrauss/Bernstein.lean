/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bernstein-type MGF condition and concentration

## Main results

- `HasBernsteinMGF`: structure capturing the "two-parameter sub-exponential" MGF bound `exp(c·t²)` on `|t| ≤ tmax`
- `HasBernsteinMGF.sum_of_iIndepFun`: closure of `HasBernsteinMGF` under iid finite sums (parameter scales as `∑ cᵢ`)
- `HasBernsteinMGF.measure_ge_le`: upper-tail Chernoff bound `ℙ[s ≤ X] ≤ exp(−s²/(4c))` on the optimal-`t` range
- `HasBernsteinMGF.measure_le_le`: lower-tail Chernoff bound `ℙ[X ≤ −s] ≤ exp(−s²/(4c))`
- `HasBernsteinMGF.measure_abs_gt_le`: two-sided bound `ℙ[s < |X|] ≤ 2·exp(−s²/(4c))`
- `centered_squared_iid_tail`: Bernstein tail bound for the deviation of `∑ Yᵢ²` from its mean `n·σ²`

## References

- Original formalization by Ganesh Sankar
-/

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## The `HasBernsteinMGF` predicate and its concentration bounds -/

/-- `HasBernsteinMGF X μ c tmax` says the MGF of `X` under `μ` is bounded
by the Gaussian envelope `exp(c t²)` on `|t| ≤ tmax`, with `exp(t · X)`
integrable on the same range. The pair `(c, tmax)` parametrizes a
"two-parameter sub-exponential" family: `c` controls the local quadratic
behavior near zero; `tmax` bounds the radius of the MGF's domain (which
may be finite for genuinely sub-exponential — but not sub-Gaussian — RVs).

For sub-Gaussian `X` (with parameter `σ²`) one can take `tmax = ∞`
formally; this predicate is more useful when `tmax < ∞`. -/
structure HasBernsteinMGF (X : Ω → ℝ) (μ : Measure Ω) (c tmax : ℝ) : Prop where
  integrable : ∀ t : ℝ, |t| ≤ tmax → Integrable (fun ω => Real.exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, |t| ≤ tmax → mgf X μ t ≤ Real.exp (c * t ^ 2)

namespace HasBernsteinMGF

variable {X : Ω → ℝ} {μ : Measure Ω} {c tmax : ℝ}

/-- **iid closure**: for an iid family `X i` with each `X i` having
`HasBernsteinMGF (c i, tmax)`, the sum `∑ X i` has Bernstein MGF
`(∑ c i, tmax)`. -/
lemma sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    {c : ι → ℝ} {tmax : ℝ}
    {s : Finset ι} (h_bern : ∀ i ∈ s, HasBernsteinMGF (X i) μ (c i) tmax) :
    HasBernsteinMGF (fun ω => ∑ i ∈ s, X i ω) μ (∑ i ∈ s, c i) tmax := by
  refine ⟨?_, ?_⟩
  · -- Integrability of `exp(t · ∑ X_i)` on `|t| ≤ tmax` from per-element integrability.
    intro t ht
    have h1 : Integrable (fun ω => Real.exp (t * (∑ i ∈ s, X i) ω)) μ := by
      refine h_indep.integrable_exp_mul_sum h_meas (fun i hi => ?_)
      exact (h_bern i hi).integrable t ht
    convert h1 using 1
    funext ω
    rw [Finset.sum_apply]
  · -- MGF bound: `mgf (∑ X_i) μ t = ∏ mgf (X_i) μ t ≤ ∏ exp(c_i t²) = exp(∑ c_i · t²)`.
    intro t ht
    have h_pi_eq : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
      funext ω; rw [Finset.sum_apply]
    rw [h_pi_eq, h_indep.mgf_sum h_meas]
    calc ∏ i ∈ s, mgf (X i) μ t
        ≤ ∏ i ∈ s, Real.exp (c i * t ^ 2) := by
          apply Finset.prod_le_prod
          · exact fun i _ => mgf_nonneg
          · exact fun i hi => (h_bern i hi).mgf_le t ht
      _ = Real.exp ((∑ i ∈ s, c i) * t ^ 2) := by
          rw [← Real.exp_sum, Finset.sum_mul]

/-- **Upper-tail Bernstein bound** (in the optimal-`t` range).
For `HasBernsteinMGF X μ c tmax` with `c > 0`, `0 ≤ s ≤ 2 c · tmax`,
`(μ {ω | s ≤ X ω}).toReal ≤ exp(-s²/(4 c))`.

The hypothesis `s ≤ 2 c · tmax` ensures the Chernoff-optimal `t = s/(2c)`
lies inside the MGF-bounded range `|t| ≤ tmax`. -/
lemma measure_ge_le {μ : Measure Ω} [IsFiniteMeasure μ]
    (h : HasBernsteinMGF X μ c tmax)
    (hc : 0 < c) (s : ℝ) (hs_pos : 0 ≤ s) (hs_le : s ≤ 2 * c * tmax) :
    (μ {ω | s ≤ X ω}).toReal ≤ Real.exp (-s ^ 2 / (4 * c)) := by
  -- Optimal t = s / (2c).
  set t : ℝ := s / (2 * c) with ht_def
  have h2c_pos : 0 < 2 * c := by linarith
  have ht_pos : 0 ≤ t := by rw [ht_def]; positivity
  have ht_le_tmax : t ≤ tmax := by
    rw [ht_def, div_le_iff₀ h2c_pos]
    linarith
  have ht_abs : |t| ≤ tmax := by rw [abs_of_nonneg ht_pos]; exact ht_le_tmax
  -- Chernoff: μ.real {ω | s ≤ X ω} ≤ exp(-t·s) · mgf X μ t ≤ exp(-t·s + c·t²).
  have h_chernoff : (μ {ω | s ≤ X ω}).toReal ≤
      Real.exp (-t * s) * mgf X μ t :=
    measure_ge_le_exp_mul_mgf s ht_pos (h.integrable t ht_abs)
  refine le_trans h_chernoff ?_
  refine le_trans (mul_le_mul_of_nonneg_left (h.mgf_le t ht_abs) (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- Now: -t·s + c·t² ≤ -s²/(4c).
  -- t = s/(2c), so c·t² = s²/(4c) and t·s = s²/(2c). Hence -t·s + c·t² = -s²/(4c).
  rw [ht_def]
  field_simp
  ring_nf
  rfl

/-- **Lower-tail Bernstein bound** by symmetry.
For `HasBernsteinMGF X μ c tmax` with `c > 0`, `0 ≤ s ≤ 2 c · tmax`,
`(μ {ω | X ω ≤ -s}).toReal ≤ exp(-s²/(4c))`. -/
lemma measure_le_le {μ : Measure Ω} [IsFiniteMeasure μ]
    (h : HasBernsteinMGF X μ c tmax)
    (hc : 0 < c) (s : ℝ) (hs_pos : 0 ≤ s) (hs_le : s ≤ 2 * c * tmax) :
    (μ {ω | X ω ≤ -s}).toReal ≤ Real.exp (-s ^ 2 / (4 * c)) := by
  -- Use t = -s/(2c) and `measure_le_le_exp_mul_mgf`.
  set t : ℝ := -(s / (2 * c)) with ht_def
  have h2c_pos : 0 < 2 * c := by linarith
  have ht_neg : t ≤ 0 := by rw [ht_def]; linarith [div_nonneg hs_pos h2c_pos.le]
  have ht_le_tmax : -t ≤ tmax := by
    rw [ht_def]; simp only [neg_neg]; rw [div_le_iff₀ h2c_pos]; linarith
  have ht_abs : |t| ≤ tmax := by rw [abs_of_nonpos ht_neg]; exact ht_le_tmax
  have h_chernoff : (μ {ω | X ω ≤ -s}).toReal ≤
      Real.exp (-t * (-s)) * mgf X μ t :=
    measure_le_le_exp_mul_mgf (-s) ht_neg (h.integrable t ht_abs)
  refine le_trans h_chernoff ?_
  refine le_trans (mul_le_mul_of_nonneg_left (h.mgf_le t ht_abs) (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [ht_def]
  field_simp
  ring_nf
  rfl

/-- **Two-sided Bernstein bound.**
For `HasBernsteinMGF X μ c tmax` with `c > 0`, `0 ≤ s ≤ 2 c · tmax`,
`(μ {ω | s < |X ω|}).toReal ≤ 2 · exp(-s²/(4c))`. -/
lemma measure_abs_gt_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : HasBernsteinMGF X μ c tmax)
    (hc : 0 < c) (s : ℝ) (hs_pos : 0 ≤ s) (hs_le : s ≤ 2 * c * tmax) :
    (μ {ω | s < |X ω|}).toReal ≤ 2 * Real.exp (-s ^ 2 / (4 * c)) := by
  -- Bad event ⊆ {s ≤ X} ∪ {X ≤ -s}.
  have hsubset : {ω | s < |X ω|} ⊆ {ω | s ≤ X ω} ∪ {ω | X ω ≤ -s} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
    by_contra h_neither
    rw [not_or] at h_neither
    obtain ⟨h1, h2⟩ := h_neither
    have hXlt : X ω < s := lt_of_not_ge h1
    have hXgt : -s < X ω := lt_of_not_ge h2
    have habs_lt : |X ω| < s := abs_lt.mpr ⟨hXgt, hXlt⟩
    exact (lt_irrefl s) (lt_of_lt_of_le hω habs_lt.le)
  -- Apply union + the two single-tail bounds.
  calc (μ {ω | s < |X ω|}).toReal
      ≤ (μ ({ω | s ≤ X ω} ∪ {ω | X ω ≤ -s})).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
    _ ≤ (μ {ω | s ≤ X ω}).toReal + (μ {ω | X ω ≤ -s}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
          (measure_union_le _ _)
    _ ≤ Real.exp (-s ^ 2 / (4 * c)) + Real.exp (-s ^ 2 / (4 * c)) := by
        gcongr
        · exact h.measure_ge_le hc s hs_pos hs_le
        · exact h.measure_le_le hc s hs_pos hs_le
    _ = 2 * Real.exp (-s ^ 2 / (4 * c)) := by ring

end HasBernsteinMGF

/-! ## Abstract centered-squared iid tail bound

A drop-in generalization of "chi-squared tail" that works for any iid
family whose centered squared variants `Y² − σ²` have Bernstein MGF.

This is the central reusable tool for JL-style concentration: plug in
Gaussian, Rademacher, or any sub-Gaussian distribution, and the proof
is identical. -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Centered-squared iid Bernstein tail bound.**
For an iid family `Y_1, …, Y_n` (indexed by `ι`) whose centered squares
`Y_i² − σ²` each have `HasBernsteinMGF (c, tmax)`, the deviation of
`Σᵢ Y_iⁿ²` from its expected value `n · σ²` satisfies the Bernstein bound

  `ℙ[ s < |Σ Y_i² − n σ²| ] ≤ 2 · exp(−s² / (4 n c))`

on the optimal `t`-range `0 ≤ s ≤ 2 n c · tmax`. -/
lemma centered_squared_iid_tail
    {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hY_meas : ∀ i, Measurable (Y i))
    (hY_indep : iIndepFun Y μ)
    {σ_sq c tmax : ℝ} (hc : 0 < c)
    (h_bern : ∀ i, HasBernsteinMGF (fun ω => (Y i ω) ^ 2 - σ_sq) μ c tmax)
    (s : ℝ) (hs_pos : 0 ≤ s)
    (hs_le : s ≤ 2 * (Fintype.card ι : ℝ) * c * tmax) :
    (μ {ω | s < |(∑ i, (Y i ω) ^ 2) - (Fintype.card ι : ℝ) * σ_sq|}).toReal ≤
      2 * Real.exp (-s ^ 2 / (4 * (Fintype.card ι : ℝ) * c)) := by
  classical
  -- Centered summands.
  set S : ι → Ω → ℝ := fun i ω => (Y i ω) ^ 2 - σ_sq with hS_def
  have hS_meas : ∀ i, Measurable (S i) := fun i =>
    ((hY_meas i).pow_const 2).sub measurable_const
  have hS_indep : iIndepFun S μ :=
    hY_indep.comp (fun _ y => y ^ 2 - σ_sq) (fun _ => by fun_prop)
  -- Iid sum has Bernstein MGF `(n c, tmax)`.
  have hSum_bern : HasBernsteinMGF (fun ω => ∑ i, S i ω) μ
      ((Fintype.card ι : ℝ) * c) tmax := by
    have h := HasBernsteinMGF.sum_of_iIndepFun hS_indep hS_meas
      (s := Finset.univ) (fun i _ => h_bern i)
    convert h using 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Bad event reduces: `s < |Σ Y_i² − n σ²|  ⇔  s < |Σ S_i|` (since
  -- Σ S_i = Σ (Y_i² − σ²) = (Σ Y_i²) − n σ²).
  have hsum_S : ∀ ω, ∑ i, S i ω = (∑ i, (Y i ω) ^ 2) - (Fintype.card ι : ℝ) * σ_sq := by
    intro ω
    simp only [S, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hbad_eq : {ω | s < |(∑ i, (Y i ω) ^ 2) - (Fintype.card ι : ℝ) * σ_sq|}
      = {ω | s < |∑ i, S i ω|} := by
    ext ω; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum_S]
  rw [hbad_eq]
  -- Case on whether ι is empty.
  by_cases h_empty : Fintype.card ι = 0
  · -- Empty case: Σ S i = 0, so bad event is `s < 0`, empty.
    have h_univ_empty : (Finset.univ : Finset ι) = ∅ :=
      Finset.card_eq_zero.mp (by rw [Finset.card_univ]; exact h_empty)
    have h_event_empty : {ω | s < |∑ i, S i ω|} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [show ∑ i, S i ω = 0 from by
        rw [show (Finset.univ : Finset ι) = ∅ from h_univ_empty]; simp]
      rw [abs_zero]
      exact hs_pos
    rw [h_event_empty, measure_empty, ENNReal.toReal_zero]
    positivity
  · -- Nontrivial case: apply abstract Bernstein concentration.
    have hcard_pos : 0 < Fintype.card ι := Nat.pos_of_ne_zero h_empty
    have hcard_real_pos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcard_pos
    have hnc_pos : 0 < (Fintype.card ι : ℝ) * c := by positivity
    refine le_trans (hSum_bern.measure_abs_gt_le hnc_pos s hs_pos ?_) ?_
    · have : (2 : ℝ) * ((Fintype.card ι : ℝ) * c) * tmax =
          2 * (Fintype.card ι : ℝ) * c * tmax := by ring
      rw [this]; exact hs_le
    · apply le_of_eq
      congr 2
      ring

end ProbabilityTheory
