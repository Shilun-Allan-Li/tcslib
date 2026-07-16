import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Data.Real.Basic

namespace ProbabilityTheory
end ProbabilityTheory

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

noncomputable section
variable {d k : ℕ}
instance : MeasurableSpace (Matrix (Fin k) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin k → Fin d → ℝ))
end

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

noncomputable section
noncomputable def rademacherReal : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)
end

noncomputable section
instance : IsProbabilityMeasure rademacherReal where
  measure_univ := by
    unfold rademacherReal
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        measure_univ, measure_univ]
    simp [ENNReal.inv_two_add_inv_two]
end

noncomputable section
instance : IsFiniteMeasure rademacherReal := inferInstance
end

noncomputable section
abbrev RadΩ (k d : ℕ) : Type := Fin k → Fin d → ℝ
end

noncomputable section
instance (k d : ℕ) : MeasurableSpace (RadΩ k d) := inferInstance
end

noncomputable section
noncomputable def radJointMeasure (k d : ℕ) : Measure (RadΩ k d) :=
  Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => rademacherReal))
end

noncomputable section
instance (k d : ℕ) : IsProbabilityMeasure (radJointMeasure k d) := by
  unfold radJointMeasure; infer_instance
end

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

noncomputable section
variable {d k : ℕ}
private lemma jl_failure_bound_of_dim
    (ε : ℝ) (hε_pos : 0 < ε)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    0 < k ∧ (V.card : ℝ) ^ 2 *
        (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1 := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_ge_2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog_n_pos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hε_sq_pos : 0 < ε ^ 2 := by positivity
  -- Step (a): kε²/8 ≥ 4 log n.
  have hk_lb : 4 * Real.log n ≤ (k : ℝ) * ε ^ 2 / 8 := by
    have := (div_le_iff₀ hε_sq_pos).mp hk
    nlinarith
  -- Step (b): 0 < k.
  have hk_real_pos : 0 < (k : ℝ) := by
    have : 0 < (k : ℝ) * ε ^ 2 / 8 :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * Real.log n) hk_lb
    nlinarith
  have hk_pos : 0 < k := by exact_mod_cast hk_real_pos
  -- Step (c): exp(-kε²/8) ≤ n^{-4}.
  have hexp_bound : Real.exp (-(k : ℝ) * ε ^ 2 / 8) ≤ (n : ℝ) ^ (-(4 : ℤ)) := by
    have h1 : -(k : ℝ) * ε ^ 2 / 8 ≤ -(4 * Real.log n) := by linarith
    calc Real.exp (-(k : ℝ) * ε ^ 2 / 8)
        ≤ Real.exp (-(4 * Real.log n)) := Real.exp_le_exp.mpr h1
      _ = Real.exp (Real.log n * (-(4 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ (-(4 : ℝ)) := by rw [Real.rpow_def_of_pos hn_pos]
      _ = (n : ℝ) ^ (-(4 : ℤ)) := by
          rw [show (-(4 : ℝ)) = ((-(4 : ℤ) : ℤ) : ℝ) from by norm_cast]
          rw [← Real.rpow_intCast]
  -- Step (d): V.card² · 2 · exp(-kε²/8) ≤ 2/n² ≤ 1/2 < 1.
  have hFail : (V.card : ℝ) ^ 2 *
      (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1 := by
    have hcard_sq_le : (V.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have hcard_nn : (0 : ℝ) ≤ V.card := by positivity
      have hcard_le : (V.card : ℝ) ≤ n := by exact_mod_cast hV
      exact pow_le_pow_left₀ hcard_nn hcard_le 2
    have h1 : (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
            ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) := by
      have hrhs_nn : 0 ≤ 2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by positivity
      exact mul_le_mul hcard_sq_le
        (mul_le_mul_of_nonneg_left hexp_bound (by norm_num : (0 : ℝ) ≤ 2))
        hrhs_nn (by positivity)
    have h2 : (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) = 2 / (n : ℝ) ^ 2 := by
      rw [zpow_neg, zpow_ofNat]; field_simp
    have h3 : (2 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 := by
      have hn_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have hn_sq_ge : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ hn_sq_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    calc (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
        ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) := h1
      _ = 2 / (n : ℝ) ^ 2 := h2
      _ ≤ 1 / 2 := h3
      _ < 1 := by norm_num
  exact ⟨hk_pos, hFail⟩
end
