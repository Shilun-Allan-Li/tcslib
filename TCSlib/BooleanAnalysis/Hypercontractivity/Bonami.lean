import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Decomposition
import TCSlib.BooleanAnalysis.Hypercontractivity.MomentBounds

/-!
# Bonami's fourth-moment lemma

This file formalizes the fourth-moment form of Bonami's lemma for Boolean functions of bounded
Fourier degree.  It supplies the expectation and uniform-measure formulations used by the
hypercontractivity development.

## Main results

* `bonami_expect`: a degree-`k` Boolean function has fourth moment at most `9^k` times the
  square of its second moment.
* `bonami_lemma`: the corresponding moment bound stated using `uniformMeasure`.
* `degree_zero_const` and `degree_zero_fourth_moment`: base cases for the induction.
-/

namespace Bonami
open BooleanAnalysis

section
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/- A degree-0 function is constant -/
lemma degree_zero_const {n : ℕ} (f : BooleanFunc n) (hf : has_degree_at_most f 0) :
    ∀ x, f x = f default := by
  intro x;
  -- By definition of $f$, we can write it as a sum of its Fourier coefficients.
  have h_fourier : f = fun x => ∑ S : Finset (Fin n), BooleanAnalysis.fourierCoeff f S * chiS S x := by
    exact funext fun x => walsh_expansion f x;
  rw [ h_fourier ];
  refine' Finset.sum_congr rfl fun S hS => _;
  by_cases h : BooleanAnalysis.fourierCoeff f S = 0 <;> simp +decide [ h ];
  specialize hf S h;
  simp_all +singlePass [ Finset.card_eq_zero ] ;

/- For a degree-0 (constant) function, E[f^4] = (E[f^2])^2 -/
lemma degree_zero_fourth_moment {n : ℕ} (f : BooleanFunc n) (hf : has_degree_at_most f 0) :
    expect (fun x => f x ^ 4) = (expect (fun x => f x ^ 2)) ^ 2 := by
  -- Since $f$ is constant, we have $f(x) = f(default)$ for all $x$.
  have h_const : ∀ x : BoolCube n, f x = f default := by
    exact fun x => degree_zero_const f hf x;
  unfold expect; simp +decide [ h_const ] ; ring_nf;
  unfold uniformWeight; norm_num [ pow_mul ] ; ring_nf;
  simp [ pow_mul' ]

/-
  Key algebraic inequality for the Bonami lemma inductive step.
  If A ≤ 9^(m+1) a², B ≤ 9^m b², C² ≤ A·B, and all are non-negative,
  then A + 6C + B ≤ 9^(m+1) (a+b)² -/
lemma bonami_algebra {m : ℕ} {a b A B C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hA_bound : A ≤ 9 ^ (m + 1) * a ^ 2)
    (hB_bound : B ≤ 9 ^ m * b ^ 2)
    (hC_bound : C ^ 2 ≤ A * B) :
    A + 6 * C + B ≤ 9 ^ (m + 1) * (a + b) ^ 2 := by
  -- By combining terms, we can factor out common factors and simplify the expression.
  ring_nf at *;
  nlinarith [ show 0 ≤ 9 ^ m by positivity, show 0 ≤ a * b * 9 ^ m by positivity, sq_nonneg ( C - a * b * 9 ^ m * 3 ), mul_le_mul_of_nonneg_left hB_bound ( show 0 ≤ 9 ^ m by positivity ) ]

/-- The main Bonami lemma, proved without the k ≥ 1 assumption, in terms of expectation -/
lemma bonami_expect {n : ℕ} (k : ℕ) (f : BooleanFunc n)
    (hf : has_degree_at_most f k) :
    expect (fun x ↦ f x ^ 4) ≤ (9 : ℝ) ^ k * (expect (fun x ↦ f x ^ 2)) ^ 2 := by
  induction n generalizing k with
  | zero =>
    -- BoolCube 0 has one element, everything reduces to f(default)
    unfold expect;
    norm_num [ Finset.card_univ ] ; ring_nf ; norm_cast; norm_num;
    unfold uniformWeight; norm_num; ring_nf; norm_cast; norm_num;
    exact le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ ( by norm_num ) )
  | succ n ih =>
    by_cases hk : k = 0
    · -- k = 0: f is constant
      subst hk
      simp only [pow_zero, one_mul]
      exact le_of_eq (degree_zero_fourth_moment f hf)
    · -- k ≥ 1: write k = m + 1
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk
      -- Define g = avgLast f, h = diffLast f
      set g := avgLast f
      set hh := diffLast f
      -- Apply the decompositions
      rw [fourth_moment_decomp f, second_moment_decomp f]
      -- Get degree bounds
      have hg_deg : has_degree_at_most g (m + 1) := degree_avgLast f (m + 1) hf
      have hh_deg : has_degree_at_most hh m := by
        have := degree_diffLast f (m + 1) hf
        simp at this
        exact this
      -- Apply IH
      have hg_bound := ih (m + 1) g hg_deg
      have hh_bound := ih m hh hh_deg
      -- Get non-negativity
      have ha := expect_sq_nonneg g
      have hb := expect_sq_nonneg hh
      have hA := expect_fourth_nonneg g
      have hB := expect_fourth_nonneg hh
      -- Get Cauchy-Schwarz
      have hCS := expect_cs_sq g hh
      -- Apply the algebraic lemma
      set a := expect (fun x => g x ^ 2)
      set b := expect (fun x => hh x ^ 2)
      set A := expect (fun x => g x ^ 4)
      set B := expect (fun x => hh x ^ 4)
      set C := expect (fun x => g x ^ 2 * hh x ^ 2)
      have hC_nn : 0 ≤ C := expect_sq_nonneg_prod g hh
      exact bonami_algebra ha hb hB hC_nn hg_bound hh_bound hCS

lemma moment_eq_expect {n : ℕ} (f : BooleanFunc n) (p : ℕ)
    (P : Measure (BoolCube n)) [IsProbabilityMeasure P]
    (hP_unif : ∀ x, (P {x}).toReal = uniformWeight n) :
    moment f p P = expect (fun x ↦ f x ^ p) := by
  rw [moment]
  simp only [Pi.pow_apply, Integrable.of_finite, integral_fintype, smul_eq_mul]
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have h_meas_x : (P.real {x}) = uniformWeight n := hP_unif x
  rw [h_meas_x]

/-- The canonical uniform probability measure on the Boolean Hypercube. -/
noncomputable def uniformMeasure (n : ℕ) : Measure (BoolCube n) :=
  (PMF.uniformOfFintype (BoolCube n)).toMeasure

instance (n : ℕ) : IsProbabilityMeasure (uniformMeasure n) := by
  unfold uniformMeasure
  infer_instance

/-- Prove that our canonical measure matches the combinatorial uniformWeight. -/
lemma uniformMeasure_apply {n : ℕ} (x : BoolCube n) :
    ((uniformMeasure n) {x}).toReal = uniformWeight n := by
  dsimp [uniformMeasure]
  rw [PMF.toMeasure_apply_singleton]
  simp only [PMF.uniformOfFintype_apply]
  rw [ENNReal.toReal_inv]
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold uniformWeight
  rw[ENNReal.toReal_natCast]
  simp only [Nat.cast_pow, Nat.cast_ofNat, inv_pow]
  exact MeasurableSet.singleton x

/--
The Bonami Lemma:
A Boolean function of degree at most k is `9^k`-reasonable under the uniform measure.
-/
lemma bonami_lemma {n : ℕ} (k : ℕ) (f : BooleanFunc n)
    (hf : has_degree_at_most f k) :
    IsBReasonable f (uniformMeasure n) ((9 : ℝ) ^ k) := by

  -- 1. Unfold your B-reasonability definition
  rw [IsBReasonable]

  -- 2. Use the bridge lemma specifically on the uniformMeasure
  rw [moment_eq_expect f 4 (uniformMeasure n) uniformMeasure_apply]
  rw [moment_eq_expect f 2 (uniformMeasure n) uniformMeasure_apply]

  -- 3. Apply the purely algebraic expectation bound
  exact bonami_expect k f hf

end
end Bonami
