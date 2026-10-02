import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import TCSlib.BooleanAnalysis.ThresholdFunctions.Gaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Degree-one Fourier weight

This file states the Chapter 5 results controlling degree-one Fourier weight for small sets and for
functions with regular first-level coefficients.

## Main definitions

* `HasFKNClosenessBound`: a parameterized statement of the FKN theorem used by Theorem 5.33.

## Main results

* `subcube_degreeOne_weight` and `hammingBall_degreeOne_limit`.
* `levelOne_inequality` and `pi_over_two_theorem`.
* `linear_form_tail_expectation`, the tail estimate used by the Level-1 inequality.
* `biased_degreeOne_weight` and `fkn_closeness_improvement`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, §5.4.
* [Tal96] M. Talagrand, How much are increasing sets positively correlated?, 1996.
* [KKMO07] S. Khot, G. Kindler, E. Mossel, and R. O'Donnell, Optimal inapproximability results for
  MAX-CUT and other 2-variable CSPs?, 2007.
* [MORS10] E. Mossel, R. O'Donnell, O. Regev, J. Steif, and B. Sudakov, Non-interactive
  correlation distillation, inhomogeneous Markov chains, and the reverse Bonami-Beckner inequality,
  2010.
* [JOW12] J. Jendrej, K. Oleszkiewicz, and J. O. Wojtaszczyk, On some extensions of the FKN
  theorem, 2012.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

variable {n : ℕ}

/-- Reindex degree-one Fourier weight by coordinates. -/
private lemma weightLevel_one_eq_sum_singleton (f : BooleanFunc n) :
    weightLevel 1 f = ∑ i : Fin n, fourierCoeff f {i} ^ 2 := by
  classical
  unfold weightLevel
  rw [← Finset.sum_filter]
  have hsets :
      (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = 1) =
      Finset.univ.image (fun i : Fin n ↦ ({i} : Finset (Fin n))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hS
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS
      exact ⟨i, by simp⟩
    · rintro ⟨i, _, rfl⟩
      simp
  rw [hsets, Finset.sum_image (fun i _ j _ h ↦ Finset.singleton_injective h)]

/-- Correlation with a linear form is the weighted sum of singleton Fourier coefficients. -/
private lemma expect_mul_linear_form (f : BooleanFunc n) (b : Fin n → ℝ) :
    expect (fun x ↦ f x * ∑ i : Fin n, b i * boolToSign (x i)) =
      ∑ i : Fin n, b i * fourierCoeff f {i} := by
  simp only [expect, fourierCoeff, innerProduct, chiS_singleton, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

/-- Normalizing the degree-one part: if `W¹[g] > 0`, the coefficients `aᵢ = ĝ({i}) / sqrt W¹[g]`
form a unit vector whose Rademacher linear form has correlation exactly `sqrt W¹[g]` with `g`.
[OD14, §5.4, proofs of the Level-1 Inequality and Cor. 5.32] -/
lemma exists_unit_linear_form (g : BooleanFunc n) (hw : 0 < weightLevel 1 g) :
    ∃ a : Fin n → ℝ, ∑ i : Fin n, a i ^ 2 = 1 ∧
      expect (fun x ↦ g x * ∑ i : Fin n, a i * boolToSign (x i)) =
        Real.sqrt (weightLevel 1 g) := (by
  have hr : 0 < Real.sqrt (weightLevel 1 g) := Real.sqrt_pos.mpr hw
  have hroot := Real.sq_sqrt hw.le
  refine ⟨fun i ↦ fourierCoeff g {i} / Real.sqrt (weightLevel 1 g), ?_, ?_⟩
  · simp only [div_pow, ← Finset.sum_div, ← weightLevel_one_eq_sum_singleton, hroot]
    exact div_self hw.ne'
  · rw [expect_mul_linear_form]
    simp only [div_mul_eq_mul_div, ← sq, ← Finset.sum_div, ← weightLevel_one_eq_sum_singleton]
    rw [div_eq_iff hr.ne', ← sq, hroot]
)

/-! ## Subcubes and Hamming balls -/

/-- A codimension-`k` subcube indicator has expectation `2⁻ᵏ` and degree-one Fourier weight
`k 2⁻²ᵏ`. [OD14, Prop. 5.24]
The nonemptiness hypothesis `hJ` is not needed by the proof; it is kept to match the source.

**Proof sketch.** Expand the indicator as the product of the `k` one-coordinate indicators. Its
Fourier expansion has equal coefficients `2⁻ᵏ` on all subsets of the fixed coordinates; exactly `k`
of these subsets are singletons. -/
theorem subcube_degreeOne_weight (J : Finset (Fin n)) (b : Fin n → Bool) (hJ : J.Nonempty) :
    expect (subcubeIndicator J b) = 1 / (2 : ℝ) ^ J.card ∧
      weightLevel 1 (subcubeIndicator J b) = J.card / (2 : ℝ) ^ (2 * J.card) := by
  classical
  -- The product expansion of the indicator is a sum over subsets of the fixed coordinates.
  have hbit (u v : Bool) : 1 + boolToSign u * boolToSign v =
      if u = v then (2 : ℝ) else 0 := by
    cases u <;> cases v <;> norm_num [boolToSign]
  have hexpand (x : BoolCube n) :
      (∑ S ∈ J.powerset, chiS S b * chiS S x) =
        (2 : ℝ) ^ J.card * subcubeIndicator J b x := by
    simp only [chiS, ← Finset.prod_mul_distrib, ← Finset.prod_one_add, hbit]
    rw [Finset.prod_ite_zero]
    simp only [Finset.prod_const, subcubeIndicator]
    split_ifs <;> simp_all [eq_comm]
  have hrepr : subcubeIndicator J b = fun x ↦
      ∑ S ∈ J.powerset, (chiS S b / (2 : ℝ) ^ J.card) * chiS S x := by
    funext x
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, hexpand]
    field_simp
  -- Orthonormality reads off the coefficients of this expansion.
  have hcoeff (S : Finset (Fin n)) : fourierCoeff (subcubeIndicator J b) S =
      (if S ⊆ J then chiS S b else 0) / (2 : ℝ) ^ J.card := by
    rw [hrepr]
    unfold fourierCoeff innerProduct expect
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    simp_rw [mul_left_comm (uniformWeight n)]
    change (∑ T ∈ J.powerset, (chiS T b / (2 : ℝ) ^ J.card) *
      innerProduct (chiS T) (chiS S)) = _
    simp_rw [fourier_coeff_chi]
    simp [Finset.mem_powerset, ite_div]
  constructor
  · rw [← fourierCoeff_empty, hcoeff]
    simp
  · have hsq (S : Finset (Fin n)) : fourierCoeff (subcubeIndicator J b) S ^ 2 =
        if S ⊆ J then 1 / (2 : ℝ) ^ (2 * J.card) else 0 := by
      rw [hcoeff]
      split_ifs <;> simp [div_pow, chiS_sq_eq_one, pow_mul, mul_comm 2]
    simp_rw [weightLevel, hsq]
    have hsets : (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = 1 ∧ S ⊆ J) =
        J.powersetCard 1 := by
      ext S
      simp [Finset.mem_powersetCard, and_comm]
    simp_rw [← ite_and]
    rw [← Finset.sum_filter, hsets]
    simp [Finset.card_powersetCard, Nat.choose_one_right, div_eq_mul_inv]

/-- Normalized Hamming-ball indicators converge in mean to a Gaussian tail and in degree-one
weight to the square of the Gaussian density at the threshold. [OD14, Prop. 5.25]

**Proof sketch.** The central limit theorem gives convergence of the normalized Rademacher sum to a
standard Gaussian, proving the mean limit. Symmetry makes all singleton Fourier coefficients equal;
conditioning on one coordinate and applying the local CLT identifies their scaled limit as `φ(t)`.
-/
theorem hammingBall_degreeOne_limit (t : ℝ) :
    Filter.Tendsto (fun n : ℕ ↦ expect (hammingBallIndicator n t)) Filter.atTop
      (nhds (standardGaussianTail t)) ∧
    Filter.Tendsto (fun n : ℕ ↦ weightLevel 1 (hammingBallIndicator n t)) Filter.atTop
      (nhds (standardGaussianPDF t ^ 2)) := sorry

/-! ## The Level-1 and pi-over-two theorems -/

/-- The moment-generating function of a unit-variance Rademacher linear form is at most
`exp(t²/2)`, the finite-cube form of Hoeffding's lemma. [OD14, §5.4, Lemma 5.31 proof]

**Proof sketch.** The exponential of the linear form factors over the coordinates, so its
expectation is `∏ᵢ cosh(t aᵢ) ≤ ∏ᵢ exp((t aᵢ)²/2) = exp(t²/2)`. -/
lemma rademacher_mgf_le (a : Fin n → ℝ)
    (hnorm : ∑ i : Fin n, a i ^ 2 = 1) (t : ℝ) :
    expect (fun x ↦ Real.exp (t * ∑ i : Fin n, a i * boolToSign (x i))) ≤
      Real.exp (t ^ 2 / 2) := (by
  have hfactor : expect (fun x ↦ Real.exp (t * ∑ i : Fin n, a i * boolToSign (x i))) =
      ∏ i : Fin n, Real.cosh (t * a i) := by
    have hexp (x : BoolCube n) : Real.exp (t * ∑ i : Fin n, a i * boolToSign (x i)) =
        ∏ i : Fin n, Real.exp (t * a i * boolToSign (x i)) := by
      simp only [Finset.mul_sum, Real.exp_sum, mul_assoc]
    simp_rw [expect, uniformWeight, hexp]
    rw [← Fintype.prod_sum (fun i : Fin n ↦
      fun b : Bool ↦ Real.exp (t * a i * boolToSign b)),
      show (2 : ℝ)⁻¹ ^ n = ∏ _i : Fin n, (2 : ℝ)⁻¹ by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp [boolToSign, Real.cosh_eq]
    ring
  calc
    _ = ∏ i : Fin n, Real.cosh (t * a i) := hfactor
    _ ≤ ∏ i : Fin n, Real.exp ((t * a i) ^ 2 / 2) :=
      Finset.prod_le_prod (fun i _ ↦ (Real.cosh_pos _).le)
        (fun i _ ↦ Real.cosh_le_exp_half_sq _)
    _ = Real.exp (t ^ 2 / 2) := by
      rw [← Real.exp_sum, ← Finset.sum_div]
      simp only [mul_pow, ← Finset.mul_sum, hnorm, mul_one]
)

/-- The truncated first moment of a normalized Rademacher linear form has a Gaussian tail bound.
[OD14, Lemma 5.31]

**Proof sketch.** The moment-generating function of a normalized Rademacher sum is bounded by
`exp(t²/2)`. On the event `|ℓ| ≥ s`, bound `|ℓ|` by
`(s+1) exp(s(|ℓ|-s))`, then average the positive and negative exponential terms. -/
theorem linear_form_tail_expectation (a : Fin n → ℝ)
    (hnorm : ∑ i : Fin n, a i ^ 2 = 1) {s : ℝ} (hs : 1 ≤ s) :
    expect (fun x ↦ if s ≤ |∑ i : Fin n, a i * boolToSign (x i)| then
        |∑ i : Fin n, a i * boolToSign (x i)| else 0) ≤
      (2 * s + 2) * Real.exp (-s ^ 2 / 2) := by
  set L : BoolCube n → ℝ := fun x ↦ ∑ i : Fin n, a i * boolToSign (x i)
  set K : ℝ := (s + 1) * Real.exp (-s ^ 2)
  have hK : 0 ≤ K := by positivity
  -- On the event `y ≥ s`, the linear bound `y ≤ (s+1)(1 + (y-s))` is dominated exponentially.
  have htrunc (y : ℝ) (hy : s ≤ y) : y ≤ K * Real.exp (s * y) := by
    have hys : 0 ≤ y - s := by linarith
    have hre : K * Real.exp (s * y) = (s + 1) * Real.exp (s * (y - s)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    rw [hre]
    calc
      y ≤ (s + 1) * (1 + (y - s)) := by nlinarith
      _ ≤ (s + 1) * Real.exp (s * (y - s)) := by
        gcongr
        linarith [Real.add_one_le_exp (s * (y - s)), mul_le_mul_of_nonneg_right hs hys]
  have hpoint (y : ℝ) :
      (if s ≤ |y| then |y| else 0) ≤ K * (Real.exp (s * y) + Real.exp (-s * y)) := by
    split_ifs with hy
    · rcases le_total 0 y with hpos | hneg
      · rw [abs_of_nonneg hpos] at hy ⊢
        nlinarith [htrunc y hy, Real.exp_pos (-s * y)]
      · rw [abs_of_nonpos hneg] at hy ⊢
        have h := htrunc (-y) hy
        rw [show s * -y = -s * y by ring] at h
        nlinarith [Real.exp_pos (s * y)]
    · positivity
  have hmgf (t : ℝ) : expect (fun x ↦ Real.exp (t * L x)) ≤ Real.exp (t ^ 2 / 2) :=
    rademacher_mgf_le a hnorm t
  calc expect (fun x ↦ if s ≤ |L x| then |L x| else 0)
      ≤ expect (fun x ↦ K * (Real.exp (s * L x) + Real.exp (-s * L x))) :=
        expect_mono fun x ↦ hpoint (L x)
    _ = K * (expect (fun x ↦ Real.exp (s * L x)) + expect (fun x ↦ Real.exp (-s * L x))) := by
        rw [expect_const_mul, expect_add]
    _ ≤ K * (Real.exp (s ^ 2 / 2) + Real.exp (s ^ 2 / 2)) := by
        gcongr
        · exact hmgf s
        · simpa using hmgf (-s)
    _ = (2 * s + 2) * Real.exp (-s ^ 2 / 2) := by
        rw [mul_add, show K * Real.exp (s ^ 2 / 2) = (s + 1) * Real.exp (-s ^ 2 / 2) by
          rw [mul_assoc, ← Real.exp_add]; ring_nf]
        ring

/-- The degree-one Fourier weight of a `{0,1}`-valued function of mean `α ≤ 1/2` is at most a
universal constant times `α² log(1/α)`. [OD14, §5.4, Level-1 Inequality; Tal96]

**Proof sketch.** Normalize the degree-one Fourier part to an `L²`-unit linear form. Split its
correlation with `f` at a threshold `s`: the central part contributes at most `αs`, while
`linear_form_tail_expectation` controls the tail. Choosing `s ≍ sqrt(log(1/α))` gives the bound. -/
theorem levelOne_inequality :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (f : BooleanFunc n) (α : ℝ),
      (∀ x, f x = 0 ∨ f x = 1) → expect f = α → 0 < α → α ≤ 1 / 2 →
        weightLevel 1 f ≤ C * α ^ 2 * Real.log α⁻¹ := by
  refine ⟨50, by positivity, ?_⟩
  intro n f α hf hα hpos hhalf
  have hlog : (1 / 2 : ℝ) ≤ Real.log α⁻¹ := by
    have h := Real.add_one_le_exp (Real.log α)
    rw [Real.exp_log hpos] at h
    rw [Real.log_inv]
    linarith
  -- The threshold `s = sqrt(2 log(1/α))` satisfies `exp(-s²/2) = α`.
  set s : ℝ := Real.sqrt (2 * Real.log α⁻¹)
  have hs2 : s ^ 2 = 2 * Real.log α⁻¹ := Real.sq_sqrt (by linarith)
  have hs : 1 ≤ s := by nlinarith [Real.sqrt_nonneg (2 * Real.log α⁻¹)]
  have hexp : Real.exp (-s ^ 2 / 2) = α := by
    rw [hs2, show -(2 * Real.log α⁻¹) / 2 = Real.log α by rw [Real.log_inv]; ring,
      Real.exp_log hpos]
  rcases (weightLevel_nonneg 1 f).eq_or_lt with hw0 | hwpos
  · rw [← hw0]
    positivity
  obtain ⟨a, hnorm, hcorr⟩ := exists_unit_linear_form f hwpos
  set L : BoolCube n → ℝ := fun x ↦ ∑ i : Fin n, a i * boolToSign (x i)
  -- Split the correlation of `f` with `L` at the threshold `s`.
  have hpt (x : BoolCube n) :
      f x * L x ≤ s * f x + (if s ≤ |L x| then |L x| else 0) := by
    have := le_abs_self (L x)
    rcases hf x with hx | hx <;> rw [hx] <;> split_ifs <;> linarith
  have hbound : Real.sqrt (weightLevel 1 f) ≤ α * (3 * s + 2) := by
    calc
      Real.sqrt (weightLevel 1 f) = expect (fun x ↦ f x * L x) := hcorr.symm
      _ ≤ expect (fun x ↦ s * f x + if s ≤ |L x| then |L x| else 0) := expect_mono hpt
      _ = s * α + expect (fun x ↦ if s ≤ |L x| then |L x| else 0) := by
        rw [expect_add, expect_const_mul, hα]
      _ ≤ s * α + (2 * s + 2) * Real.exp (-s ^ 2 / 2) := by
        gcongr
        exact linear_form_tail_expectation a hnorm hs
      _ = α * (3 * s + 2) := by rw [hexp]; ring
  calc
    weightLevel 1 f = Real.sqrt (weightLevel 1 f) ^ 2 := (Real.sq_sqrt hwpos.le).symm
    _ ≤ (α * (3 * s + 2)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2
    _ ≤ (α * (5 * s)) ^ 2 := by gcongr; linarith
    _ = 50 * α ^ 2 * Real.log α⁻¹ := by rw [mul_pow, mul_pow, hs2]; ring

/-- A `±1`-valued function with all first-level coefficients at most `ε` has degree-one weight at
most `2/π + O(ε)`; near equality forces closeness to the threshold of its degree-one part.
[OD14, §5.4, The pi-over-two Theorem; KKMO07; MORS10]

**Proof sketch.** Normalize the degree-one part and correlate it with `f`. Theorem 5.16 bounds the
linear form's expected absolute value by `sqrt(2/π) + O(ε)`, yielding the weight bound. Near
equality
forces disagreement with its sign to occur only where the linear form is small; Berry-Esseen bounds
that small-ball probability by `O(sqrt ε)`. -/
theorem pi_over_two_theorem :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (f : BooleanFunc n) (ε : ℝ),
      isPmOne f → 0 ≤ ε → (∀ i : Fin n, |fourierCoeff f {i}| ≤ ε) →
        weightLevel 1 f ≤ 2 / Real.pi + C * ε ∧
        (2 / Real.pi - ε ≤ weightLevel 1 f →
          IsClose f (fun x ↦ thresholdSign (degreeOnePart f x)) (C * Real.sqrt ε)) := sorry

/-! ## A sharp FKN consequence -/

/-- `HasFKNClosenessBound C` asserts that first-level weight at least `1-δ` forces `Cδ`-closeness
to a dictator or negated dictator.

[OD14, §5.4, discussion preceding Thm. 5.33] -/
def HasFKNClosenessBound (C : ℝ) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (f : BooleanFunc n) (δ : ℝ),
    isPmOne f → 0 ≤ δ → δ ≤ 1 → 1 - δ ≤ weightLevel 1 f →
      ∃ i : Fin n, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ IsClose f (s • dictator i) (C * δ)

/-- A highly biased `±1`-valued function has small degree-one Fourier weight.
[OD14, Cor. 5.32]

**Proof sketch.** Replace `f` by the `{0,1}`-indicator of its minority value, whose mean is at
most `δ/2`. Normalize its degree-one coefficients to form a unit-variance Rademacher sum. An
exponential-moment bound controls its correlation with the indicator, giving the stronger
`2δ² log(2/δ)` bound; rescale the Fourier coefficients to recover `f`. -/
theorem biased_degreeOne_weight (f : BooleanFunc n) (hf : isPmOne f) {δ : ℝ}
    (hδ : 0 ≤ 1 - δ) (hbias : 1 - δ ≤ |expect f|) :
    weightLevel 1 f ≤ 4 * δ ^ 2 * Real.log (2 / δ) := by
  -- Step 1: pass to the indicator `g = (1 - σ f)/2` of the minority value, `σ = sign E[f]`.
  let σ : ℝ := thresholdSign (expect f)
  let g : BooleanFunc n := fun x ↦ (1 - σ * f x) / 2
  have hσsq : σ ^ 2 = 1 := by rcases thresholdSign_pm_one (expect f) with h | h <;> simp [σ, h]
  have hg (x : BoolCube n) : g x = 0 ∨ g x = 1 := by
    rcases hf x with hx | hx <;> rcases thresholdSign_pm_one (expect f) with h | h <;>
      simp [g, σ, hx, h]
  have hg0 (x : BoolCube n) : 0 ≤ g x := by rcases hg x with h | h <;> simp [h]
  have hmean : expect g = (1 - |expect f|) / 2 := by
    have hg' : g = fun x ↦ 2⁻¹ + (-(σ / 2)) * f x := funext fun x ↦ by ring
    rw [hg', expect_add, expect_const, expect_const_mul, ← mul_thresholdSign_self]
    ring
  have hbeta : expect g ≤ δ / 2 := by rw [hmean]; linarith
  -- The singleton coefficients of `g` are those of `f` scaled by `-σ/2`.
  have hcoef (i : Fin n) : fourierCoeff g {i} = -(σ / 2) * fourierCoeff f {i} := by
    have hchi : expect (fun x ↦ chiS {i} x) = 0 := by
      simpa [innerProduct, chiS_singleton] using fourier_coeff_chi ({i} : Finset (Fin n)) ∅
    have hg' : (fun x ↦ g x * chiS {i} x) =
        fun x ↦ 2⁻¹ * chiS {i} x + (-(σ / 2)) * (f x * chiS {i} x) := funext fun x ↦ by ring
    simp only [fourierCoeff, innerProduct]
    rw [hg', expect_add, expect_const_mul, expect_const_mul, hchi]
    ring
  have hweight : weightLevel 1 f = 4 * weightLevel 1 g := by
    rw [weightLevel_one_eq_sum_singleton f, weightLevel_one_eq_sum_singleton g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hcoef]
    linear_combination (-(fourierCoeff f {i}) ^ 2) * hσsq
  have hβnonneg : 0 ≤ expect g := expect_nonneg hg0
  rcases (show 0 ≤ δ by linarith).eq_or_lt with hδ0 | hδpos
  · -- An unbiased-free function is constant, so it has no degree-one weight.
    subst hδ0
    have hgzero : g = 0 := eq_zero_of_expect_eq_zero hg0 (by linarith)
    rw [hweight, hgzero]
    simp [weightLevel, fourierCoeff, innerProduct, expect]
  -- Step 2: the parameters `γ = δ/2`, `c = log(1/γ) ≥ 1/2`, and `t = sqrt(2c)`.
  set γ : ℝ := δ / 2 with hγdef
  have hγpos : 0 < γ := by positivity
  set c : ℝ := Real.log γ⁻¹ with hcdef
  have hc : (1 / 2 : ℝ) ≤ c := by
    have h := Real.add_one_le_exp (Real.log γ)
    rw [Real.exp_log hγpos] at h
    rw [hcdef, Real.log_inv]
    linarith
  have hcEq : c = Real.log (2 / δ) := by
    rw [hcdef, hγdef]
    congr 1
    field_simp
  have hcexp : Real.exp (-c) = γ := by rw [hcdef, Real.log_inv, neg_neg, Real.exp_log hγpos]
  set t : ℝ := Real.sqrt (2 * c)
  have ht2 : t ^ 2 = 2 * c := Real.sq_sqrt (by linarith)
  have htpos : 0 < t := Real.sqrt_pos.mpr (by linarith)
  rcases (weightLevel_nonneg 1 g).eq_or_lt with hw0 | hwpos
  · rw [hweight, ← hw0, ← hcEq]
    nlinarith [sq_nonneg δ]
  -- Step 3: correlate `g` with the normalized degree-one linear form `L`.
  obtain ⟨a, hnorm, hcorr⟩ := exists_unit_linear_form g hwpos
  set r : ℝ := Real.sqrt (weightLevel 1 g)
  set L : BoolCube n → ℝ := fun x ↦ ∑ i : Fin n, a i * boolToSign (x i)
  -- Pointwise, `t g L ≤ (t²/2 + c - 1) g + γ exp(-t²/2) exp(tL)` since `1 + u ≤ exp u`.
  have hpt (x : BoolCube n) :
      t * (g x * L x) ≤
        (t ^ 2 / 2 + c - 1) * g x + γ * Real.exp (-t ^ 2 / 2) * Real.exp (t * L x) := by
    have hex : γ * Real.exp (-t ^ 2 / 2) * Real.exp (t * L x) =
        Real.exp (t * L x - t ^ 2 / 2 - c) := by
      rw [← hcexp, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    rcases hg x with hx | hx
    · rw [hx]
      simp only [mul_zero, zero_mul, zero_add]
      positivity
    · rw [hx, hex]
      linarith [Real.add_one_le_exp (t * L x - t ^ 2 / 2 - c)]
  have hmgf : expect (fun x ↦ Real.exp (t * L x)) ≤ Real.exp (t ^ 2 / 2) :=
    rademacher_mgf_le a hnorm t
  have hmain : t * r ≤ 2 * γ * c := by
    calc
      t * r = expect (fun x ↦ t * (g x * L x)) := by rw [expect_const_mul, ← hcorr]
      _ ≤ expect (fun x ↦ (t ^ 2 / 2 + c - 1) * g x +
            γ * Real.exp (-t ^ 2 / 2) * Real.exp (t * L x)) := expect_mono hpt
      _ = (t ^ 2 / 2 + c - 1) * expect g +
            γ * Real.exp (-t ^ 2 / 2) * expect (fun x ↦ Real.exp (t * L x)) := by
        rw [expect_add, expect_const_mul, expect_const_mul]
      _ ≤ (t ^ 2 / 2 + c - 1) * γ + γ * Real.exp (-t ^ 2 / 2) * Real.exp (t ^ 2 / 2) := by
        gcongr
        rw [ht2]
        linarith
      _ = 2 * γ * c := by
        rw [mul_assoc γ, ← Real.exp_add, show -t ^ 2 / 2 + t ^ 2 / 2 = 0 by ring, Real.exp_zero,
          ht2]
        ring
  have hrbound : r ≤ γ * t := by
    refine le_of_mul_le_mul_left ?_ htpos
    nlinarith
  calc
    weightLevel 1 f = 4 * r ^ 2 := by rw [hweight, Real.sq_sqrt hwpos.le]
    _ ≤ 4 * (γ * t) ^ 2 := by gcongr
    _ = 2 * δ ^ 2 * c := by rw [mul_pow, ht2]; ring
    _ ≤ 4 * δ ^ 2 * Real.log (2 / δ) := by
      rw [← hcEq]
      nlinarith [mul_nonneg (sq_nonneg δ) (show 0 ≤ c by linarith)]

/-- Any linear FKN closeness bound `Cδ` self-improves to the essentially optimal bound
`δ/4 + 16 C² δ² max(log(1/(Cδ)),1)`. [OD14, Thm. 5.33; JOW12]

**Proof sketch.** Start with the dictator supplied by the assumed FKN bound and restrict the
function on that coordinate. Each restriction is highly biased, so `biased_degreeOne_weight`
controls all remaining first-level coefficients. Parseval then sharpens the dictator coefficient,
which translates directly into the improved disagreement probability. -/
theorem fkn_closeness_improvement {C : ℝ} (hC : 1 ≤ C) (hFKN : HasFKNClosenessBound C) :
    ∀ {n : ℕ}, 0 < n → ∀ (f : BooleanFunc n) (δ : ℝ),
      isPmOne f → 0 ≤ δ → δ ≤ 1 → 1 - δ ≤ weightLevel 1 f →
        ∃ i : Fin n, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
          IsClose f (s • dictator i)
            (δ / 4 + 16 * C ^ 2 * δ ^ 2 * max (Real.log (1 / (C * δ))) 1) := by
  classical
  intro n hn f δ hf hδ hδ1 hw
  obtain ⟨i, s, hs, hclose⟩ := hFKN hn f δ hf hδ hδ1 hw
  refine ⟨i, s, hs, ?_⟩
  let ε : ℝ := C * δ
  let η : ℝ := disagreementProbability f (s • dictator i)
  have hη : η ≤ ε := hclose
  have hε : 0 ≤ ε := mul_nonneg (by linarith) hδ
  have hη0 : 0 ≤ η := by
    change 0 ≤ expect (fun x => if f x = (s • dictator i) x then (0 : ℝ) else 1)
    exact expect_nonneg (fun x => by split_ifs <;> norm_num)
  have hη1 : η ≤ 1 := by
    calc
      η ≤ expect (fun _ : BoolCube n => (1 : ℝ)) := by
        apply expect_mono
        intro x
        split_ifs <;> norm_num
      _ = 1 := expect_const 1
  by_cases hεzero : ε = 0
  · have hδzero : δ = 0 := by
      have h : C * δ = 0 := hεzero
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact h
    change η ≤ _
    simp [ε, hδzero] at hη ⊢
    exact hη
  have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hεzero)
  by_cases hlarge : (1 / 4 : ℝ) ≤ ε
  · change η ≤ _
    have hM : 1 ≤ max (Real.log (1 / (C * δ))) 1 := le_max_right _ _
    have hsq : 1 ≤ 16 * ε ^ 2 := by nlinarith [hlarge, hεpos.le]
    have hprod : 1 ≤ 16 * C ^ 2 * δ ^ 2 * max (Real.log (1 / (C * δ))) 1 := by
      calc
        1 ≤ 16 * ε ^ 2 := hsq
        _ = 16 * C ^ 2 * δ ^ 2 := by dsimp [ε]; ring
        _ ≤ 16 * C ^ 2 * δ ^ 2 * max (Real.log (1 / (C * δ))) 1 := by
          nlinarith [mul_nonneg (show 0 ≤ 16 * C ^ 2 * δ ^ 2 by positivity)
            (sub_nonneg.mpr hM)]
    linarith
  have hsmall : ε < 1 / 4 := lt_of_not_ge hlarge
  have hu (x : BoolCube n) (b : Bool) :
      Function.update x i b = if x i = b then x else flipBit x i := by
    split_ifs with h
    · rw [← h, Function.update_eq_self]
    · rw [flipBit, show b = !x i by cases b <;> simp_all]
  have havg (g : BooleanFunc n) : expect (expectationOperator i g) = expect g := by
    have key (x : BoolCube n) :
        expectationOperator i g x = (g x + g (flipBit x i)) / 2 := by
      cases hx : x i <;> simp [expectationOperator, hu, hx] <;> ring
    have hflip : ∑ x : BoolCube n, g (flipBit x i) = ∑ x : BoolCube n, g x :=
      Equiv.sum_comp (Function.Involutive.toPerm (fun x => flipBit x i)
        (fun x => flipBit_flipBit x i)) g
    simp only [expect, key, ← Finset.sum_div, Finset.sum_add_distrib, hflip]
    ring
  have hsplit (g : BooleanFunc n) :
      expect g = (expect (fun x => g (Function.update x i false)) +
        expect (fun x => g (Function.update x i true))) / 2 := by
    rw [← havg g]
    change expect (fun x => (g (Function.update x i false) +
      g (Function.update x i true)) / 2) = _
    simp only [div_eq_mul_inv, mul_comm, expect_const_mul, expect_add]
  let r (b : Bool) : BooleanFunc n := fun x => f (Function.update x i b)
  let d (b : Bool) : BooleanFunc n := fun x =>
    if r b x = s * boolToSign b then 0 else 1
  have hηavg : η = (expect (d false) + expect (d true)) / 2 := by
    have h := hsplit (fun x => if f x = (s • dictator i) x then (0 : ℝ) else 1)
    simpa [η, disagreementProbability, d, r, dictator, Pi.smul_apply, smul_eq_mul] using h
  have hd0 (b : Bool) : 0 ≤ expect (d b) :=
    expect_nonneg (fun x => by dsimp [d]; split_ifs <;> norm_num)
  have hdb (b : Bool) : expect (d b) ≤ 2 * ε := by
    cases b <;> linarith [hηavg, hd0 false, hd0 true, hη]
  have hpt (b : Bool) (x : BoolCube n) :
      (s * boolToSign b) * r b x = 1 - 2 * d b x := by
    rcases hf (Function.update x i b) with hx | hx <;>
      rcases hs with hs | hs <;> cases b <;>
      norm_num [d, r, hx, hs, boolToSign]
  have hmean (b : Bool) :
      (s * boolToSign b) * expect (r b) = 1 - 2 * expect (d b) := by
    calc
      _ = expect (fun x => (s * boolToSign b) * r b x) :=
        (expect_const_mul _ _).symm
      _ = expect (fun x => 1 - 2 * d b x) := by
        congr 1
        funext x
        exact hpt b x
      _ = _ := by rw [expect_sub, expect_const, expect_const_mul]
  have hbias (b : Bool) : 1 - 4 * ε ≤ |expect (r b)| := by
    have hsabs : |s * boolToSign b| = 1 := by
      rcases hs with hs | hs <;> cases b <;> norm_num [hs, boolToSign]
    calc
      1 - 4 * ε ≤ (s * boolToSign b) * expect (r b) := by
        rw [hmean]
        linarith [hdb b]
      _ ≤ |(s * boolToSign b) * expect (r b)| := le_abs_self _
      _ = |expect (r b)| := by rw [abs_mul, hsabs, one_mul]
  have hbound (b : Bool) :
      weightLevel 1 (r b) ≤ 64 * ε ^ 2 * Real.log (1 / (2 * ε)) := by
    have h := biased_degreeOne_weight (r b) (fun x => hf _)
      (δ := 4 * ε) (by linarith [hsmall, hε]) (hbias b)
    have heq : (2 : ℝ) / (4 * ε) = 1 / (2 * ε) := by
      field_simp [ne_of_gt hεpos] <;> ring
    rw [heq] at h
    convert h using 1 <;> ring
  have hcoef (j : Fin n) (hji : j ≠ i) :
      fourierCoeff f {j} =
        (fourierCoeff (r false) {j} + fourierCoeff (r true) {j}) / 2 := by
    have h := hsplit (fun x => f x * chiS {j} x)
    simpa [fourierCoeff, innerProduct, r, chiS_singleton,
      Function.update_of_ne hji] using h
  have hother :
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, fourierCoeff f {j} ^ 2 ≤
        64 * ε ^ 2 * Real.log (1 / (2 * ε)) := by
    calc
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          (fourierCoeff (r false) {j} ^ 2 + fourierCoeff (r true) {j} ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_erase] at hj
        rw [hcoef j hj.1]
        nlinarith [sq_nonneg
          (fourierCoeff (r false) {j} - fourierCoeff (r true) {j})]
      _ ≤ ∑ j : Fin n,
          (fourierCoeff (r false) {j} ^ 2 + fourierCoeff (r true) {j} ^ 2) / 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
        intro j hj hj'
        positivity
      _ = (weightLevel 1 (r false) + weightLevel 1 (r true)) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib,
          ← weightLevel_one_eq_sum_singleton, ← weightLevel_one_eq_sum_singleton]
      _ ≤ 64 * ε ^ 2 * Real.log (1 / (2 * ε)) := by
        linarith [hbound false, hbound true]
  have hselected : s * fourierCoeff f {i} = 1 - 2 * η := by
    have hpt' (x : BoolCube n) :
        s * (f x * chiS {i} x) = 1 - 2 *
          (if f x = (s • dictator i) x then (0 : ℝ) else 1) := by
      rcases hf x with hx | hx <;> rcases hs with hs | hs <;>
        cases hxi : x i <;>
        norm_num [hx, hs, chiS_singleton, dictator, boolToSign, hxi]
    rw [fourierCoeff, innerProduct, ← expect_const_mul]
    simp_rw [hpt']
    rw [expect_sub, expect_const, expect_const_mul]
    rfl
  have hs2 : s ^ 2 = 1 := by rcases hs with hs | hs <;> rw [hs] <;> norm_num
  have hselected2 : fourierCoeff f {i} ^ 2 = (1 - 2 * η) ^ 2 := by
    calc
      _ = (s * fourierCoeff f {i}) ^ 2 := by rw [mul_pow, hs2, one_mul]
      _ = _ := by rw [hselected]
  have hW : 1 - δ ≤ (1 - 2 * η) ^ 2 +
      64 * ε ^ 2 * Real.log (1 / (2 * ε)) := by
    calc
      1 - δ ≤ weightLevel 1 f := hw
      _ = fourierCoeff f {i} ^ 2 +
          ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            fourierCoeff f {j} ^ 2 := by
        rw [weightLevel_one_eq_sum_singleton]
        exact (Finset.add_sum_erase (Finset.univ : Finset (Fin n))
          (fun j => fourierCoeff f {j} ^ 2) (Finset.mem_univ i)).symm
      _ ≤ _ := by rw [hselected2]; exact add_le_add_left hother _
  have hraw : η ≤ δ / 4 + η ^ 2 +
      16 * ε ^ 2 * Real.log (1 / (2 * ε)) := by nlinarith [hW]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hlogid : Real.log (1 / (2 * ε)) = Real.log (1 / ε) - Real.log 2 := by
    rw [show (1 : ℝ) / (2 * ε) = (1 / ε) / 2 by
      field_simp [ne_of_gt hεpos]]
    exact Real.log_div (by positivity) (by norm_num)
  have hηsq : η ^ 2 ≤ ε ^ 2 := by nlinarith [hη, hη0, hε]
  have hlogbound : η ^ 2 ≤ 16 * ε ^ 2 * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 16 * ε ^ 2 by positivity)
    nlinarith [hηsq, h]
  change η ≤ δ / 4 + 16 * C ^ 2 * δ ^ 2 *
    max (Real.log (1 / (C * δ))) 1
  rw [show 16 * C ^ 2 * δ ^ 2 = 16 * ε ^ 2 by dsimp [ε]; ring]
  calc
    η ≤ δ / 4 + η ^ 2 + 16 * ε ^ 2 * Real.log (1 / (2 * ε)) := hraw
    _ ≤ δ / 4 + 16 * ε ^ 2 * Real.log (1 / ε) := by
      rw [hlogid]
      nlinarith [hlogbound]
    _ ≤ δ / 4 + 16 * ε ^ 2 *
        max (Real.log (1 / (C * δ))) 1 := by
      gcongr
      change Real.log (1 / (C * δ)) ≤ _
      exact le_max_left _ _


end ThresholdFunctions
end BooleanAnalysis
