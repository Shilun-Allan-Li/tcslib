import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
import TCSlib.BooleanAnalysis.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Threshold functions: basic definitions

This file introduces representations of linear and polynomial threshold functions on the Boolean
cube. It also gathers the Fourier and metric notation used throughout the Chapter 5 development.

## Main definitions

* `MultilinearPolynomial`: a multilinear polynomial in the Walsh basis.
* `IsPolynomialThreshold`: the predicate that a Boolean function is a degree-bounded PTF.
* `IsLinearThreshold`: the specialization to degree one.
* `IsMajorityOfSignedParities`: majority representations by signed Walsh characters.
* `fourierWeightUpTo`, `fourierWeightAbove`, and `spectralOneNorm`.
* `noiseStability`, `noiseSensitivity`, and `disagreementProbability`.

## Main results

The source results are stated in the downstream files. This file only adds elementary helper
lemmas used throughout the chapter:

* `expect_mono`, `expect_nonneg`, `expect_add`, `expect_const_mul`: linearity and monotonicity of
  the uniform expectation.
* `mul_thresholdSign_self`, `thresholdSign_mono`, `thresholdSign_eq_of_abs_sub_lt_one`: basic
  properties of the threshold sign.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Chapter 5.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

variable {n : ℕ}

/-! ## Multilinear polynomials and threshold representations -/

/-- A multilinear polynomial on the Boolean cube, represented by its Walsh-basis coefficients.

[OD14, §5.1, Def. 5.4] -/
abbrev MultilinearPolynomial (n : ℕ) := Finset (Fin n) → ℝ

/-- The value of a multilinear polynomial at a Boolean-cube point.

[OD14, §5.1, Def. 5.4] -/
noncomputable def MultilinearPolynomial.eval (p : MultilinearPolynomial n) (x : BoolCube n) : ℝ :=
  ∑ S : Finset (Fin n), p S * chiS S x

/-- A multilinear polynomial has degree at most `k` when coefficients above level `k` vanish.

[OD14, §5.1, Def. 5.4] -/
def MultilinearPolynomial.HasDegreeAtMost (p : MultilinearPolynomial n) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), k < S.card → p S = 0

/-- The sign convention used for threshold functions: zero is assigned sign `1`.

[OD14, §5.1, Eq. (5.1)] -/
noncomputable def thresholdSign (r : ℝ) : ℝ :=
  if 0 ≤ r then 1 else -1

/-- The Boolean function obtained by taking the sign of a multilinear polynomial.

[OD14, §5.1, Def. 5.4] -/
noncomputable def MultilinearPolynomial.threshold (p : MultilinearPolynomial n) : BooleanFunc n :=
  fun x ↦ thresholdSign (p.eval x)

/-- A polynomial threshold representation of `f` consists of a polynomial whose sign is `f`.

[OD14, §5.1, Def. 5.4] -/
def IsPolynomialThresholdRepresentation (f : BooleanFunc n) (p : MultilinearPolynomial n) : Prop :=
  p.threshold = f

/-- A Boolean function is a degree-`k` polynomial threshold function when it is represented by the
sign of a multilinear polynomial of degree at most `k`.

[OD14, §5.1, Def. 5.4] -/
def IsPolynomialThreshold (f : BooleanFunc n) (k : ℕ) : Prop :=
  ∃ p : MultilinearPolynomial n,
    p.HasDegreeAtMost k ∧ IsPolynomialThresholdRepresentation f p

/-- A linear threshold function is a polynomial threshold function of degree at most one.

[OD14, §5.1, Eq. (5.1)] -/
def IsLinearThreshold (f : BooleanFunc n) : Prop :=
  IsPolynomialThreshold f 1

/-- An unbiased linear threshold representation has no constant coefficient and its defining
linear form never vanishes on the Boolean cube.

[OD14, §5.2, Thm. 5.17] -/
def IsHomogeneousLinearThresholdRepresentation
    (f : BooleanFunc n) (a : Fin n → ℝ) : Prop :=
  f = (fun x ↦ thresholdSign (∑ i : Fin n, a i * boolToSign (x i))) ∧
    ∀ x : BoolCube n, ∑ i : Fin n, a i * boolToSign (x i) ≠ 0

/-- A function is a majority of `s` parities or negated parities when it is the sign of an
unweighted sum of `s` signed Walsh characters.

[OD14, Cor. 5.13] -/
def IsMajorityOfSignedParities (f : BooleanFunc n) (s : ℕ) : Prop :=
  ∃ sets : Fin s → Finset (Fin n), ∃ signs : Fin s → ℝ,
    (∀ j, signs j = 1 ∨ signs j = -1) ∧
      f = fun x ↦ thresholdSign (∑ j : Fin s, signs j * chiS (sets j) x)

/-- The support of a multilinear polynomial is the set of monomials with nonzero coefficient.

[OD14, §5.1, Def. 5.7] -/
noncomputable def MultilinearPolynomial.support (p : MultilinearPolynomial n) :
    Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ p S ≠ 0

/-- The sparsity of a polynomial is the number of monomials with nonzero coefficient.

[OD14, §5.1, Def. 5.7] -/
noncomputable def MultilinearPolynomial.sparsity (p : MultilinearPolynomial n) : ℕ :=
  p.support.card

/-! ## Fourier weights and norms -/

/-- The Fourier weight of `f` on levels at most `k`.

[OD14, §5.1] -/
noncomputable def fourierWeightUpTo (k : ℕ) (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), if S.card ≤ k then fourierCoeff f S ^ 2 else 0

/-- The Fourier weight of `f` on levels strictly above `k`.

[OD14, §5.3] -/
noncomputable def fourierWeightAbove (k : ℕ) (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), if k < S.card then fourierCoeff f S ^ 2 else 0

/-- The Fourier spectral one-norm `∑_S |f̂(S)|`.

[OD14, §5.1, Thm. 5.12] -/
noncomputable def spectralOneNorm (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), |fourierCoeff f S|

/-- The degree-one part of a Boolean function's Fourier expansion.

[OD14, §5.4] -/
noncomputable def degreeOnePart (f : BooleanFunc n) : BooleanFunc n :=
  fun x ↦ ∑ i : Fin n, fourierCoeff f {i} * chiS {i} x

/-- The largest absolute value of an individual influence.

[OD14, §5.2, Majority Is Stablest] -/
noncomputable def maxInfluence (f : BooleanFunc n) : ℝ :=
  sSup (Set.range fun i : Fin n ↦ |influence i f|)

/-! ## Distance, stability, and sensitivity -/

/-- The uniform probability that two functions disagree on the Boolean cube.

[OD14, §3.1] -/
noncomputable def disagreementProbability (f g : BooleanFunc n) : ℝ :=
  expect fun x ↦ if f x = g x then 0 else 1

/-- Two functions are `ε`-close when their uniform disagreement probability is at most `ε`.

[OD14, §3.1] -/
def IsClose (f g : BooleanFunc n) (ε : ℝ) : Prop :=
  disagreementProbability f g ≤ ε

/-- The supremum norm of a function on the finite Boolean cube.

[OD14, §5.1, Thm. 5.12] -/
noncomputable def supNorm (f : BooleanFunc n) : ℝ :=
  sSup (Set.range fun x : BoolCube n ↦ |f x|)

/-- The noise stability of `f` at correlation `ρ`.

[OD14, §2.4] -/
noncomputable def noiseStability (ρ : ℝ) (f : BooleanFunc n) : ℝ :=
  innerProduct f (noiseOp ρ f)

/-- The noise sensitivity at bit-flip probability `δ`, expressed through stability at
correlation `1 - 2δ`. This total real-valued extension agrees with disagreement probability for
`±1`-valued functions, which are the functions to which Chapter 5 applies it.

[OD14, §2.4] -/
noncomputable def noiseSensitivity (δ : ℝ) (f : BooleanFunc n) : ℝ :=
  (1 - noiseStability (1 - 2 * δ) f) / 2

/-! ## Canonical functions used by the chapter -/

/-- The inner-product-mod-two function on two `n`-bit blocks, in the `±1` convention.

[OD14, §5.1, Cor. 5.11] -/
noncomputable def innerProductModTwo (n : ℕ) : BooleanFunc (n + n) :=
  fun x ↦ ∏ i : Fin n,
    if x (Fin.castAdd n i) && x (Fin.natAdd n i) then (-1 : ℝ) else 1

/-- The indicator of the subcube fixing the coordinates in `J` to the pattern `b`.

[OD14, §5.4, Prop. 5.24] -/
noncomputable def subcubeIndicator (J : Finset (Fin n)) (b : Fin n → Bool) : BooleanFunc n :=
  fun x ↦ if ∀ i ∈ J, x i = b i then 1 else 0

/-- The Hamming-ball halfspace with normalized threshold `t`.

[OD14, §5.4, Prop. 5.25] -/
noncomputable def hammingBallIndicator (n : ℕ) (t : ℝ) : BooleanFunc n :=
  fun x ↦
    if t ≤ (∑ i : Fin n, boolToSign (x i)) / Real.sqrt n then 1 else 0

/-! ## Elementary lemmas

Small facts about the uniform expectation, the threshold sign, and the spectral one-norm that are
used throughout the chapter. -/

/-- The uniform expectation is monotone. -/
lemma expect_mono {f g : BooleanFunc n} (h : ∀ x, f x ≤ g x) : expect f ≤ expect g := by
  rw [expect_eq_fintypeExpect, expect_eq_fintypeExpect]
  exact Finset.expect_le_expect fun x _ ↦ h x

/-- The uniform expectation of a nonnegative function is nonnegative. -/
lemma expect_nonneg {f : BooleanFunc n} (h : ∀ x, 0 ≤ f x) : 0 ≤ expect f := by
  rw [expect_eq_fintypeExpect]
  exact Finset.expect_nonneg fun x _ ↦ h x

/-- The uniform expectation of a constant function is that constant. -/
@[simp]
lemma expect_const (c : ℝ) : expect (fun _ : BoolCube n ↦ c) = c := by
  rw [expect_eq_fintypeExpect]
  exact Fintype.expect_const c

/-- The uniform expectation is additive. -/
lemma expect_add (f g : BooleanFunc n) :
    expect (fun x ↦ f x + g x) = expect f + expect g := by
  simp only [expect, Finset.sum_add_distrib, mul_add]

/-- The uniform expectation commutes with scalar multiplication. -/
lemma expect_const_mul (c : ℝ) (f : BooleanFunc n) :
    expect (fun x ↦ c * f x) = c * expect f := by
  simp only [expect, ← Finset.mul_sum]
  ring

/-- The uniform expectation commutes with negation. -/
lemma expect_neg (f : BooleanFunc n) : expect (fun x ↦ -f x) = -expect f := by
  simpa using expect_const_mul (-1) f

/-- The uniform expectation commutes with subtraction. -/
lemma expect_sub (f g : BooleanFunc n) :
    expect (fun x ↦ f x - g x) = expect f - expect g := by
  simp only [sub_eq_add_neg, expect_add, expect_neg]

/-- A nonnegative function with zero expectation vanishes identically. -/
lemma eq_zero_of_expect_eq_zero {f : BooleanFunc n} (h : ∀ x, 0 ≤ f x) (h0 : expect f = 0) :
    f = 0 :=
  (Fintype.expect_eq_zero_iff_of_nonneg h).mp (by rwa [← expect_eq_fintypeExpect])

/-- The threshold sign of a nonnegative number is `1`. -/
@[simp]
lemma thresholdSign_of_nonneg {r : ℝ} (h : 0 ≤ r) : thresholdSign r = 1 := if_pos h

/-- The threshold sign of a negative number is `-1`. -/
@[simp]
lemma thresholdSign_of_neg {r : ℝ} (h : r < 0) : thresholdSign r = -1 := if_neg (not_le.mpr h)

/-- The threshold sign takes only the values `1` and `-1`. -/
lemma thresholdSign_pm_one (r : ℝ) : thresholdSign r = 1 ∨ thresholdSign r = -1 := by
  unfold thresholdSign; split_ifs <;> simp

/-- The threshold sign has absolute value one. -/
@[simp]
lemma abs_thresholdSign (r : ℝ) : |thresholdSign r| = 1 := by
  rcases thresholdSign_pm_one r with h | h <;> simp [h]

/-- Multiplying a number by its threshold sign gives its absolute value. -/
lemma mul_thresholdSign_self (r : ℝ) : r * thresholdSign r = |r| := by
  rcases le_or_gt 0 r with h | h
  · simp [h, abs_of_nonneg h]
  · simp [h, abs_of_neg h]

/-- The absolute value of a number times its threshold sign is the number itself. -/
lemma abs_mul_thresholdSign (r : ℝ) : |r| * thresholdSign r = r := by
  rcases le_or_gt 0 r with h | h
  · simp [h, abs_of_nonneg h]
  · simp [h, abs_of_neg h]

/-- The threshold sign is monotone. -/
lemma thresholdSign_mono {r s : ℝ} (h : r ≤ s) : thresholdSign r ≤ thresholdSign s := by
  rcases le_or_gt 0 r with hr | hr
  · rw [thresholdSign_of_nonneg hr, thresholdSign_of_nonneg (hr.trans h)]
  · rw [thresholdSign_of_neg hr]
    rcases thresholdSign_pm_one s with hs | hs <;> norm_num [hs]

/-- A positive rescaling does not change the threshold sign. -/
lemma thresholdSign_mul_of_pos {c : ℝ} (hc : 0 < c) (r : ℝ) :
    thresholdSign (c * r) = thresholdSign r := by
  unfold thresholdSign
  congr 1
  exact propext ⟨fun h ↦ nonneg_of_mul_nonneg_right (by linarith) hc, fun h ↦ by positivity⟩

/-- A real number at distance less than one from a sign `y = ±1` has threshold sign `y`. -/
lemma thresholdSign_eq_of_abs_sub_lt_one {y r : ℝ} (hy : y = 1 ∨ y = -1) (h : |y - r| < 1) :
    thresholdSign r = y := by
  rcases abs_lt.mp h with ⟨h1, h2⟩
  rcases hy with rfl | rfl
  · exact thresholdSign_of_nonneg (by linarith)
  · exact thresholdSign_of_neg (by linarith)

/-- The threshold of any real function on the cube is `±1`-valued. -/
lemma isPmOne_thresholdSign (g : BoolCube n → ℝ) :
    isPmOne (fun x ↦ thresholdSign (g x)) := fun _ ↦ thresholdSign_pm_one _

/-- The Fourier spectral one-norm is nonnegative. -/
lemma spectralOneNorm_nonneg (f : BooleanFunc n) : 0 ≤ spectralOneNorm f :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

end ThresholdFunctions
end BooleanAnalysis
