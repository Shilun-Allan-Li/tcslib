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

This file contains definitions only. The source results are stated in the downstream files.

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

end ThresholdFunctions
end BooleanAnalysis
