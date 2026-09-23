import Mathlib.Algebra.Order.Floor.Ring
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier theory of threshold functions

This file states the Chapter 5 results relating polynomial threshold representations to low-degree
Fourier coefficients, Fourier weight, and polynomial sparsity.

## Main definitions

The representation and Fourier-weight definitions are imported from `ThresholdFunctions.Basic`.

## Main results

* `chow_theorem`: an LTF is determined by its degree-zero and degree-one coefficients.
* `ptf_chow_theorem`: a degree-`k` PTF is determined by coefficients through degree `k`.
* `ptf_low_degree_weight`: a degree-`k` PTF has low-degree weight at least `exp (-2k)`.
* `ptf_support_fourier_mass`: a PTF support carries Fourier one-mass at least one.
* `sparse_polynomial_approximation`: small spectral one-norm gives a sparse approximation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Chapter 5.
* [Cho61] C.-K. Chow, On the characterization of threshold functions, 1961.
* [Bru90] J. Bruck, Harmonic analysis of polynomial threshold functions, 1990.
* [GL94] C. Gotsman and N. Linial, Spectral properties of threshold functions, 1994.
* [BS92] J. Bruck and R. Smolensky, Polynomial threshold functions and sparse polynomials, 1992.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

variable {n k : ℕ}

/-! ## Chow-type uniqueness theorems -/

/-- A linear threshold function is uniquely determined among all `±1`-valued functions by its
Fourier coefficients in degrees zero and one. [OD14, Thm. 5.1]

**Proof sketch.** Choose a nonvanishing affine separator `ℓ` for `f`. Pointwise,
`f(x)ℓ(x) = |ℓ(x)| ≥ g(x)ℓ(x)`, with equality exactly where `f(x) = g(x)`. Plancherel and the
equality of the degree-at-most-one coefficients force equality of the two expectations, hence
pointwise equality. -/
theorem chow_theorem {f g : BooleanFunc n} (hf : IsLinearThreshold f) (hfb : isPmOne f)
    (hgb : isPmOne g)
    (hcoeff : ∀ S : Finset (Fin n), S.card ≤ 1 → fourierCoeff g S = fourierCoeff f S) :
    g = f := sorry

/-- A degree-`k` polynomial threshold function is uniquely determined among all `±1`-valued
functions by its Fourier coefficients through degree `k`. [OD14, Thm. 5.8; Bru90]

**Proof sketch.** Repeat Chow's separating-polynomial argument with a nonvanishing degree-`k`
representing polynomial. Plancherel reduces both correlations to coefficients of degree at most
`k`, where the two functions agree by hypothesis. -/
theorem ptf_chow_theorem {f g : BooleanFunc n} (hf : IsPolynomialThreshold f k)
    (hfb : isPmOne f) (hgb : isPmOne g)
    (hcoeff : ∀ S : Finset (Fin n), S.card ≤ k → fourierCoeff g S = fourierCoeff f S) :
    g = f := sorry

/-! ## Low-degree approximation and weight -/

/-- Every Boolean function is close to a PTF whose degree is the reciprocal noise scale.
[OD14, Prop. 5.6]

**Proof sketch.** Truncate the Fourier expansion above degree `⌊1/δ⌋`. The Fourier tail is bounded
by three times the noise sensitivity, and taking the sign of the truncation can only decrease the
pointwise disagreement with the original Boolean function. -/
theorem close_to_low_degree_ptf (f : BooleanFunc n) (hf : isPmOne f) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ g : BooleanFunc n,
      IsPolynomialThreshold g (Nat.floor δ⁻¹) ∧
        IsClose f g (3 * noiseSensitivity δ f) := sorry

/-- Every linear threshold function has at least one half of its Fourier weight in degrees zero and
one. [OD14, Thm. 5.2; GL94]

**Proof sketch.** Correlate the function with a normalized affine separator, project the correlation
onto degrees zero and one, and apply Cauchy-Schwarz. The sharp Khintchine-Kahane lower bound for the
separator's `L¹` norm yields the factor `1/2`. -/
theorem ltf_low_degree_weight {f : BooleanFunc n} (hf : IsLinearThreshold f)
    (hfb : isPmOne f) :
    1 / 2 ≤ fourierWeightUpTo 1 f := sorry

/-- A degree-`k` polynomial threshold function has Fourier weight at least `exp (-2k)` through
degree `k`. [OD14, Thm. 5.9; GL94]

**Proof sketch.** Correlate `f` with a degree-`k` representing polynomial and use Cauchy-Schwarz on
the low-degree projection. The hypercontractive estimate `‖p‖₂ ≤ exp(k) ‖p‖₁` supplies the stated
exponential lower bound. -/
theorem ptf_low_degree_weight {f : BooleanFunc n} (hf : IsPolynomialThreshold f k)
    (hfb : isPmOne f) :
    Real.exp (-2 * (k : ℝ)) ≤ fourierWeightUpTo k f := sorry

/-! ## Sparse threshold representations -/

/-- If a PTF is represented using only monomials from `F`, the absolute Fourier mass of `f` on `F`
is at least one. [OD14, Thm. 5.10; Bru90]

**Proof sketch.** Form the polynomial whose coefficients on `F` are the corresponding Fourier
coefficients of `f`. Plancherel identifies its correlation with the representing polynomial.
Hölder's inequality and `‖p̂‖∞ ≤ ‖p‖₁` then force Fourier one-mass at least one. -/
theorem ptf_support_fourier_mass {f : BooleanFunc n} (hfb : isPmOne f)
    (p : MultilinearPolynomial n) (F : Finset (Finset (Fin n)))
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hsupport : ∀ S : Finset (Fin n), p S ≠ 0 → S ∈ F) :
    1 ≤ ∑ S ∈ F, |fourierCoeff f S| := sorry

/-- Every polynomial threshold representation of the inner-product-mod-two function on `2n` bits
has sparsity at least `2ⁿ`. [OD14, Cor. 5.11]

**Proof sketch.** Every Fourier coefficient of inner product mod two has magnitude `2⁻ⁿ`. Apply
`ptf_support_fourier_mass` to the support of the representing polynomial and rearrange. -/
theorem innerProductModTwo_ptf_sparsity (p : MultilinearPolynomial (n + n))
    (hrep : IsPolynomialThresholdRepresentation (innerProductModTwo n) p) :
    2 ^ n ≤ p.sparsity := sorry

/-- A nonzero function of positive arity with small spectral one-norm has a uniformly close sparse
multilinear polynomial approximation. The positive-arity hypothesis makes explicit the source's
standing convention that Boolean functions have at least one input. [OD14, Thm. 5.12; BS92]

**Proof sketch.** Independently sample `s` Fourier characters with probabilities proportional to
the magnitudes of their coefficients and average their signed characters. A Chernoff bound controls
the error at each cube point; a union bound over the `2ⁿ` points yields one simultaneous choice. -/
theorem sparse_polynomial_approximation (f : BooleanFunc n) (hn : 0 < n) (hf : f ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (s : ℕ) (hs : 4 * n * spectralOneNorm f ^ 2 / δ ^ 2 ≤ s) :
    ∃ q : MultilinearPolynomial n,
      q.sparsity ≤ s ∧ supNorm (fun x ↦ f x - q.eval x) < δ := sorry

/-- Every positive-arity `±1`-valued Boolean function has a PTF representation of sparsity at most
`⌈4n ‖f̂‖₁²⌉` and is a majority of that many parities or negated parities. The positive-arity
hypothesis makes explicit the source's standing convention. [OD14, Cor. 5.13; BS92]

**Proof sketch.** Apply `sparse_polynomial_approximation` with error one. Strict approximation to a
`±1`-valued function preserves its sign at every point, so the approximating polynomial is a PTF
representation. -/
theorem exists_sparse_ptf_representation (f : BooleanFunc n) (hn : 0 < n) (hf : isPmOne f) :
    let s := Nat.ceil (4 * n * spectralOneNorm f ^ 2)
    (∃ p : MultilinearPolynomial n,
      IsPolynomialThresholdRepresentation f p ∧ p.sparsity ≤ s) ∧
      IsMajorityOfSignedParities f s := sorry

end ThresholdFunctions
end BooleanAnalysis
