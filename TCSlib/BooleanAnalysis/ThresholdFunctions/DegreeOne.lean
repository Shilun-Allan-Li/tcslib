import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-! ## Subcubes and Hamming balls -/

/-- A codimension-`k` subcube indicator has expectation `2⁻ᵏ` and degree-one Fourier weight
`k 2⁻²ᵏ`. [OD14, Prop. 5.24]

**Proof sketch.** Expand the indicator as the product of the `k` one-coordinate indicators. Its
Fourier expansion has equal coefficients `2⁻ᵏ` on all subsets of the fixed coordinates; exactly `k`
of these subsets are singletons. -/
theorem subcube_degreeOne_weight (J : Finset (Fin n)) (b : Fin n → Bool) (hJ : J.Nonempty) :
    expect (subcubeIndicator J b) = 1 / (2 : ℝ) ^ J.card ∧
      weightLevel 1 (subcubeIndicator J b) = J.card / (2 : ℝ) ^ (2 * J.card) := sorry

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

/-- The truncated first moment of a normalized Rademacher linear form has a Gaussian tail bound.
[OD14, Lemma 5.31]

**Proof sketch.** Express the truncated first moment as `s Pr[|ℓ| ≥ s]` plus the integral of the
tail probability. Hoeffding's inequality bounds both terms, and the remaining Gaussian integral is
at most its integrand multiplied by `2/s`. -/
theorem linear_form_tail_expectation (a : Fin n → ℝ)
    (hnorm : ∑ i : Fin n, a i ^ 2 = 1) {s : ℝ} (hs : 1 ≤ s) :
    expect (fun x ↦ if s ≤ |∑ i : Fin n, a i * boolToSign (x i)| then
        |∑ i : Fin n, a i * boolToSign (x i)| else 0) ≤
      (2 * s + 2) * Real.exp (-s ^ 2 / 2) := sorry

/-- The degree-one Fourier weight of a `{0,1}`-valued function of mean `α ≤ 1/2` is at most a
universal constant times `α² log(1/α)`. [OD14, §5.4, Level-1 Inequality; Tal96]

**Proof sketch.** Normalize the degree-one Fourier part to an `L²`-unit linear form. Split its
correlation with `f` at a threshold `s`: the central part contributes at most `αs`, while
`linear_form_tail_expectation` controls the tail. Choosing `s ≍ sqrt(log(1/α))` gives the bound. -/
theorem levelOne_inequality :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (f : BooleanFunc n) (α : ℝ),
      (∀ x, f x = 0 ∨ f x = 1) → expect f = α → 0 < α → α ≤ 1 / 2 →
        weightLevel 1 f ≤ C * α ^ 2 * Real.log α⁻¹ := sorry

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

**Proof sketch.** Replace `f` by the `{0,1}`-indicator of its minority value. Its mean is at most
`δ/2`; rescaling its singleton Fourier coefficients and applying the Level-1 inequality gives the
stated bound. -/
theorem biased_degreeOne_weight (f : BooleanFunc n) (hf : isPmOne f) {δ : ℝ}
    (hδ : 0 ≤ 1 - δ) (hbias : 1 - δ ≤ |expect f|) :
    weightLevel 1 f ≤ 4 * δ ^ 2 * Real.log (2 / δ) := sorry

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
            (δ / 4 + 16 * C ^ 2 * δ ^ 2 * max (Real.log (1 / (C * δ))) 1) := sorry

end ThresholdFunctions
end BooleanAnalysis
