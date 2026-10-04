import TCSlib.BooleanAnalysis.Hypercontractivity.ProductSpace
import TCSlib.BooleanAnalysis.Hypercontractivity.Parameters

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hypercontractivity on finite product spaces: statement skeletons

## Main definitions

The definitions are in `ProductSpace`. Norms here have finite real exponents.

## Main results

* `one_coordinate_hypercontractivity`: Corollary 10.20.
* `product_hypercontractivity`: the General Hypercontractivity Theorem, with both
  the `(2,q)` and conjugate `(q',2)` estimates and possibly different coordinate spaces.
* `product_hypercontractivity_induction`: tensorization for finite ordered exponents `p ≤ q`.

The one-coordinate corollary reuses the general product theorem. The general estimates
and tensorization statement remain proof obligations.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Chapter 10, opening theorem, §10.1, and Corollary 10.20.
-/

open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity

universe u

/-- On a heterogeneous finite product with every atom at least `lam`, the minimum-atom
radius gives both conjugate hypercontractive inequalities.
[OD14, Ch. 10, General Hypercontractivity Theorem]

**Proof sketch.** Establish the scalar contraction on each coordinate by splitting off
the mean and applying the discrete two-point moment estimate. Tensorize the resulting
norm inequalities using the two-function induction argument, then use duality. -/
theorem product_hypercontractivity {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ)
    (hbound : ρ ≤ (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q))
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm 2 f ∧
      P.norm 2 (P.noise ρ f) ≤ P.norm (q / (q - 1)) f := sorry

/-- On a single finite coordinate, noise is hypercontractive from `2` to `q` and from
`q/(q-1)` to `2` at the minimum-atom radius. [OD14, Cor. 10.20]
The book assumes at least two outcomes; the singleton case satisfies the same statement.

**Proof sketch.** Specialize the general product theorem to one coordinate. -/
theorem one_coordinate_hypercontractivity (P : FiniteProduct.{u} 1)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ)
    (hbound : ρ ≤ (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q))
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm 2 f ∧
      P.norm 2 (P.noise ρ f) ≤ P.norm (q / (q - 1)) f := by
  exact product_hypercontractivity P lam q ρ hlam hlam1 hπ hq hρ hbound f

/-- Coordinatewise hypercontractivity tensorizes to the full product for finite
ordered exponents `1 ≤ p ≤ q`.
[OD14, §10.1, Hypercontractivity Induction Theorem]
The source allows any `p,q ≥ 1`. This declaration specializes to `p ≤ q`, the range needed
for the finite-`q` General Hypercontractivity Theorem, and does not represent infinite
exponents or the source's `p > q` contraction cases.

**Proof sketch.** Express operator contraction as a two-function inequality by norm duality.
Induct on the number of coordinates, applying the coordinate estimate and the mixed-norm
inequality at each step, then dualize back. -/
theorem product_hypercontractivity_induction {n : ℕ} (P : FiniteProduct.{u} n)
    (p q ρ : ℝ) (hp : 1 ≤ p) (hpq : p ≤ q) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcoord : ∀ i (g : P.Ω i → ℝ),
      ((∑ x, P.weight i x *
        |ρ * g x + (1 - ρ) * (∑ y, P.weight i y * g y)| ^ q) ^ (1 / q)) ≤
      ((∑ x, P.weight i x * |g x| ^ p) ^ (1 / p)))
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm p f := sorry

/-- The sharp discrete radius also tensorizes, giving the improved parameter explicitly
mentioned in the General Hypercontractivity Theorem.
[OD14, Ch. 10, General Hypercontractivity Theorem and Thm. 10.18]

**Proof sketch.** Apply the sharp centered discrete-variable inequality to each coordinate,
then tensorize and use duality for the conjugate estimate. -/
theorem product_hypercontractivity_sharp {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ sharpDiscreteRadius q lam)
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm 2 f ∧
      P.norm 2 (P.noise ρ f) ≤ P.norm (q / (q - 1)) f := sorry

end BooleanAnalysis.Hypercontractivity
