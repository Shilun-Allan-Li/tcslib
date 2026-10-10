/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Expanders.Walks

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Expander Chernoff Bound

Arora–Barak's Theorem 7.41: the fraction of time a random walk on an expander
spends inside a set `B` of density `β` concentrates around `β`, with the same
exponential decay (up to the spectral gap factor `1−λ`) as for independent
samples.  This is the tool behind randomness-efficient error reduction for
*two-sided* error algorithms (run the algorithm on the `k` coin strings
visited by a walk and take the majority).

## Main definitions

None — this module only states theorems about existing definitions.

## Main results (intentionally statement-only)

* `Expander.walk_visits_concentration` — [AB09, Thm 7.41].

## Deviations from the source

* As in `Expanders.Walks`, our walk `walkPMF hA k` visits `k+1` vertices
  (the book's `X₁,…,X_k` has `k` vertices), so `k+1` replaces the book's `k`.
* **Erratum.** The draft prints the bound as `2e^{(1−λ)δ²k/60}`, with a
  positive exponent, which is vacuous; the intended bound (cf. Gillman,
  *A Chernoff bound for random walks on expander graphs*, SIAM J. Comput.
  1998) is `2e^{−(1−λ)δ²k/60}`.  We state it with the negative exponent.
* The book's proof is omitted ("whose proof we omit"), so the eventual proof
  here will follow an external source rather than [AB09].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Gil98] D. Gillman, *A Chernoff bound for random walks on expander graphs*,
  SIAM Journal on Computing 27(4), 1998.
-/

namespace Expander

open Matrix

variable {n : ℕ} [NeZero n]

/-- **Expander Chernoff Bound** ([AB09, Thm 7.41]).  Let `A` be symmetric
stochastic with `λ(A) ≤ λ` (for a graph: an `(N,d,λ)`-graph) and `B` a set of
exactly `βN` vertices.  For a uniformly-started `k`-step random walk visiting
`X₀, …, X_k`, let `Bᵢ` be the indicator that `Xᵢ ∈ B`.  Then for every
`δ > 0`,

`Pr[ |(Σᵢ Bᵢ)/(k+1) − β| > δ ] < 2·exp(−(1−λ)δ²(k+1)/60)`.

The draft's positive exponent is a typo; see the module docstring.

**Proof sketch** (omitted in [AB09]; after [Gil98]): bound the moment
generating function `E[exp(t·Σᵢ Bᵢ)]` by the largest eigenvalue of the
perturbed transition operator `A·exp(t·B̂)`, control that eigenvalue via the
spectral gap `1−λ` using first-order perturbation theory, and conclude by the
exponential Markov inequality applied to both tails. -/
theorem walk_visits_concentration {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {B : Finset (Fin n)} {β δ : ℝ}
    (hB : (B.card : ℝ) = β * n) (hδ : 0 < δ) (k : ℕ) :
    (walkPMF hA k).toMeasure
        {f | δ < |(∑ i, if f i ∈ B then (1 : ℝ) else 0) / (k + 1) - β|} <
      ENNReal.ofReal (2 * Real.exp (-((1 - lam) * δ ^ 2 * (k + 1)) / 60)) := by
  sorry

end Expander
