/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Error reduction by repetition: the Chernoff core

The probabilistic heart of Arora–Barak's error-reduction theorem
([AB09, Thm 7.10]): run `k` independent trials of a decision procedure that
is correct with probability `p ≥ 1/2 + ε` and take the majority; the
probability that the majority is wrong is exponentially small in `k`.

This file states the machine-independent core over i.i.d. Bernoulli random
variables: the Chernoff-type concentration bound [AB09, Cor 7.11] and the
majority-vote error bound instantiating [AB09, Thm 7.10]'s calculation.
Wrapping these into statements about `BPP`-style verifier classes is Tier B
work and lives elsewhere.

## Main results (sorry-stubbed)

* `Randomized.iid_bernoulli_avg_concentration` — [AB09, Cor 7.11], with a
  corrected constant (see **Deviations**).
* `Randomized.majority_error_le` — the calculation proving [AB09, Thm 7.10].

## Deviations from the source

* [AB09, Cor 7.11] is stated for abstract i.i.d. Boolean random variables
  `X₁,…,X_k` with `Pr[Xᵢ = 1] = p`; we realize them concretely as the product
  measure of `k` Bernoulli(`p`) distributions on `Fin k → Bool`, which is the
  same joint distribution.
* **Erratum.** [AB09, Cor 7.11] prints the bound
  `Pr[|(1/k)ΣXᵢ − p| > δ] < e^{−(δ²/4)pk}`, which is false: for a single
  trial (`k = 1`) with `p = 1/2` and `δ = 1/4`, the deviation event has
  probability `1` while the claimed bound is `e^{−1/128} < 1`.  We state the
  standard two-sided Hoeffding bound `≤ 2·e^{−2δ²k}` instead, which is what
  the error-reduction argument needs.
* [AB09, Thm 7.10] is stated for polynomial-time PTMs, with
  `p = 1/2 + |x|^{−c}` and final bound `2^{−|x|^d}`; `majority_error_le` is
  its probabilistic content with `ε` in place of `|x|^{−c}`: the one-sided
  Hoeffding bound gives majority error at most `e^{−2ε²k}`, which for
  `k = Θ((n+1)^{2c+d})` is at most `2^{−(n+1)^d}`.  The book's displayed
  intermediate step normalizes the sum by `1/n` where `1/k` is meant; we
  state it with `1/k`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open MeasureTheory
open scoped NNReal ENNReal

/-- The joint distribution of `k` independent Bernoulli(`p`) trials, as a
measure on `Fin k → Bool`.  [AB09, Cor 7.11: "independent identically
distributed Boolean random variables"] -/
noncomputable def iidBernoulli (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (Fin k → Bool) :=
  Measure.pi fun _ => (PMF.bernoulli p hp).toMeasure

/-- The number of successes among the `k` trials `ω`, as a real number. -/
def successCount {k : ℕ} (ω : Fin k → Bool) : ℝ :=
  ∑ i, if ω i then (1 : ℝ) else 0

/-- **Concentration for i.i.d. Boolean trials** (the role of
[AB09, Cor 7.11], stated as the two-sided Hoeffding bound).  Let `X₁,…,X_k`
be i.i.d. Boolean random variables with `Pr[Xᵢ = 1] = p`, and `δ > 0`.  Then
`Pr[|(1/k)Σᵢ Xᵢ − p| > δ] ≤ 2·e^{−2δ²k}`.

The book's printed bound `< e^{−(δ²/4)pk}` is false (see the module
docstring's **Erratum**); this is the standard replacement, and suffices for
[AB09, Thm 7.10].

**Proof sketch.** Hoeffding's inequality for sums of independent bounded
random variables (in Mathlib: `measure_sum_ge_le_of_iIndepFun` for
sub-Gaussian summands; a `{0,1}`-valued variable is sub-Gaussian with
parameter `1/4` by Hoeffding's lemma), applied to `Xᵢ − p` on each of the
two tails with threshold `t = δk`, each tail contributing `e^{−2δ²k}`. -/
theorem iid_bernoulli_avg_concentration {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ}
    (hk : 0 < k) {δ : ℝ} (hδ0 : 0 < δ) :
    iidBernoulli k p hp {ω | δ < |successCount ω / k - (p : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * k)) := by
  sorry

/-- **Majority-vote error reduction, concentration core** (the calculation
proving [AB09, Thm 7.10]).  If each of `k` i.i.d. trials succeeds with
probability `p ≥ 1/2 + ε`, the probability that at most half the trials
succeed — i.e. that the majority vote errs — is at most `e^{−2ε²k}`
(one-sided Hoeffding; the book's `e^{−(δ²/4)pk}`-based route is unsound,
see the module docstring's **Erratum**).

For advantage `ε ≥ (n+1)^{−c}/6` and `k = Θ((n+1)^{2c+d})` repetitions this
is at most `2^{−(n+1)^d}`, which is [AB09, Thm 7.10]'s bound.

**Proof sketch.** If at most half the trials succeed then
`(1/k)Σᵢ Xᵢ ≤ 1/2 ≤ p − ε`, so the lower tail `Σᵢ(Xᵢ − p) ≤ −εk` has
occurred; one-sided Hoeffding for independent `{0,1}`-valued summands bounds
it by `e^{−2ε²k}`. -/
theorem majority_error_le {p : ℝ≥0} (hp : p ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hpε : 1 / 2 + ε ≤ (p : ℝ)) {k : ℕ} (hk : 0 < k) :
    iidBernoulli k p hp {ω | 2 * successCount ω ≤ k} ≤
      ENNReal.ofReal (Real.exp (-2 * ε ^ 2 * k)) := by
  sorry

end Randomized
