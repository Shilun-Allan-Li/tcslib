/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Complexity.Promise.Basic
import Mathlib.Data.Real.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class PP

`PP` is the class of languages decided by an efficient randomized verifier that accepts every
member with probability *strictly* greater than `1/2` and every non-member with probability at
most `1/2` [Wat08, §II.1]. Unlike `BPP` there is no gap between the two thresholds, which is why
`PP` is a counting class rather than a class of efficient algorithms.

## Main definitions

* `Counting.InPP E L` — `L ∈ PP` relative to the verifier model `E`.
* `Counting.InPromisePP E A` — the promise version [Wat08, §II.1].

## Main results

* `Counting.inPromisePP_ofLanguage_iff` — on languages, promise `PP` is `PP`.
* `Counting.randProb_cast_eq_sum` — `randProb` read as a real-valued uniform average, the form
  in which quantum acceptance probabilities meet classical ones (plan FD-11).

## Divergences

* As for `Randomized.InBPP` (see `TCSlib/Complexity/Randomized/Classes.lean`, **Deviations**),
  machines are replaced by an abstract `VerifierModel` `E` with random strings of length
  `polyLen a k |x|`; the intended instance is `Randomized.polyTimeModel`. [Wat08, §II.1] and
  [AB09, ch. 17] state `PP` for polynomial-time probabilistic machines; the certificate form here
  is the standard equivalent with the coin flips written out as the random string.

## References

* [Wat08] J. Watrous, *Quantum Computational Complexity*, arXiv:0804.3401, 2008.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Counting

open Randomized Finset

/-- `L ∈ PP` relative to the verifier model `E`: some efficient Boolean verifier `M` with random
strings of length `polyLen a k |x|` accepts `x` with probability strictly greater than `1/2`
exactly when `x ∈ L`. [Wat08, §II.1], [AB09, ch. 17], in the certificate form of the module
docstring. -/
def InPP (E : VerifierModel) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      x ∈ L ↔ 1/2 < randProb (polyLen a k x.length) fun r => M x r = true

/-- `L ∈ PP` iff some efficient verifier accepts exactly the members of `L` with probability
greater than `1/2`. -/
theorem inPP_iff (E : VerifierModel) (L : Language Bool) :
    InPP E L ↔
      ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
        E.Eff (boolVerifier M) ∧
        ∀ x : List Bool,
          x ∈ L ↔ 1/2 < randProb (polyLen a k x.length) fun r => M x r = true := Iff.rfl

/-- The promise problem `A` is in (promise) `PP` relative to `E`: some efficient verifier accepts
every yes-instance with probability greater than `1/2` and every no-instance with probability at
most `1/2`. [Wat08, §II.1] -/
def InPromisePP (E : VerifierModel) (A : Promise.Problem) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ A.yes → 1/2 < randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∈ A.no → randProb (polyLen a k x.length) (fun r => M x r = true) ≤ 1/2)

/-- `A` is in promise `PP` iff some efficient verifier separates its yes- and no-instances at the
threshold `1/2`. -/
theorem inPromisePP_iff (E : VerifierModel) (A : Promise.Problem) :
    InPromisePP E A ↔
      ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
        E.Eff (boolVerifier M) ∧
        ∀ x : List Bool,
          (x ∈ A.yes → 1/2 < randProb (polyLen a k x.length) fun r => M x r = true) ∧
          (x ∈ A.no → randProb (polyLen a k x.length) (fun r => M x r = true) ≤ 1/2) :=
  Iff.rfl

/-- On languages, promise `PP` is `PP`.

**Proof sketch.** For `ofLanguage L`, the two clauses say `x ∈ L → 1/2 < Pr` and
`x ∉ L → Pr ≤ 1/2`; together, with `not_lt`, they are the equivalence `x ∈ L ↔ 1/2 < Pr`. -/
theorem inPromisePP_ofLanguage_iff (E : VerifierModel) (L : Language Bool) :
    InPromisePP E (Promise.ofLanguage L) ↔ InPP E L := by
  sorry

/-- `randProb` as a real-valued uniform average: the probability of `A` over `m` random bits is
`∑_r [A r] / 2^m`, summed over all `2^m` strings. This is the form a quantum circuit's
acceptance probability takes when its random bits come from Hadamard gates (plan FD-11).

**Proof sketch.** `randProb m A` is `#{r : A r} / 2^m` in `ℚ`; cast to `ℝ` (`Rat.cast_div`,
`Rat.cast_natCast`) and write the count as a sum of indicators (`Finset.sum_boole`), then move
the division inside the sum (`Finset.sum_div`). -/
theorem randProb_cast_eq_sum (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    ((randProb m A : ℚ) : ℝ) =
      ∑ r : Fin m → Bool, (if A (List.ofFn r) then (1 : ℝ) else 0) / 2 ^ m := by
  sorry

end Counting
