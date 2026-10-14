/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Negligible and noticeable functions

A function of the security parameter is negligible when it eventually falls below every
inverse polynomial, and noticeable when it eventually stays above some inverse
polynomial. Security definitions allow an adversary negligible success; hardness
amplification starts from a noticeable failure probability. The two notions are not
complementary: a function can be neither.

The functions here take real values and the conditions bound `|μ n|`, so that
differences of probabilities can be fed in directly. [Gar26] restricts to values in
`[0, 1]`; on such functions the definitions agree.

## Main definitions

* `Negligible μ`: for every `c`, eventually `|μ n| < 1 / n^c`.
* `Noticeable μ`: for some `c`, eventually `μ n > 1 / n^c`.

## Main results

* `Negligible.add`, `Negligible.mul`, `Negligible.const_mul`, `Negligible.mono`: closure.
* `Negligible.mul_pow`: a negligible function times a polynomial is negligible.
* `negligible_two_pow_neg`: `2^{-n}` is negligible.
* `Noticeable.not_negligible`: noticeable functions are not negligible.
* `not_negligible_sub`: a non-negligible function minus a negligible one is
  non-negligible.
* `exists_not_negligible_not_noticeable`: some function is neither.
* `not_negligible_iff`: a function is non-negligible exactly when it exceeds some
  inverse polynomial infinitely often.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §1.2 (Definitions 1.3 and 1.4, Exercise 1.1) and
  Exercises 2.1 and 2.2.
-/

namespace TCSlib.Cryptography

/-- A function `μ` of the security parameter is negligible when for every `c` there is
`n₀` with `|μ n| < 1 / n^c` for all `n ≥ n₀`. [Gar26, Definition 1.4], for real-valued
functions bounded in absolute value; on `[0, 1]`-valued functions this is the source's
definition. -/
def Negligible (μ : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, |μ n| < 1 / (n : ℝ) ^ c

/-- A function `μ` is noticeable when there are `c` and `n₀` with `μ n > 1 / n^c` for all
`n ≥ n₀`. [Gar26, Definition 1.3]. -/
def Noticeable (μ : ℕ → ℝ) : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀, 1 / (n : ℝ) ^ c < μ n

variable {μ ν : ℕ → ℝ}

/-- A function eventually dominated in absolute value by a negligible one is negligible.
Technical glue. -/
theorem Negligible.mono (hμ : Negligible μ) (h : ∃ n₀, ∀ n ≥ n₀, |ν n| ≤ |μ n|) :
    Negligible ν := by
  sorry

/-- The sum of two negligible functions is negligible. [Gar26, Exercise 1.1(1)–(2)].

**Proof sketch.** Bound each by `1 / n^(c+1)` eventually; their sum is below
`2 / n^(c+1) ≤ 1 / n^c` once `n ≥ 2`. -/
theorem Negligible.add (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (fun n => μ n + ν n) := by
  sorry

/-- A constant multiple of a negligible function is negligible. -/
theorem Negligible.const_mul (hμ : Negligible μ) (a : ℝ) :
    Negligible (fun n => a * μ n) := by
  sorry

/-- The product of two negligible functions is negligible. [Gar26, Exercise 1.1(3) and
Exercise 2.1]. -/
theorem Negligible.mul (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (fun n => μ n * ν n) := by
  sorry

/-- A negligible function times the polynomial `n^d` is negligible. Used whenever a
hybrid argument multiplies an advantage by a polynomial number of hybrids. [Gar26,
§1.2, "any polynomial function of a negligible function is still negligible"].

**Proof sketch.** Given `c`, use the bound for `c + d`. -/
theorem Negligible.mul_pow (hμ : Negligible μ) (d : ℕ) :
    Negligible (fun n => (n : ℝ) ^ d * μ n) := by
  sorry

/-- The function `2^{-n}` is negligible. [Gar26, §1.2, Example after Definition 1.4].

**Proof sketch.** `n^c < 2^n` for all large `n`. -/
theorem negligible_two_pow_neg : Negligible (fun n => (2 : ℝ)⁻¹ ^ n) := by
  sorry

/-- A noticeable function is not negligible. [Gar26, §1.2]. -/
theorem Noticeable.not_negligible (hμ : Noticeable μ) : ¬ Negligible μ := by
  sorry

/-- A function is non-negligible exactly when there is `c` such that `|μ n| ≥ 1 / n^c`
for infinitely many `n`. [Gar26, §1.2, "Gap between Noticeable and Negligible
Functions"]. -/
theorem not_negligible_iff :
    ¬ Negligible μ ↔ ∃ c : ℕ, ∀ n₀ : ℕ, ∃ n ≥ n₀, 1 / (n : ℝ) ^ c ≤ |μ n| := by
  sorry

/-- If `μ` is not negligible and `ν` is negligible then `μ - ν` is not negligible.
[Gar26, §2.2.2, footnote 3 (exercise)].

**Proof sketch.** Otherwise `μ = (μ - ν) + ν` would be negligible. -/
theorem not_negligible_sub (hμ : ¬ Negligible μ) (hν : Negligible ν) :
    ¬ Negligible (fun n => μ n - ν n) := by
  sorry

/-- Some function into `[0, 1]` is neither negligible nor noticeable: `2^{-n}` at even
`n` and `n^{-3}` at odd `n`. [Gar26, §1.2, "Gap between Noticeable and Negligible
Functions"]. -/
theorem exists_not_negligible_not_noticeable :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n ∧ μ n ≤ 1) ∧ ¬ Negligible μ ∧ ¬ Noticeable μ := by
  sorry

end TCSlib.Cryptography
