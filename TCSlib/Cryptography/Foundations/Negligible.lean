/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed

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
  intro c
  obtain ⟨n₀, h₀⟩ := h
  obtain ⟨n₁, h₁⟩ := hμ c
  exact ⟨max n₀ n₁, fun n hn =>
    (h₀ n (le_of_max_le_left hn)).trans_lt (h₁ n (le_of_max_le_right hn))⟩

/-- The sum of two negligible functions is negligible. [Gar26, Exercise 1.1(1)–(2)].

**Proof sketch.** Bound each by `1 / n^(c+1)` eventually; their sum is below
`2 / n^(c+1) ≤ 1 / n^c` once `n ≥ 2`. -/
theorem Negligible.add (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (fun n => μ n + ν n) := by
  intro c
  obtain ⟨n₁, h₁⟩ := hμ (c + 1)
  obtain ⟨n₂, h₂⟩ := hν (c + 1)
  refine ⟨max (max n₁ n₂) 2, fun n hn => ?_⟩
  have hn₁ : n ≥ n₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : n ≥ n₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by linarith) c
  have key : 2 * (1 / (n : ℝ) ^ (c + 1)) ≤ 1 / (n : ℝ) ^ c := by
    have hinv : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h2
    have ha : 0 < 1 / (n : ℝ) ^ c := by positivity
    rw [pow_succ, ← one_div_mul_one_div]
    nlinarith
  calc |μ n + ν n| ≤ |μ n| + |ν n| := abs_add_le _ _
    _ < 1 / (n : ℝ) ^ (c + 1) + 1 / (n : ℝ) ^ (c + 1) := add_lt_add (h₁ n hn₁) (h₂ n hn₂)
    _ ≤ 1 / (n : ℝ) ^ c := by linarith

/-- The product of two negligible functions is negligible. [Gar26, Exercise 1.1(3) and
Exercise 2.1].

**Proof sketch.** Eventually `|ν n| < 1` (the bound for `c = 0`), so
`|μ n ν n| ≤ |μ n| < 1 / n^c`. -/
theorem Negligible.mul (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (fun n => μ n * ν n) := by
  intro c
  obtain ⟨n₁, h₁⟩ := hμ c
  obtain ⟨n₂, h₂⟩ := hν 0
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  have hν1 : |ν n| < 1 := by simpa using h₂ n (le_of_max_le_right hn)
  rw [abs_mul]
  calc |μ n| * |ν n| ≤ |μ n| * 1 := mul_le_mul_of_nonneg_left hν1.le (abs_nonneg _)
    _ < 1 / (n : ℝ) ^ c := by rw [mul_one]; exact h₁ n (le_of_max_le_left hn)

/-- A negligible function times the polynomial `n^d` is negligible. Used whenever a
hybrid argument multiplies an advantage by a polynomial number of hybrids. [Gar26,
§1.2, "any polynomial function of a negligible function is still negligible"].

**Proof sketch.** Given `c`, use the bound for `c + d`. -/
theorem Negligible.mul_pow (hμ : Negligible μ) (d : ℕ) :
    Negligible (fun n => (n : ℝ) ^ d * μ n) := by
  intro c
  obtain ⟨n₀, h₀⟩ := hμ (c + d)
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by linarith) d
  rw [abs_mul, abs_of_pos hpos]
  calc (n : ℝ) ^ d * |μ n| < (n : ℝ) ^ d * (1 / (n : ℝ) ^ (c + d)) :=
        mul_lt_mul_of_pos_left (h₀ n (le_of_max_le_left hn)) hpos
    _ = 1 / (n : ℝ) ^ c := by
        rw [pow_add]; field_simp

/-- A constant multiple of a negligible function is negligible. [Gar26, §1.2].

**Proof sketch.** For `n ≥ |a|`, `|a μ n| ≤ |n μ n|`, and `n μ n` is negligible by
`Negligible.mul_pow`. -/
theorem Negligible.const_mul (hμ : Negligible μ) (a : ℝ) :
    Negligible (fun n => a * μ n) := by
  refine (hμ.mul_pow 1).mono ⟨⌈|a|⌉₊, fun n hn => ?_⟩
  have ha : |a| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [abs_mul, abs_mul, pow_one, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)

/-- The function `2^{-n}` is negligible. [Gar26, §1.2, Example after Definition 1.4].

**Proof sketch.** `n^c < 2^n` for all large `n`. -/
theorem negligible_two_pow_neg : Negligible (fun n => (2 : ℝ)⁻¹ ^ n) := by
  intro c
  have ht := tendsto_pow_const_div_const_pow_of_one_lt c (r := (2 : ℝ)) one_lt_two
  obtain ⟨n₀, h₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hlt : (n : ℝ) ^ c < 2 ^ n :=
    (div_lt_one (by positivity)).mp (h₀ n (le_of_max_le_left hn))
  show |(2 : ℝ)⁻¹ ^ n| < 1 / (n : ℝ) ^ c
  rw [abs_of_pos (by positivity), inv_pow, ← one_div]
  exact one_div_lt_one_div_of_lt (pow_pos (by linarith) c) hlt

/-- A noticeable function is not negligible. [Gar26, §1.2].

**Proof sketch.** With the noticeability exponent `c`, at any `n` past both thresholds
`1 / n^c < μ n ≤ |μ n| < 1 / n^c`. -/
theorem Noticeable.not_negligible (hμ : Noticeable μ) : ¬ Negligible μ := by
  intro hneg
  obtain ⟨c, n₀, h₀⟩ := hμ
  obtain ⟨n₁, h₁⟩ := hneg c
  have a := h₀ (max n₀ n₁) (le_max_left _ _)
  have b := h₁ (max n₀ n₁) (le_max_right _ _)
  linarith [le_abs_self (μ (max n₀ n₁))]

/-- A function is non-negligible exactly when there is `c` such that `|μ n| ≥ 1 / n^c`
for infinitely many `n`. [Gar26, §1.2, "Gap between Noticeable and Negligible
Functions"]. -/
theorem not_negligible_iff :
    ¬ Negligible μ ↔ ∃ c : ℕ, ∀ n₀ : ℕ, ∃ n ≥ n₀, 1 / (n : ℝ) ^ c ≤ |μ n| := by
  simp only [Negligible, not_forall, not_exists, not_lt, exists_prop]

/-- If `μ` is not negligible and `ν` is negligible then `μ - ν` is not negligible.
[Gar26, §2.2.2, footnote 3 (exercise)].

**Proof sketch.** Otherwise `μ = (μ - ν) + ν` would be negligible. -/
theorem not_negligible_sub (hμ : ¬ Negligible μ) (hν : Negligible ν) :
    ¬ Negligible (fun n => μ n - ν n) := by
  intro h
  exact hμ (by simpa using h.add hν)

/-- Some function into `[0, 1]` is neither negligible nor noticeable: `2^{-n}` at even
`n` and `n^{-3}` at odd `n`. [Gar26, §1.2, "Gap between Noticeable and Negligible
Functions"].

**Proof sketch.** The values lie in `[0, 1]` directly. At odd `n` the value is `1 / n^3`,
so the bound for `c = 3` fails infinitely often and `μ` is not negligible
(`not_negligible_iff`). At even `n` the value is `2^{-n}`, which is eventually below every
`1 / n^c` (`negligible_two_pow_neg`), so `μ` is not noticeable. -/
theorem exists_not_negligible_not_noticeable :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n ∧ μ n ≤ 1) ∧ ¬ Negligible μ ∧ ¬ Noticeable μ := by
  refine ⟨fun n => if n % 2 = 0 then (2 : ℝ)⁻¹ ^ n else 1 / (n : ℝ) ^ 3, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs with h
    · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact ⟨by positivity, div_le_one_of_le₀ (one_le_pow₀ hn) (by positivity)⟩
  · refine not_negligible_iff.mpr ⟨3, fun n₀ => ⟨2 * n₀ + 1, by omega, ?_⟩⟩
    dsimp only
    rw [if_neg (by omega)]
    exact le_abs_self _
  · rintro ⟨c, n₀, h₀⟩
    obtain ⟨n₁, h₁⟩ := negligible_two_pow_neg c
    have h := h₀ (2 * max n₀ n₁) (by omega)
    have h' := h₁ (2 * max n₀ n₁) (by omega)
    dsimp only at h h'
    rw [if_pos (by omega)] at h
    rw [abs_of_pos (by positivity)] at h'
    linarith

end TCSlib.Cryptography
