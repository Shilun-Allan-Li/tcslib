/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Chebyshev's lower bound on the prime counting function and the density of primes

The set `Π_n` of primes below `2^n` [PS10, §2.3.2] and the two facts about it that the
candidate one-way functions of [PS10, ch. 2] rest on: Chebyshev's bound
`π(x) ≥ x / (2 log₂ x)` [PS10, Theorem 31.3] and its corollary that at least a `1/(2n)`
fraction of the `n`-bit numbers are prime [PS10, §2.3.2, Claim-33.1 of the inventory].

The proof follows [PS10, Theorem 31.3] through the central binomial coefficient: `C(2x, x)`
is at least `2^x`, and every prime power dividing it is at most `2x` (the corrected
[PS10, Claim 32.4], `Nat.pow_factorization_choose_le`), so `2^x ≤ (2x)^{π(2x)}`. This
*integer core* (`two_pow_le_pow_primeCounting`) is proved; the density corollary
(`two_pow_le_two_mul_card_primes`) follows from it at `x = 2^{n-1}`; the real-logarithm form
of the theorem (`chebyshev`) follows for even arguments by taking logarithms and for odd
arguments by the text's monotonicity of `t / log t`.

**Deviation:** [PS10, Theorem 31.3] claims the strict inequality `π(x) > x / (2 log x)` for
every real `x > 1`; equality holds at `x = 2` (`π(2) = 1`), so the theorem is stated with `≤`,
for natural arguments `m ≥ 2`. **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
`x = 1, p = 2`; the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is Mathlib's
`Nat.pow_factorization_choose_le`. **Deviation:** the density corollary needs `n ≥ 2`
(`Π_1 = ∅`); the text's "`n`-bit numbers" silently assumes it.

## Main definitions

* `TCSlib.Cryptography.NumberTheory.Primes` — `Π_n`, the primes below `2^n`, as a finite
  type ([PS10, §2.3.2]).

## Main results

* `TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting` — the integer core of
  Chebyshev's bound, `2^x ≤ (2x)^{π(2x)}` [PS10, Theorem 31.3].
* `TCSlib.Cryptography.NumberTheory.chebyshev_two_mul`,
  `TCSlib.Cryptography.NumberTheory.chebyshev` — the real-logarithm form
  [PS10, Theorem 31.3].
* `TCSlib.Cryptography.NumberTheory.two_pow_le_two_mul_card_primes`,
  `TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime`,
  `TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair` — the density of primes
  among `n`-bit numbers, as a cardinality and as uniform probabilities (Claim-33.1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3.2: Theorem 31.3, Claim 32.4 and the prime-density corollary on p. 33.)
-/

namespace TCSlib.Cryptography.NumberTheory

open Finset

/-! ### The set `Π_n` -/

/-- `Π_n`: the primes below `2^n`, i.e. the primes among the `n`-bit numbers, as a finite
type; the uniform distribution on it is `uprob` over this type [PS10, §2.3.2]. It contains
`2` and all small primes (the text's later "`n`-bit primes" is this set, used consistently
throughout the campaign). -/
abbrev Primes (n : ℕ) : Type := {p : Fin (2 ^ n) // (p : ℕ).Prime}

/-- `|Π_n|` is the number of primes strictly below `2^n` (`Nat.primeCounting'`). -/
theorem card_primes (n : ℕ) : Fintype.card (Primes n) = Nat.primeCounting' (2 ^ n) := by
  rw [← Nat.primesBelow_card_eq_primeCounting', ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun p => ⟨p.1, Nat.mem_primesBelow.2 ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨⟨p.1, (Nat.mem_primesBelow.1 p.2).1⟩, (Nat.mem_primesBelow.1 p.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-! ### The integer core of Chebyshev's bound -/

/-- `2x ≤ 2^x` for `x ≥ 1`. -/
private theorem two_mul_le_two_pow : ∀ x : ℕ, 1 ≤ x → 2 * x ≤ 2 ^ x
  | 0, h => absurd h (by omega)
  | 1, _ => le_rfl
  | x + 2, _ => by
    have := two_mul_le_two_pow (x + 1) (by omega)
    rw [pow_succ]
    omega

/-- The central binomial coefficient dominates `2^x` [PS10, proof of Theorem 31.3,
"`X > 2^x`"; the inequality is an equality at `x = 1`]. -/
private theorem two_pow_le_centralBinom (x : ℕ) (hx : 0 < x) : 2 ^ x ≤ Nat.centralBinom x := by
  have h4 := Nat.four_pow_le_two_mul_self_mul_centralBinom x hx
  have h2 : 2 * x ≤ 2 ^ x := two_mul_le_two_pow x hx
  have : (2 * x) * 2 ^ x ≤ (2 * x) * Nat.centralBinom x := by
    calc (2 * x) * 2 ^ x ≤ 2 ^ x * 2 ^ x := Nat.mul_le_mul_right _ h2
      _ = 4 ^ x := by rw [← mul_pow]; norm_num
      _ ≤ (2 * x) * Nat.centralBinom x := h4
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **The integer core of Chebyshev's theorem** [PS10, Theorem 31.3]: for `x ≥ 1`,
`2^x ≤ (2x)^{π(2x)}`, where `π(2x)` is the number of primes `≤ 2x`; taking logarithms,
`π(2x) ≥ x / log₂(2x) = (2x) / (2 log₂(2x))`.

**Proof sketch.** `X = C(2x, x) ≥ 2^x` (`Nat.four_pow_le_two_mul_self_mul_centralBinom` and
`2x ≤ 2^x`), `X = ∏_{p ≤ 2x} p^{ν_p(X)}` (`Nat.prod_pow_factorization_centralBinom`), each
prime factor contributes `p^{ν_p(X)} ≤ 2x` (the corrected [PS10, Claim 32.4],
`Nat.pow_factorization_choose_le`) and each non-prime contributes `1`, so the product is at
most `(2x)^{#\{p ≤ 2x prime\}} = (2x)^{π(2x)}`. -/
theorem two_pow_le_pow_primeCounting (x : ℕ) (hx : 0 < x) :
    2 ^ x ≤ (2 * x) ^ Nat.primeCounting (2 * x) := by
  have hprod : Nat.centralBinom x ≤ ∏ p ∈ range (2 * x + 1), (if p.Prime then 2 * x else 1) := by
    rw [← Nat.prod_pow_factorization_centralBinom x]
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p _ => ?_
    by_cases hp : p.Prime
    · rw [if_pos hp, Nat.centralBinom_eq_two_mul_choose]
      exact Nat.pow_factorization_choose_le (by omega)
    · rw [if_neg hp, Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
  have hcount : ∏ p ∈ range (2 * x + 1), (if p.Prime then 2 * x else 1) =
      (2 * x) ^ Nat.primeCounting (2 * x) := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Nat.primeCounting,
      ← Nat.primesBelow_card_eq_primeCounting']
    rfl
  calc 2 ^ x ≤ Nat.centralBinom x := two_pow_le_centralBinom x hx
    _ ≤ _ := hprod
    _ = _ := hcount

/-- **Chebyshev's bound at even arguments** [PS10, Theorem 31.3]: for `x ≥ 1`,
`(2x) / (2 log₂(2x)) ≤ π(2x)`.

**Proof sketch.** Take `log₂` of `two_pow_le_pow_primeCounting` (monotone,
`Real.logb_pow`, `log₂ 2 = 1`): `x ≤ π(2x) · log₂(2x)`; divide by `2 log₂(2x) > 0`. -/
theorem chebyshev_two_mul (x : ℕ) (hx : 0 < x) :
    (2 * x : ℝ) / (2 * Real.logb 2 (2 * x)) ≤ Nat.primeCounting (2 * x) := by
  have hcore : ((2 : ℝ) ^ x) ≤ ((2 * x : ℕ) : ℝ) ^ Nat.primeCounting (2 * x) := by
    exact_mod_cast two_pow_le_pow_primeCounting x hx
  have hx1 : (1 : ℝ) < 2 * x := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    linarith
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hcore
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  push_cast at hlog
  have hpos : 0 < Real.logb 2 (2 * x) := Real.logb_pos (by norm_num) hx1
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Chebyshev's theorem** [PS10, Theorem 31.3]: for every natural `m ≥ 2`,
`m / (2 log₂ m) ≤ π(m)`.

**Deviation:** stated with `≤` (the text's `>` fails at `m = 2`) and for natural arguments
`m ≥ 2` (the text's real `x > 1`; `π` is a step function, so nothing is lost).

**Proof sketch.** Even `m = 2x`: `chebyshev_two_mul`. Odd `m = 2x − 1 ≥ 3`: `2x` is composite,
so `π(m) = π(2x) ≥ 2x / (2 log₂(2x))`, and `t ↦ t / log₂ t` is increasing for `t ≥ 3`
(equivalently `(m+1)^m ≤ m^{m+1}` for `m ≥ 3`, i.e. `(1 + 1/m)^m ≤ e < 3 ≤ m`, from
`Real.add_one_le_exp`), so `2x / (2 log₂(2x)) ≥ m / (2 log₂ m)`. Sub-obligations:
`Nat.primeCounting` is constant across a non-prime (`Nat.count_succ`), the monotonicity
inequality in `Real.logb`, and the case `m = 3` (`π(3) = 2 ≥ 3 / (2 log₂ 3)`). -/
theorem chebyshev (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) / (2 * Real.logb 2 m) ≤ Nat.primeCounting m := by
  rcases Nat.even_or_odd m with ⟨x, hx⟩ | ⟨x, hx⟩
  · -- even `m = 2x`
    have hx0 : 0 < x := by omega
    rw [hx, show x + x = 2 * x by ring]
    push_cast
    exact chebyshev_two_mul x hx0
  · -- odd `m = 2x + 1 ≥ 3`: `π(m) = π(m + 1)` and `t / log₂ t` is increasing
    have hx1 : 1 ≤ x := by omega
    have hπ : Nat.primeCounting m = Nat.primeCounting (2 * (x + 1)) := by
      rw [show 2 * (x + 1) = m + 1 by omega]
      show Nat.primeCounting' (m + 1) = Nat.primeCounting' (m + 1 + 1)
      have hnp : ¬ Nat.Prime (m + 1) := by
        rw [show m + 1 = 2 * (x + 1) by omega]
        exact Nat.not_prime_mul (a := 2) (b := x + 1) (by norm_num) (by omega)
      rw [Nat.primeCounting', Nat.count_succ Nat.Prime (m + 1), if_neg hnp, add_zero]
    rw [hπ]
    have h1 := chebyshev_two_mul (x + 1) (by omega)
    have hm1 : ((2 * (x + 1) : ℕ) : ℝ) = (m : ℝ) + 1 := by
      rw [hx]
      push_cast
      ring
    push_cast at h1
    push_cast at hm1
    rw [hm1] at h1
    refine le_trans ?_ h1
    -- monotonicity of `t ↦ t / log₂ t` from `m` to `m + 1`, for `m ≥ 3`
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast (by omega : 3 ≤ m)
    have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
    have hlogm1 : 0 < Real.log (m + 1) := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hkey : ((m : ℝ) + 1) ^ m ≤ (m : ℝ) ^ (m + 1) := by
      have hmpos : (0 : ℝ) < m := by linarith
      have he : (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 / (m : ℝ))
        calc (1 + 1 / (m : ℝ)) ^ m ≤ (Real.exp (1 / m)) ^ m :=
              pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = Real.exp 1 := by
              rw [← Real.exp_nat_mul]
              congr 1
              field_simp
      have h3 : Real.exp 1 ≤ 3 := by
        have := Real.exp_one_lt_d9
        norm_num at this
        linarith
      calc ((m : ℝ) + 1) ^ m = (m : ℝ) ^ m * (1 + 1 / m) ^ m := by
            rw [← mul_pow]
            congr 1
            field_simp
        _ ≤ (m : ℝ) ^ m * 3 := by gcongr; exact he.trans h3
        _ ≤ (m : ℝ) ^ m * m := by gcongr
        _ = (m : ℝ) ^ (m + 1) := by rw [pow_succ]
    have hlogkey : (m : ℝ) * Real.log (m + 1) ≤ (m + 1) * Real.log m := by
      have := Real.log_le_log (by positivity) hkey
      rw [Real.log_pow, Real.log_pow] at this
      push_cast at this
      linarith
    have hdiv := div_le_div_of_nonneg_right hlogkey hlog2.le
    rw [Real.logb, Real.logb, div_le_div_iff₀ (mul_pos two_pos (div_pos hlogm hlog2))
      (mul_pos two_pos (div_pos hlogm1 hlog2))]
    calc (m : ℝ) * (2 * (Real.log (m + 1) / Real.log 2))
        = 2 * ((m * Real.log (m + 1)) / Real.log 2) := by ring
      _ ≤ 2 * (((m + 1) * Real.log m) / Real.log 2) := by linarith
      _ = ((m : ℝ) + 1) * (2 * (Real.log m / Real.log 2)) := by ring

/-! ### The density of primes among `n`-bit numbers -/

/-- `π(2^n) = π'(2^n)` for `n ≥ 2`: `2^n` is not prime. -/
private theorem primeCounting_two_pow (n : ℕ) (hn : 2 ≤ n) :
    Nat.primeCounting (2 ^ n) = Nat.primeCounting' (2 ^ n) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, if_neg, add_zero]
  exact fun h => not_prime_pow (by omega) (Nat.prime_iff.1 h)

/-- **Prime density** [PS10, §2.3.2, p. 33, Claim-33.1]: for `n ≥ 2`, `|Π_n| ≥ 2^n / (2n)`,
i.e. at least a `1/(2n)` fraction of the `n`-bit numbers are prime.

**Deviation:** `n ≥ 2` (`Π_1 = ∅`); §2.6.6 (p. 50) misquotes the bound as `1/n`.

**Proof sketch.** The integer core at `x = 2^{n−1}` gives `2^{2^{n−1}} ≤ (2^n)^{π(2^n)}`,
hence `2^{n−1} ≤ n · π(2^n)`; `π(2^n) = |Π_n|` since `2^n` is not prime. -/
theorem two_pow_le_two_mul_card_primes (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n ≤ 2 * n * Fintype.card (Primes n) := by
  have hcore := two_pow_le_pow_primeCounting (2 ^ (n - 1)) (by positivity)
  have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2, ← pow_mul] at hcore
  have hexp : 2 ^ (n - 1) ≤ n * Nat.primeCounting (2 ^ n) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 hcore
  rw [card_primes, ← primeCounting_two_pow n hn]
  calc 2 ^ n = 2 * 2 ^ (n - 1) := h2.symm
    _ ≤ 2 * (n * Nat.primeCounting (2 ^ n)) := Nat.mul_le_mul le_rfl hexp
    _ = 2 * n * Nat.primeCounting (2 ^ n) := by ring

/-- The probability that a uniform number below `2^n` is prime is `|Π_n| / 2^n`. -/
theorem uprob_prime_eq (n : ℕ) :
    uprob (fun x : Fin (2 ^ n) => (x : ℕ).Prime) = Fintype.card (Primes n) / 2 ^ n := by
  rw [uprob_eq_card_filter, Fintype.card_subtype, Fintype.card_fin]
  push_cast
  rfl

/-- A uniform `n`-bit string read as a number (`bitsToNat`) is prime with the same probability
as a uniform number below `2^n`: the bridge between the sampler of [PS10, Algorithm 50.16]
(`x ← {0,1}^n`) and `Π_n`. -/
theorem uprob_prime_bits (n : ℕ) :
    uprob (fun b : Fin n → Bool => (bitsToNat b).Prime) =
      uprob (fun x : Fin (2 ^ n) => (x : ℕ).Prime) :=
  uprob_comp_equiv (bitsEquiv n) (fun x : Fin (2 ^ n) => (x : ℕ).Prime)

/-- **Prime density as a probability** [PS10, §2.3.2, Claim-33.1]: for `n ≥ 2`, a uniform
number below `2^n` is prime with probability at least `1/(2n)`. -/
theorem one_div_le_uprob_prime (n : ℕ) (hn : 2 ≤ n) :
    1 / (2 * n : ℝ) ≤ uprob (fun x : Fin (2 ^ n) => (x : ℕ).Prime) := by
  rw [uprob_prime_eq, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h := two_pow_le_two_mul_card_primes n hn
  have h' : (2 : ℝ) ^ n ≤ 2 * n * Fintype.card (Primes n) := by exact_mod_cast h
  linarith

/-- A uniform pair of numbers below `2^n` consists of two primes with probability
`Pr[prime]^2` (independent coordinates). -/
theorem uprob_prime_pair (n : ℕ) :
    uprob (fun z : Fin (2 ^ n) × Fin (2 ^ n) => (z.1 : ℕ).Prime ∧ (z.2 : ℕ).Prime) =
      uprob (fun x : Fin (2 ^ n) => (x : ℕ).Prime) ^ 2 := by
  exact (HardcoreBit.uprob_prod_and (fun x : Fin (2 ^ n) => (x : ℕ).Prime)
    (fun x : Fin (2 ^ n) => (x : ℕ).Prime)).trans (sq _).symm

/-- **Prime pairs** [PS10, proof of Theorem 33.5, "with probability `1/4n²` a random input
pair consists of two primes"]: for `n ≥ 2`, a uniform pair of numbers below `2^n` is a pair
of primes with probability at least `1/(4n²)`. -/
theorem one_div_le_uprob_prime_pair (n : ℕ) (hn : 2 ≤ n) :
    1 / (4 * (n : ℝ) ^ 2) ≤
      uprob (fun z : Fin (2 ^ n) × Fin (2 ^ n) => (z.1 : ℕ).Prime ∧ (z.2 : ℕ).Prime) := by
  rw [uprob_prime_pair]
  have h := one_div_le_uprob_prime n hn
  have h0 : (0 : ℝ) ≤ 1 / (2 * n) := by positivity
  calc 1 / (4 * (n : ℝ) ^ 2) = (1 / (2 * n)) ^ 2 := by field_simp; ring
    _ ≤ _ := pow_le_pow_left₀ h0 h 2

end TCSlib.Cryptography.NumberTheory
