/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The extended Euclidean algorithm

The recursive `ExtendedEuclid(a, b)` of [PS10, Algorithm 43.2], returning Bézout
coefficients `(x, y)` with `ax + by = gcd(a, b)`, together with its recursive-call counter.
Both are defined by well-founded recursion on the second argument exactly as the text's
pseudo-code. The two facts proved about it are the ones the text proves:

* [PS10, Claim 43.3]: on `a > b` with `a < 2^n` the algorithm makes at most `2n` recursive
  calls (`extEuclidCalls_le`), by the text's induction on `n` with the two cases `b < 2^n`
  and `b ≥ 2^n` (in the second case `a mod b < 2^n` after one more call);
* [PS10, Claim 44.5]: correctness `ax + by = gcd(a, b)` (`extEuclid_spec`), by strong
  induction on `b` and the regrouping `d = b(x − ⌊a/b⌋y) + ay` of the text.

Mathlib's own extended Euclid (`Nat.xgcd`, `Nat.gcdA`, `Nat.gcdB`, `Nat.gcd_eq_gcd_ab`) is
the same algorithm in iterative form; the text's recursive variant and its call count are
formalized here because the call bound is what [PS10] proves. The modular inverse
`extEuclid_inv` is the use the text makes of the algorithm (inverses in `Z_N^*`,
[PS10, §2.6.4, Theorem 46.8], the RSA decryption exponent [PS10, Theorem 57.2]).

**Deviation:** the text's precondition is `a > b > 0` (Algorithm 43.2) or `a > b ≥ 0`
(Claim 43.3); on `b = 0` the recursion of the text falls through to `ExtendedEuclid(0, a)`,
which returns `(0, 1)` and then `(1, 0 − 1 · ⌊a/0⌋)`; here `b = 0` is an explicit base case
returning `(1, 0)` with no recursive call (same value, one call fewer). The "polynomial
time in `log a + log b`" remark (inventory Rem-43.6) is machine-level and not formalized;
Claim 43.3 is its mathematical content.

## Main definitions

* `TCSlib.Cryptography.NumberTheory.extEuclid` — `ExtendedEuclid(a, b)` [PS10, Algorithm 43.2].
* `TCSlib.Cryptography.NumberTheory.extEuclidCalls` — its number of recursive calls.

## Main results

* `TCSlib.Cryptography.NumberTheory.extEuclid_spec` — `ax + by = gcd(a, b)`
  [PS10, Claim 44.5].
* `TCSlib.Cryptography.NumberTheory.extEuclidCalls_le` — at most `2n` recursive calls for
  `a < 2^n` [PS10, Claim 43.3].
* `TCSlib.Cryptography.NumberTheory.extEuclid_inv` — the first coefficient is the inverse of
  `a` modulo `N` when `gcd(a, N) = 1`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.6.2: Algorithm 43.2, Claims 43.3, 44.4 and 44.5.)
-/

namespace TCSlib.Cryptography.NumberTheory

/-! ### The algorithm -/

/-- `ExtendedEuclid(a, b)` [PS10, Algorithm 43.2]: if `a mod b = 0` return `(0, 1)`; otherwise
let `(x, y) ← ExtendedEuclid(b, a mod b)` and return `(y, x − y ⌊a/b⌋)`. The value is the pair
of Bézout coefficients `(x, y)` with `ax + by = gcd(a, b)` (`extEuclid_spec`). Defined by
well-founded recursion on `b` (`a mod b < b`); the base case `b = 0` returns `(1, 0)`
(Deviation, see the module docstring). -/
def extEuclid (a b : ℕ) : ℤ × ℤ :=
  if _hb : b = 0 then (1, 0)
  else if a % b = 0 then (0, 1)
  else
    let r := extEuclid b (a % b)
    (r.2, r.1 - r.2 * ((a / b : ℕ) : ℤ))
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hb)

/-- The number of recursive calls made by `ExtendedEuclid(a, b)` [PS10, Claim 43.3]: `0` in
the base cases, one more than the count of the call on `(b, a mod b)` otherwise. -/
def extEuclidCalls (a b : ℕ) : ℕ :=
  if _hb : b = 0 then 0
  else if a % b = 0 then 0
  else extEuclidCalls b (a % b) + 1
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hb)

/-- Unfolding: the base case `b = 0`. -/
theorem extEuclid_zero_right (a : ℕ) : extEuclid a 0 = (1, 0) := by
  rw [extEuclid]
  simp

/-- Unfolding: the base case `a mod b = 0` (`b ≠ 0`). -/
theorem extEuclid_of_mod_eq_zero {a b : ℕ} (hb : b ≠ 0) (h : a % b = 0) :
    extEuclid a b = (0, 1) := by
  rw [extEuclid, dif_neg hb, if_pos h]

/-- Unfolding: the recursive case. -/
theorem extEuclid_of_mod_ne_zero {a b : ℕ} (hb : b ≠ 0) (h : a % b ≠ 0) :
    extEuclid a b =
      ((extEuclid b (a % b)).2,
        (extEuclid b (a % b)).1 - (extEuclid b (a % b)).2 * ((a / b : ℕ) : ℤ)) := by
  rw [extEuclid, dif_neg hb, if_neg h]

/-- Unfolding: no recursive call when `b = 0`. -/
theorem extEuclidCalls_zero_right (a : ℕ) : extEuclidCalls a 0 = 0 := by
  rw [extEuclidCalls]
  simp

/-- Unfolding: no recursive call when `a mod b = 0` (`b ≠ 0`). -/
theorem extEuclidCalls_of_mod_eq_zero {a b : ℕ} (hb : b ≠ 0) (h : a % b = 0) :
    extEuclidCalls a b = 0 := by
  rw [extEuclidCalls, dif_neg hb, if_pos h]

/-- Unfolding: one call plus the calls of `(b, a mod b)` in the recursive case. -/
theorem extEuclidCalls_of_mod_ne_zero {a b : ℕ} (hb : b ≠ 0) (h : a % b ≠ 0) :
    extEuclidCalls a b = extEuclidCalls b (a % b) + 1 := by
  rw [extEuclidCalls, dif_neg hb, if_neg h]

/-! ### Correctness -/

/-- **Correctness of the extended Euclidean algorithm** [PS10, Claim 44.5]: if
`ExtendedEuclid(a, b) = (x, y)` then `ax + by = gcd(a, b)`.

**Proof sketch.** Strong induction on `b`. If `b = 0` the value `(1, 0)` gives `a = gcd(a, 0)`.
If `b ∣ a` the value `(0, 1)` gives `b = gcd(a, b)`. Otherwise the recursive call returns
`(x, y)` with `bx + (a mod b)y = gcd(b, a mod b) = gcd(a, b)` ([PS10, Claim 44.4],
`Nat.gcd_rec`), and the regrouping `bx + (a mod b)y = b(x − ⌊a/b⌋y) + ay` (using
`a = b⌊a/b⌋ + a mod b`) shows the returned pair `(y, x − ⌊a/b⌋y)` is correct. -/
theorem extEuclid_spec (a b : ℕ) :
    (extEuclid a b).1 * a + (extEuclid a b).2 * b = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    by_cases hb : b = 0
    · subst hb
      rw [extEuclid_zero_right]
      simp
    by_cases h : a % b = 0
    · rw [extEuclid_of_mod_eq_zero hb h, Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)]
      simp
    · rw [extEuclid_of_mod_ne_zero hb h]
      have hrec := ih (a % b) (Nat.mod_lt _ (Nat.pos_of_ne_zero hb)) b
      have hgcd : Nat.gcd a b = Nat.gcd b (a % b) := by
        rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
      have hdiv : ((a : ℕ) : ℤ) = (b : ℤ) * ((a / b : ℕ) : ℤ) + ((a % b : ℕ) : ℤ) := by
        exact_mod_cast (Nat.div_add_mod a b).symm
      rw [hgcd, ← hrec]
      linear_combination (extEuclid b (a % b)).2 * hdiv

/-- The first Bézout coefficient of `ExtendedEuclid(a, N)` is the inverse of `a` modulo `N`
when `gcd(a, N) = 1`: the computation of inverses in `Z_N^*` [PS10, §2.6.4, proof of
Theorem 46.8; §2.9, the RSA exponent `d = e⁻¹ mod Φ(N)`]. -/
theorem extEuclid_inv (a N : ℕ) (h : Nat.gcd a N = 1) :
    ((extEuclid a N).1 : ZMod N) * (a : ZMod N) = 1 := by
  have hspec := extEuclid_spec a N
  rw [h] at hspec
  have hcast := congrArg (Int.cast : ℤ → ZMod N) hspec
  push_cast at hcast
  rwa [ZMod.natCast_self, mul_zero, add_zero] at hcast

/-! ### The recursive-call bound -/

/-- **The call bound** [PS10, Claim 43.3]: if `a > b` and `a < 2^n` then `ExtendedEuclid(a, b)`
makes at most `2n` recursive calls.

**Deviation:** the text's case 2 writes `b > 2^n` for `b ≥ 2^n`; the text's precondition
`b ≥ 0` is `b < a` here (with `b = 0` a base case).

**Proof sketch.** Induction on `n`, for all `a, b`. The base cases of the algorithm make no
call. In the recursive case let `r = a mod b < b`. Case `b < 2^n`: the call on `(b, r)` meets
the induction hypothesis, total `≤ 2n + 1`. Case `b ≥ 2^n`: then `a < 2^{n+1} ≤ 2b`, so
`⌊a/b⌋ = 1` and `r = a − b < 2^{n+1} − 2^n = 2^n`; the call on `(b, r)` either stops at once
or recurses on `(r, b mod r)` with `r < 2^n`, which meets the induction hypothesis: total
`≤ 2 + 2n`. -/
theorem extEuclidCalls_le (n : ℕ) : ∀ a b : ℕ, b < a → a < 2 ^ n → extEuclidCalls a b ≤ 2 * n := by
  induction n with
  | zero =>
    intro a b hba ha
    omega
  | succ n ih =>
    intro a b hba ha
    by_cases hb : b = 0
    · subst hb
      rw [extEuclidCalls_zero_right]
      omega
    by_cases h : a % b = 0
    · rw [extEuclidCalls_of_mod_eq_zero hb h]
      omega
    rw [extEuclidCalls_of_mod_ne_zero hb h]
    have hr : a % b < b := Nat.mod_lt _ (Nat.pos_of_ne_zero hb)
    by_cases hb' : b < 2 ^ n
    · have := ih b (a % b) hr hb'
      omega
    · push_neg at hb'
      -- `a mod b + b ≤ a`, hence `a mod b < 2^n`
      have hab : a % b + b ≤ a := by
        have hmod := Nat.mod_add_div a b
        have hq : 1 ≤ a / b := (Nat.one_le_div_iff (Nat.pos_of_ne_zero hb)).2 hba.le
        have hbq : b ≤ b * (a / b) := Nat.le_mul_of_pos_right _ hq
        omega
      have hr2 : a % b < 2 ^ n := by
        rw [pow_succ] at ha
        omega
      by_cases h2 : b % (a % b) = 0
      · rw [extEuclidCalls_of_mod_eq_zero h h2]
        omega
      · rw [extEuclidCalls_of_mod_ne_zero h h2]
        have := ih (a % b) (b % (a % b)) (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) hr2
        omega

end TCSlib.Cryptography.NumberTheory
