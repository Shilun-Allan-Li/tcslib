/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Modular exponentiation by repeated squaring

The loop `ModularExponentiation(a, x, N)` of [PS10, Algorithm 45.5]: `r ← 1`; while `x > 0`:
if `x` is odd then `r ← r·a mod N`; `x ← ⌊x/2⌋`; `a ← a² mod N`; return `r`. The loop is
written as a tail recursion on the state `(r, a, x)` instrumented with a counter of the
modular multiplications performed (one squaring per iteration, plus one multiplication when
`x` is odd). Its correctness `modExp a x N = a^x mod N` is proved, and the operation count of
[PS10, Theorem 45.6] is proved in the form "at most `2(⌊log₂ x⌋ + 1)` modular
multiplications" (`modExpMults_le`): the loop runs `⌊log₂ x⌋ + 1` times for `x > 0`.

**Deviation:** [PS10, Theorem 45.6] states the running time `O(log x · log² N)` for a machine
charging `log² N` per modular multiplication; the campaign has no binary-arithmetic machines
(plan D11), so the bound is stated as an explicit count of modular multiplications, with no
cost monad. The text's restriction `a ∈ [1, N]` is immaterial and dropped; the remark on
p. 46 that Euler's theorem "removes the restriction that `x < N`" refers to a restriction the
algorithm does not have. For `x = 0` the loop returns the literal `1` (not `1 mod N`), so the
correctness equation needs `x > 0` or `N ≠ 1`.

## Main definitions

* `TCSlib.Cryptography.NumberTheory.modExpLoop` — the instrumented loop.
* `TCSlib.Cryptography.NumberTheory.modExp` — `a^x mod N` by repeated squaring
  [PS10, Algorithm 45.5].
* `TCSlib.Cryptography.NumberTheory.modExpMults` — the number of modular multiplications.

## Main results

* `TCSlib.Cryptography.NumberTheory.modExp_eq` — correctness, `modExp a x N = a^x % N`.
* `TCSlib.Cryptography.NumberTheory.modExpMults_le` — at most `2(⌊log₂ x⌋ + 1)` modular
  multiplications [PS10, Theorem 45.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.6.3: Algorithm 45.5, Theorem 45.6.)
-/

namespace TCSlib.Cryptography.NumberTheory

/-! ### The loop -/

/-- The loop of [PS10, Algorithm 45.5] on the state `(r, a, x)` with the counter `c` of modular
multiplications performed so far: while `x > 0`, multiply `r` by `a` modulo `N` when `x` is odd
(one multiplication), halve `x` and square `a` modulo `N` (one multiplication). Returns the
final `r` and the final count. -/
def modExpLoop (N r a x c : ℕ) : ℕ × ℕ :=
  if hx : x = 0 then (r, c)
  else
    modExpLoop N (if x % 2 = 1 then r * a % N else r) (a * a % N) (x / 2)
      (c + if x % 2 = 1 then 2 else 1)
termination_by x
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hx) one_lt_two

/-- `ModularExponentiation(a, x, N)` [PS10, Algorithm 45.5]: `a^x mod N` by repeated
squaring, i.e. the product `∏_{i : x_i = 1} a^{2^i} mod N` over the binary digits of `x`. -/
def modExp (a x N : ℕ) : ℕ := (modExpLoop N 1 a x 0).1

/-- The number of modular multiplications performed by `ModularExponentiation(a, x, N)`
(squarings and multiplications by `r`), the cost measure of [PS10, Theorem 45.6]. -/
def modExpMults (a x N : ℕ) : ℕ := (modExpLoop N 1 a x 0).2

/-- Unfolding: the loop stops at `x = 0`. -/
theorem modExpLoop_zero (N r a c : ℕ) : modExpLoop N r a 0 c = (r, c) := by
  rw [modExpLoop]
  simp

/-- Unfolding: one iteration of the loop for `x ≠ 0`. -/
theorem modExpLoop_of_ne_zero (N r a x c : ℕ) (hx : x ≠ 0) :
    modExpLoop N r a x c =
      modExpLoop N (if x % 2 = 1 then r * a % N else r) (a * a % N) (x / 2)
        (c + if x % 2 = 1 then 2 else 1) := by
  rw [modExpLoop, dif_neg hx]

/-! ### Correctness -/

/-- The loop invariant: for `x > 0` the value is `r · a^x mod N`.

**Proof sketch.** Strong induction on `x`. If `x = 1` the loop multiplies once and stops. Else
the recursive call computes `r' · (a² mod N)^{⌊x/2⌋} mod N` with `r' ≡ r · a^{x mod 2}`, and
`r · a^{x mod 2} · (a²)^{⌊x/2⌋} = r · a^x` since `x = 2⌊x/2⌋ + x mod 2`; the reductions modulo
`N` commute with the products (`Nat.ModEq`). -/
theorem modExpLoop_fst (N : ℕ) :
    ∀ x r a c : ℕ, 0 < x → (modExpLoop N r a x c).1 = r * a ^ x % N := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro r a c hx
    rw [modExpLoop_of_ne_zero N r a x c hx.ne']
    by_cases hx2 : x / 2 = 0
    · have hx1 : x = 1 := by omega
      subst hx1
      rw [modExpLoop_zero]
      simp
    · rw [ih (x / 2) (Nat.div_lt_self hx one_lt_two) _ _ _ (Nat.pos_of_ne_zero hx2)]
      have h1 : (a * a % N) ^ (x / 2) ≡ (a * a) ^ (x / 2) [MOD N] := (Nat.mod_modEq _ _).pow _
      have h2 : (if x % 2 = 1 then r * a % N else r) ≡ r * a ^ (x % 2) [MOD N] := by
        split_ifs with hodd
        · rw [hodd, pow_one]
          exact Nat.mod_modEq _ _
        · have h0 : x % 2 = 0 := by omega
          rw [h0, pow_zero, mul_one]
      have h3 := h2.mul h1
      have hx' : r * a ^ (x % 2) * (a * a) ^ (x / 2) = r * a ^ x := by
        rw [← pow_two, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega
      rw [hx'] at h3
      exact h3

/-- **Correctness of repeated squaring** [PS10, Algorithm 45.5]: for `x > 0`,
`modExp a x N = a^x mod N`. -/
theorem modExp_eq (a x N : ℕ) (hx : 0 < x) : modExp a x N = a ^ x % N :=
  (modExpLoop_fst N x 1 a 0 hx).trans (by rw [one_mul])

/-- The loop returns the literal `1` on `x = 0` (the initial value of `r`). -/
theorem modExp_zero (a N : ℕ) : modExp a 0 N = 1 := by
  rw [modExp, modExpLoop_zero]

/-- Correctness for every exponent when `N ≠ 1` (then `1 = 1 mod N`). -/
theorem modExp_eq_of_ne_one (a x N : ℕ) (hN : N ≠ 1) : modExp a x N = a ^ x % N := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [modExp_zero, pow_zero, Nat.one_mod_eq_one.2 hN]
  · exact modExp_eq a x N hx

/-- Correctness in `ZMod N`: the computed residue is `a^x`. -/
theorem modExp_cast (a x N : ℕ) (hx : 0 < x) : ((modExp a x N : ℕ) : ZMod N) = (a : ZMod N) ^ x := by
  rw [modExp_eq a x N hx, ZMod.natCast_mod, Nat.cast_pow]

/-! ### The operation count -/

/-- The counter of the loop: at most `2(⌊log₂ x⌋ + 1)` multiplications are added for `x > 0`,
none for `x = 0`.

**Proof sketch.** Strong induction on `x`: one iteration adds at most `2` and halves `x`, and
`⌊log₂ ⌊x/2⌋⌋ = ⌊log₂ x⌋ − 1` for `x ≥ 2` (`Nat.log_div_base`); `x = 1` is the last
iteration. -/
theorem modExpLoop_snd_le (N : ℕ) :
    ∀ x r a c : ℕ, (modExpLoop N r a x c).2 ≤ c + (if x = 0 then 0 else 2 * (Nat.log 2 x + 1)) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro r a c
    by_cases hx : x = 0
    · subst hx
      rw [modExpLoop_zero]
      simp
    rw [modExpLoop_of_ne_zero N r a x c hx, if_neg hx]
    have hrec := ih (x / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hx) one_lt_two)
      (if x % 2 = 1 then r * a % N else r) (a * a % N) (c + if x % 2 = 1 then 2 else 1)
    by_cases hx2 : x / 2 = 0
    · rw [if_pos hx2] at hrec
      have hx1 : x = 1 := by omega
      subst hx1
      simp only [Nat.log_one_right, zero_add, mul_one]
      split_ifs at hrec ⊢ <;> omega
    · rw [if_neg hx2, Nat.log_div_base] at hrec
      have hlog : 1 ≤ Nat.log 2 x := Nat.log_pos one_lt_two (by omega)
      split_ifs at hrec ⊢ <;> omega

/-- **The operation count of repeated squaring** [PS10, Theorem 45.6]: `ModularExponentiation`
performs at most `2(⌊log₂ x⌋ + 1)` modular multiplications (each iteration of the loop
performs at most two, and there are `⌊log₂ x⌋ + 1` iterations).

**Deviation:** operation count instead of the text's `O(log x · log² N)` machine time (D11). -/
theorem modExpMults_le (a x N : ℕ) : modExpMults a x N ≤ 2 * (Nat.log 2 x + 1) := by
  have := modExpLoop_snd_le N x 1 a 0
  rw [zero_add] at this
  refine this.trans ?_
  split_ifs <;> omega

end TCSlib.Cryptography.NumberTheory
