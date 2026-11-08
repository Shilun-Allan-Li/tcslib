/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Max

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The group `Z_N^*`, Euler's theorem and the RSA permutation

The multiplicative group `Z_N^* = (ZMod N)ˣ` of [PS10, §2.6.4] and the consequences of
Euler's theorem that the RSA and factoring candidates of [PS10, §2.7–§2.9] use:

* `Z_N^*` is the group of units of `ZMod N`; its elements are the residues `x ∈ [1, N−1]` with
  `gcd(x, N) = 1` [PS10, Theorem 46.8] (Mathlib: `ZMod.unitsEquivCoprime`,
  `ZMod.isUnit_iff_coprime`; `units_val_mem` records the range `[1, N−1]`);
* `|Z_N^*| = Φ(N)` with `Φ(p) = p − 1` and `Φ(pq) = (p−1)(q−1)` for distinct primes
  [PS10, Claim 47.2 and p. 47];
* Euler's theorem `a^{Φ(N)} = 1` [PS10, Theorem 47.10] is `ZMod.pow_totient`; Fermat's
  little theorem [PS10, Corollary 48.11] is `ZMod.pow_card_sub_one_eq_one`;
* exponents may be reduced modulo `Φ(N)` [PS10, Corollary 48.12];
* `x ↦ x^e` is a permutation of `Z_N^*` when `e ∈ Z^*_{Φ(N)}`, with inverse `y ↦ y^d` for
  `ed ≡ 1 (mod Φ(N))` [PS10, Theorem 54.3];
* the density `Φ(m)/m ≥ 1/(log₂ m + 1)` (inventory lemma C9), used to sample `Z^*_{Φ(N)}` by
  rejection in [PS10, Theorem 53.2].

**Deviation:** the text's `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`
(`Φ(p²) = p(p−1)`); the hypothesis is explicit here.

## Main definitions

None: `Z_N^*` is `(ZMod N)ˣ` and `Φ` is `Nat.totient` (Mathlib).

## Main results

* `TCSlib.Cryptography.NumberTheory.totient_prime_mul_prime`,
  `TCSlib.Cryptography.NumberTheory.card_units_zmod_prime_mul_prime` — `Φ(pq) = (p−1)(q−1)`
  and `|Z_{pq}^*|` [PS10, Claim 47.2].
* `TCSlib.Cryptography.NumberTheory.units_pow_mod_totient`,
  `TCSlib.Cryptography.NumberTheory.pow_mod_totient_modEq` — `a^x = a^{x mod Φ(N)}`
  [PS10, Corollary 48.12].
* `TCSlib.Cryptography.NumberTheory.rsa_pow_pow`,
  `TCSlib.Cryptography.NumberTheory.rsa_pow_bijective` — the RSA permutation and its inverse
  [PS10, Theorem 54.3].
* `TCSlib.Cryptography.NumberTheory.le_totient_mul_log_succ` — `m ≤ Φ(m)(⌊log₂ m⌋ + 1)` (C9).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.6.4: Theorem 46.8, Claim 47.2, Theorem 47.10, Corollaries 48.11–48.12; §2.9:
  Theorem 54.3.)
-/

namespace TCSlib.Cryptography.NumberTheory

open Nat

/-! ### The group `Z_N^*` -/

/-- The elements of `Z_N^*` are residues in `[1, N−1]` [PS10, Theorem 46.8, the description
`Z_N^* = {x ∈ [1, N−1] | gcd(x, N) = 1}`; the coprimality is `ZMod.unitsEquivCoprime`]. -/
theorem units_val_mem {N : ℕ} [Fact (1 < N)] (u : (ZMod N)ˣ) :
    1 ≤ (u : ZMod N).val ∧ (u : ZMod N).val ≤ N - 1 := by
  have hne : (u : ZMod N) ≠ 0 := u.ne_zero
  have hlt := (u : ZMod N).val_lt
  have hpos : (u : ZMod N).val ≠ 0 := fun h => hne (ZMod.val_eq_zero _ |>.1 h)
  omega

/-- **The totient of a product of two distinct primes** [PS10, Claim 47.2 and p. 47]:
`Φ(pq) = (p−1)(q−1)`; also `Φ(p) = p − 1` (`Nat.totient_prime`).

**Deviation:** `p ≠ q` is required (the text omits it). -/
theorem totient_prime_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    φ (p * q) = (p - 1) * (q - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq), Nat.totient_prime hp,
    Nat.totient_prime hq]

/-- `|Z_{pq}^*| = Φ(pq) = (p−1)(q−1)` for distinct primes [PS10, Claim 47.2,
"`|Z_N^*| = Φ(N)`"]. -/
theorem card_units_zmod_prime_mul_prime {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) : Fintype.card (ZMod (p * q))ˣ = (p - 1) * (q - 1) := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  rw [ZMod.card_units_eq_totient, totient_prime_mul_prime hp.out hq.out hpq]

/-! ### Euler's theorem and exponent reduction -/

/-- **Exponent reduction modulo `Φ(N)`** [PS10, Corollary 48.12]: for `a ∈ Z_N^*` and every
`x`, `a^x = a^{x mod Φ(N)}`.

**Proof sketch.** Write `x = Φ(N)⌊x/Φ(N)⌋ + (x mod Φ(N))` and apply Euler's theorem
`a^{Φ(N)} = 1` (`ZMod.pow_totient`). -/
theorem units_pow_mod_totient {N : ℕ} (a : (ZMod N)ˣ) (x : ℕ) : a ^ x = a ^ (x % φ N) := by
  conv_lhs => rw [← Nat.div_add_mod x (φ N)]
  rw [pow_add, pow_mul, ZMod.pow_totient, one_pow, one_mul]

/-- **Exponent reduction modulo `Φ(N)`, integer form** [PS10, Corollary 48.12]: for
`gcd(a, N) = 1`, `a^x ≡ a^{x mod Φ(N)} (mod N)`. -/
theorem pow_mod_totient_modEq {a N : ℕ} (h : Nat.Coprime a N) (x : ℕ) :
    a ^ x ≡ a ^ (x % φ N) [MOD N] := by
  conv_lhs => rw [← Nat.div_add_mod x (φ N)]
  rw [pow_add, pow_mul]
  calc (a ^ φ N) ^ (x / φ N) * a ^ (x % φ N) ≡ 1 ^ (x / φ N) * a ^ (x % φ N) [MOD N] :=
        ((Nat.ModEq.pow_totient h).pow _).mul_right _
    _ = a ^ (x % φ N) := by rw [one_pow, one_mul]

/-! ### The RSA permutation -/

/-- **RSA decryption inverts encryption** [PS10, Theorem 54.3]: if `ed ≡ 1 (mod Φ(N))` then
`(x^e)^d = x` for every `x ∈ Z_N^*`; so `y ↦ y^d` is the inverse of `x ↦ x^e`.

**Proof sketch.** `(x^e)^d = x^{ed} = x^{ed mod Φ(N)} = x^{1 mod Φ(N)} = x` by
`units_pow_mod_totient`. -/
theorem rsa_pow_pow {N e d : ℕ} (hed : e * d ≡ 1 [MOD φ N]) (x : (ZMod N)ˣ) :
    (x ^ e) ^ d = x := by
  rw [← pow_mul, units_pow_mod_totient x (e * d), show e * d % φ N = 1 % φ N from hed,
    ← units_pow_mod_totient, pow_one]

/-- **RSA is a permutation** [PS10, Theorem 54.3]: for `e` coprime to `Φ(N)` (i.e.
`e ∈ Z^*_{Φ(N)}`), `x ↦ x^e` is a bijection of `Z_N^*`.

**Proof sketch.** `|Z_N^*| = Φ(N)` (`ZMod.card_units_eq_totient`), and raising to a power
coprime to the group order is a bijection of any finite group (`powCoprime`; the inverse is
`y ↦ y^d` with `ed ≡ 1 (mod Φ(N))`, `rsa_pow_pow`). -/
theorem rsa_pow_bijective {N e : ℕ} [NeZero N] (he : Nat.Coprime e (φ N)) :
    Function.Bijective (fun x : (ZMod N)ˣ => x ^ e) := by
  have h : (Nat.card (ZMod N)ˣ).Coprime e := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact he.symm
  exact (powCoprime h).bijective

/-- **Existence of the decryption exponent** [PS10, Theorem 54.3, "let `d` be its inverse"]:
for `e ∈ Z^*_{Φ(N)}` and `N > 2` there is `d < Φ(N)` with `ed ≡ 1 (mod Φ(N))`. -/
theorem exists_rsa_inverse {N e : ℕ} (hN : 2 < N) (he : Nat.Coprime e (φ N)) :
    ∃ d, d < φ N ∧ e * d ≡ 1 [MOD φ N] := by
  have h1 : 1 < φ N := by
    have hpos : 0 < φ N := Nat.totient_pos.2 (by omega)
    have heven := Nat.totient_even hN
    rcases heven with ⟨k, hk⟩
    omega
  obtain ⟨d, hd⟩ := Nat.exists_mul_emod_eq_one_of_coprime he h1
  refine ⟨d % φ N, Nat.mod_lt _ (by omega), ?_⟩
  show e * (d % φ N) % φ N = 1 % φ N
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hd, Nat.one_mod_eq_one.2 (by omega)]

/-! ### Density of units -/

/-- The combinatorial core of C9: for a finite set `S` of naturals `≥ 2`,
`∏_{p ∈ S} p ≤ (∏_{p ∈ S} (p − 1)) · (|S| + 1)` (the `k` distinct elements `p_1 < ⋯ < p_k`
satisfy `p_i ≥ i + 1`, so `∏ p_i/(p_i − 1) ≤ ∏ (i+1)/i = k + 1`).

**Proof sketch.** Induction on `S` removing its maximum `a` (`Finset.induction_on_max`): the
remaining `k` elements lie in `[2, a)`, so `k + 2 ≤ a`, and then
`a · k' ≤ (a − 1)(k' + 1)` for `k' = k + 1`. -/
private theorem prod_le_prod_pred_mul_card (S : Finset ℕ) :
    (∀ p ∈ S, 2 ≤ p) → ∏ p ∈ S, p ≤ (∏ p ∈ S, (p - 1)) * (S.card + 1) := by
  induction S using Finset.induction_on_max with
  | h0 => intro; simp
  | step a s hlt ih =>
    intro hS
    have ha : 2 ≤ a := hS a (Finset.mem_insert_self _ _)
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hnot : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hcard : s.card ≤ a - 2 := by
      have hsub : s ⊆ Finset.Ico 2 a := fun x hx => Finset.mem_Ico.2 ⟨hs x hx, hlt x hx⟩
      have := Finset.card_le_card hsub
      rwa [Nat.card_Ico] at this
    rw [Finset.prod_insert hnot, Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
    have hstep : a * (s.card + 1) ≤ (a - 1) * (s.card + 1 + 1) := by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have : s.card + 1 ≤ a' := by omega
      nlinarith
    calc a * ∏ p ∈ s, p ≤ a * ((∏ p ∈ s, (p - 1)) * (s.card + 1)) := Nat.mul_le_mul_left _ (ih hs)
      _ = (∏ p ∈ s, (p - 1)) * (a * (s.card + 1)) := by ring
      _ ≤ (∏ p ∈ s, (p - 1)) * ((a - 1) * (s.card + 1 + 1)) := Nat.mul_le_mul_left _ hstep
      _ = (a - 1) * (∏ p ∈ s, (p - 1)) * (s.card + 1 + 1) := by ring

/-- **Density of units** (inventory lemma C9, used to sample `Z^*_{Φ(N)}` by rejection in
[PS10, Theorem 53.2]): for `m ≥ 1`, `Φ(m)/m ≥ 1/(⌊log₂ m⌋ + 1)`, i.e.
`m ≤ Φ(m) · (⌊log₂ m⌋ + 1)`.

**Proof sketch.** `Φ(m)/m = ∏_{p ∣ m} (1 − 1/p)` (`Nat.totient_eq_div_primeFactors_mul` /
`Nat.totient_mul_prod_primeFactors`). If `m` has `k` distinct prime factors
`p_1 < ⋯ < p_k` then `p_i ≥ i + 1`, so `∏ (1 − 1/p_i) ≥ ∏_{i=1}^k i/(i+1) = 1/(k+1)`; and
`2^k ≤ ∏ p_i ≤ m` gives `k ≤ ⌊log₂ m⌋`. Sub-obligations: the sorted enumeration of
`m.primeFactors` with `p_i ≥ i + 1` (`Finset.orderEmbOfFin`, strictly increasing from `≥ 2`),
the telescoping product, and `Finset.prod_le` monotonicity. -/
theorem le_totient_mul_log_succ (m : ℕ) (hm : 0 < m) : m ≤ φ m * (Nat.log 2 m + 1) := by
  have hS : ∀ p ∈ m.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hcore := prod_le_prod_pred_mul_card m.primeFactors hS
  have hcard : m.primeFactors.card ≤ Nat.log 2 m := by
    apply Nat.le_log_of_pow_le one_lt_two
    calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ hS
      _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hpos : 0 < ∏ p ∈ m.primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by have := hS p hp; omega
  have hkey := Nat.totient_mul_prod_primeFactors m
  refine Nat.le_of_mul_le_mul_right (c := ∏ p ∈ m.primeFactors, (p - 1)) ?_ hpos
  calc m * ∏ p ∈ m.primeFactors, (p - 1) = φ m * ∏ p ∈ m.primeFactors, p := hkey.symm
    _ ≤ φ m * ((∏ p ∈ m.primeFactors, (p - 1)) * (m.primeFactors.card + 1)) :=
        Nat.mul_le_mul_left _ hcore
    _ ≤ φ m * ((∏ p ∈ m.primeFactors, (p - 1)) * (Nat.log 2 m + 1)) := by gcongr
    _ = φ m * (Nat.log 2 m + 1) * ∏ p ∈ m.primeFactors, (p - 1) := by ring

end TCSlib.Cryptography.NumberTheory
