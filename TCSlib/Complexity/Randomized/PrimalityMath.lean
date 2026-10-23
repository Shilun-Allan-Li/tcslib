/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Totient
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.SpaceComplexity.Machines.Bin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Solovay–Strassen primality testing: the number theory

The mathematical half of [AB09, §7.2.2]: the language `PRIMES`, the symbol `QR_N(A)`, the
three number-theoretic facts the book quotes, and the error analysis of the Solovay–Strassen
test "pick `A`, reject unless `gcd(A, N) = 1` and `(A/N) ≡ A^{(N−1)/2} (mod N)`", including
the sampling of `A` from a random bit string. The class statement `PRIMES ∈ coRP` consumes
`Randomized.eulerLiarRounds` and the bounds below.

## Main definitions

* `Randomized.PRIMES` — the set of primes.
* `Randomized.qrSymbol` — the book's `QR_N(A) ∈ {0, ±1}`.
* `Randomized.jacobiSymZMod` — the Jacobi symbol `(x/N)` of a residue, in `ZMod N`.
* `Randomized.IsEulerLiar` — `A` passes the test for `N`.
* `Randomized.eulerLiarSubgroup` — the Euler liars among the units of `ZMod N`.
* `Randomized.eulerSample`, `Randomized.eulerLiarRounds` — `A := 1 + (val r mod (N−1))`
  from random bits, and the conjunction of `k` independent rounds.

## Main results

* `Randomized.qrSymbol_eq_legendreSym`, `Randomized.jacobiSym_eq_prod_qrSymbol` — `QR_P` is
  Mathlib's `legendreSym`; Mathlib's `jacobiSym` is the book's product `∏ QR_{P_i}(A)`.
* `Randomized.qrSymbol_eq_pow` — fact 1 (Euler's criterion).
* `Randomized.eulerLiarSubgroup_ne_top`, `Randomized.two_mul_card_eulerLiarSubgroup_le` —
  fact 3.
* `Randomized.two_mul_card_filter_isEulerLiar_le` — at most `(N−1)/2` liars in `[1, N)`.
* `Randomized.isEulerLiar_of_prime`, `Randomized.eulerLiarRounds_of_prime` — for an odd
  prime `N` every `A` passes.
* `Randomized.randProb_isEulerLiar_le`, `Randomized.randProb_eulerLiarRounds_le`,
  `Randomized.randProb_eulerLiarRounds_two_le` — the error bounds.

## Divergences

* Fact 1 is stated for every `A`, not only `A ∈ [N−1]` (both sides vanish when `N ∣ A`).
* Fact 2 (the Jacobi symbol is computable in time `O(log A · log N)`) is algorithmic and
  belongs to the class half; here only the book's definition of the symbol is matched.
* Fact 3 is proved as the book states it (the liars among the units form a proper subgroup,
  hence at most half of them) and also counted over all of `[1, N)`, since non-units fail the
  `gcd` test.
* The book picks `A` uniformly in `[1, N)`. A random string `r ∈ {0,1}^ℓ` gives
  `A = 1 + (val r mod (N−1))`, which is not exactly uniform; the liar probability is bounded
  by `1/2 + (N−1)/2^{ℓ+1}` (the bias term is explicit). The book's "repeat a constant number
  of times" is made concrete: two rounds with `8N ≤ 2^ℓ` give liar probability `≤ 1/3`, the
  `2/3` threshold of `Randomized.InRP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset NumberTheorySymbols

/-! ### PRIMES and the symbol `QR_N(A)` -/

/-- The language `PRIMES = {N : N is a prime number}`, as a set of naturals.
[AB09, §7.2.2, p.128] -/
def PRIMES : Set ℕ := {N | N.Prime}

open Classical in
/-- The book's `QR_N(A)`: `0` if `gcd(A, N) ≠ 1`, `+1` if `A` is a square modulo `N`, and `−1`
otherwise. [AB09, §7.2.2, p.128] -/
noncomputable def qrSymbol (N A : ℕ) : ℤ :=
  if Nat.Coprime A N then (if IsSquare (A : ZMod N) then 1 else -1) else 0

/-- `QR_N(A)` takes only the values `0`, `1`, `−1`. [AB09, §7.2.2, p.128] -/
theorem qrSymbol_trichotomy (N A : ℕ) :
    qrSymbol N A = 0 ∨ qrSymbol N A = 1 ∨ qrSymbol N A = -1 := by
  unfold qrSymbol
  split_ifs <;> simp

/-- For a prime `p`, `p ∤ A` is the same as `A ≢ 0 (mod p)` and as `gcd(A, p) = 1`. -/
private theorem coprime_iff_natCast_ne_zero {p : ℕ} (hp : p.Prime) (A : ℕ) :
    Nat.Coprime A p ↔ (A : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]

/-- For a prime `p`, the book's `QR_p(A)` is Mathlib's Legendre symbol `(A/p)`. -/
theorem qrSymbol_eq_legendreSym {p : ℕ} [Fact p.Prime] (A : ℕ) :
    qrSymbol p A = legendreSym p A := by
  have hcop := coprime_iff_natCast_ne_zero (Fact.out : p.Prime) A
  unfold qrSymbol
  by_cases h : Nat.Coprime A p
  · rw [if_pos h]
    by_cases hs : IsSquare (A : ZMod p)
    · rw [if_pos hs, (legendreSym.eq_one_iff' (p := p) (hcop.1 h)).2 hs]
    · rw [if_neg hs, (legendreSym.eq_neg_one_iff' (p := p)).2 hs]
  · rw [if_neg h]
    have h0 : (A : ZMod p) = 0 := by
      by_contra h0
      exact h (hcop.2 h0)
    exact ((legendreSym.eq_zero_iff p _).2 (by simpa using h0)).symm

/-- Mathlib's Jacobi symbol `jacobiSym A N` is the book's `(N/A) = ∏ᵢ QR_{Pᵢ}(A)` over the
prime factors `P₁, …, P_k` of `N` (with multiplicity). [AB09, §7.2.2, fact 2] -/
theorem jacobiSym_eq_prod_qrSymbol (A N : ℕ) :
    jacobiSym A N = (N.primeFactorsList.map (qrSymbol · A)).prod := by
  unfold jacobiSym
  suffices ∀ (l : List ℕ) (H : ∀ p ∈ l, p.Prime),
      (l.pmap (fun p pp => @legendreSym p ⟨pp⟩ (A : ℤ)) H).prod =
        (l.map (qrSymbol · A)).prod from this _ _
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p l ih =>
    intro H
    simp only [List.pmap, List.map_cons, List.prod_cons]
    rw [ih fun q hq => H q (List.mem_cons_of_mem _ hq),
      @qrSymbol_eq_legendreSym p ⟨H p (by simp)⟩]

/-- **Fact 1 (Euler's criterion).** For an odd prime `p`, `QR_p(A) ≡ A^{(p−1)/2} (mod p)`.
[AB09, §7.2.2, fact 1] -/
theorem qrSymbol_eq_pow {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (A : ℕ) :
    (qrSymbol p A : ZMod p) = (A : ZMod p) ^ ((p - 1) / 2) := by
  have hodd := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp)
  rw [qrSymbol_eq_legendreSym, legendreSym.eq_pow, show p / 2 = (p - 1) / 2 by omega]
  simp

/-! ### Euler liars -/

/-- `A` is an *Euler liar* for `N`: it passes the Solovay–Strassen test, i.e.
`gcd(A, N) = 1` and `(A/N) ≡ A^{(N−1)/2} (mod N)`. [AB09, §7.2.2, p.128] -/
def IsEulerLiar (N A : ℕ) : Prop :=
  Nat.Coprime A N ∧ ((jacobiSym A N : ℤ) : ZMod N) = (A : ZMod N) ^ ((N - 1) / 2)

/-- The test is decidable. -/
instance (N A : ℕ) : Decidable (IsEulerLiar N A) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The test in integer arithmetic: `gcd(A, N) = 1` and `(A/N) mod N = (A^{(N−1)/2} mod N)`. -/
theorem isEulerLiar_iff_emod (N A : ℕ) :
    IsEulerLiar N A ↔
      Nat.gcd A N = 1 ∧ jacobiSym A N % N = ((A ^ ((N - 1) / 2) % N : ℕ) : ℤ) := by
  unfold IsEulerLiar
  have h : (A : ZMod N) ^ ((N - 1) / 2) = (((A ^ ((N - 1) / 2) : ℕ) : ℤ) : ZMod N) := by
    push_cast; rfl
  rw [h, ZMod.intCast_eq_intCast_iff', Int.natCast_mod]

/-- **Converse.** For an odd prime `p`, every `A` with `gcd(A, p) = 1` passes the test.
[AB09, §7.2.2, p.128] -/
theorem isEulerLiar_of_prime {p A : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hA : Nat.Coprime A p) :
    IsEulerLiar p A := by
  haveI := Fact.mk hp
  refine ⟨hA, ?_⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym, ← qrSymbol_eq_legendreSym]
  exact qrSymbol_eq_pow hp2 A

/-- For an odd prime `p`, every `A ∈ [1, p)` passes the test. [AB09, §7.2.2, p.128] -/
theorem isEulerLiar_of_prime_of_mem_Ico {p A : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : A ∈ Ico 1 p) : IsEulerLiar p A := by
  rw [mem_Ico] at hA
  refine isEulerLiar_of_prime hp hp2 ((coprime_iff_natCast_ne_zero hp A).2 ?_)
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hA.1 hA.2

/-- The Jacobi symbol `(x/N)` of a residue `x`, read in `ZMod N`. -/
def jacobiSymZMod (N : ℕ) (x : ZMod N) : ZMod N :=
  ((jacobiSym (x.val : ℤ) N : ℤ) : ZMod N)

/-- For `A : ℕ`, `jacobiSymZMod N A` is `(A/N)` cast to `ZMod N`. -/
theorem jacobiSymZMod_natCast (N : ℕ) [NeZero N] (A : ℕ) :
    jacobiSymZMod N (A : ZMod N) = ((jacobiSym A N : ℤ) : ZMod N) := by
  unfold jacobiSymZMod
  rw [ZMod.val_natCast, jacobiSym.mod_left' (a₂ := (A : ℤ))]
  rw [Int.natCast_mod, Int.emod_emod]

/-- `jacobiSymZMod N` is multiplicative. -/
theorem jacobiSymZMod_mul (N : ℕ) [NeZero N] (x y : ZMod N) :
    jacobiSymZMod N (x * y) = jacobiSymZMod N x * jacobiSymZMod N y := by
  unfold jacobiSymZMod
  rw [← Int.cast_mul, ← jacobiSym.mul_left, jacobiSym.mod_left' (a₂ := (x.val * y.val : ℤ))]
  rw [ZMod.val_mul, Int.natCast_mod, Int.emod_emod, Nat.cast_mul]

/-- `(1/N) = 1`. -/
theorem jacobiSymZMod_one (N : ℕ) [NeZero N] : jacobiSymZMod N 1 = 1 := by
  have h := jacobiSymZMod_natCast N 1
  rw [Nat.cast_one] at h
  rw [h, Nat.cast_one, jacobiSym.one_left, Int.cast_one]

/-- The Euler liars among the units of `ZMod N`, as a subgroup:
`{u | (u/N) ≡ u^{(N−1)/2} (mod N)}`. [AB09, §7.2.2, fact 3] -/
def eulerLiarSubgroup (N : ℕ) [NeZero N] : Subgroup (ZMod N)ˣ where
  carrier := {u | jacobiSymZMod N u = (u : ZMod N) ^ ((N - 1) / 2)}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one, one_pow]
    exact jacobiSymZMod_one N
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rw [jacobiSymZMod_mul, hu, hv, mul_pow]
  inv_mem' := by
    intro u hu
    simp only [Set.mem_setOf_eq] at *
    have h1 := jacobiSymZMod_mul N ((u⁻¹ : (ZMod N)ˣ) : ZMod N) (u : ZMod N)
    rw [Units.inv_mul, jacobiSymZMod_one, hu] at h1
    have h2 : (u : ZMod N) ^ ((N - 1) / 2) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) ^ ((N - 1) / 2) = 1 :=
      by rw [← mul_pow, Units.mul_inv, one_pow]
    linear_combination (-((u⁻¹ : (ZMod N)ˣ) : ZMod N) ^ ((N - 1) / 2)) * h1 -
      jacobiSymZMod N ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * h2

/-- Membership in `eulerLiarSubgroup N` is the Euler congruence. -/
theorem mem_eulerLiarSubgroup {N : ℕ} [NeZero N] {u : (ZMod N)ˣ} :
    u ∈ eulerLiarSubgroup N ↔ jacobiSymZMod N u = (u : ZMod N) ^ ((N - 1) / 2) :=
  Iff.rfl

/-- For odd `N > 1`, an Euler liar `u` satisfies `u^{N−1} = 1`, since `(u/N) = ±1`. -/
theorem pow_sub_one_eq_one_of_mem_eulerLiarSubgroup {N : ℕ} [NeZero N] (hN : 1 < N)
    (hodd : Odd N) {u : (ZMod N)ˣ} (hu : u ∈ eulerLiarSubgroup N) :
    (u : ZMod N) ^ (N - 1) = 1 := by
  haveI : Fact (1 < N) := ⟨hN⟩
  have hodd' := Nat.odd_iff.1 hodd
  rw [mem_eulerLiarSubgroup] at hu
  rw [show N - 1 = 2 * ((N - 1) / 2) by omega, pow_mul', ← hu]
  unfold jacobiSymZMod at hu ⊢
  rcases jacobiSym.trichotomy ((u : ZMod N).val : ℤ) N with h | h | h <;> rw [h] at hu ⊢
  · exfalso
    rw [Int.cast_zero, ← Units.val_pow_eq_pow_val] at hu
    exact (Units.ne_zero _) hu.symm
  · simp
  · simp

/-- If `p² ∣ N` (`N` odd), some unit of `ZMod N` is not an Euler liar.

**Proof sketch.** Let `x = N/p`, so `x² = 0` in `ZMod N`. Then `(1 + x)^{N−1} = 1 + (N−1)x
= 1 − x ≠ 1`, while every Euler liar `u` has `u^{N−1} = 1`
(`pow_sub_one_eq_one_of_mem_eulerLiarSubgroup`); so the unit `1 + x` is not a liar. -/
private theorem exists_not_mem_of_sq_dvd {N p : ℕ} [NeZero N] (hN : 1 < N) (hodd : Odd N)
    (hp : p.Prime) (hpN : p * p ∣ N) : ∃ u : (ZMod N)ˣ, u ∉ eulerLiarSubgroup N := by
  obtain ⟨k, hk⟩ := hpN
  set x : ZMod N := ((p * k : ℕ) : ZMod N) with hxdef
  have hx2 : x * x = 0 := by
    rw [hxdef, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact ⟨k, by rw [hk]; ring⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
    omega
  have hx0 : x ≠ 0 := by
    rw [hxdef, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have h2 := hp.two_le
    have hpk : 0 < p * k := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hk0)
    have := Nat.le_of_dvd hpk hd
    rw [hk] at this
    nlinarith
  have hpow : ∀ n : ℕ, (1 + x) ^ n = 1 + n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih]
      push_cast
      linear_combination (n : ZMod N) * hx2
  let u : (ZMod N)ˣ := ⟨1 + x, 1 - x, by linear_combination -hx2, by linear_combination -hx2⟩
  refine ⟨u, fun hu => hx0 ?_⟩
  have h1 := pow_sub_one_eq_one_of_mem_eulerLiarSubgroup hN hodd hu
  have hc : ((N - 1 : ℕ) : ZMod N) = -1 := by
    rw [Nat.cast_sub hN.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  change (1 + x) ^ (N - 1) = 1 at h1
  rw [hpow, hc] at h1
  linear_combination -h1

/-- If `N` is odd and composite and no `p²` divides `N`, some unit of `ZMod N` is not an
Euler liar.

**Proof sketch.** Write `N = p·m` with `p ∤ m`, `m > 1`. The CRT residue `A ≡ b (mod p)`,
`A ≡ 1 (mod m)` for a non-square `b` has `(A/N) = (b/p)(1/m) = −1` but
`A^{(N−1)/2} ≡ 1 (mod m)`; a liar would have `A^{(N−1)/2} ≡ −1 (mod m)`, impossible as
`m > 2`. -/
private theorem exists_not_mem_of_not_sq_dvd {N : ℕ} [NeZero N] (hN : 1 < N) (hodd : Odd N)
    (hnp : ¬ N.Prime) (hsq : ∀ p, p.Prime → ¬ p * p ∣ N) :
    ∃ u : (ZMod N)ˣ, u ∉ eulerLiarSubgroup N := by
  set p := N.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd N
  rw [← hpdef] at hm
  have hpm : ¬ p ∣ m := fun h => hsq p hp (by rw [hm]; exact Nat.mul_dvd_mul_left p h)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hm1 : m ≠ 1 := fun h => hnp (by rw [hm, h, mul_one]; exact hp)
  have hpmodd : Odd p ∧ Odd m := Nat.odd_mul.1 (by rw [← hm]; exact hodd)
  have hmodd : Odd m := hpmodd.2
  have hp2 : p ≠ 2 := by
    intro h
    have := hpmodd.1
    rw [h] at this
    exact (by decide : ¬ Odd 2) this
  haveI := Fact.mk hp
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (IsSquare.zero)
  let a := Nat.chineseRemainder hcop b.val 1
  have ha1 : ((a : ℕ) : ZMod p) = b := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 a.2.1, ZMod.natCast_zmod_val]
  have ha2 : ((a : ℕ) : ZMod m) = 1 := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 a.2.2, Nat.cast_one]
  have hcopp : Nat.Coprime a p := (coprime_iff_natCast_ne_zero hp a).2 (by rw [ha1]; exact hb0)
  have hcopm : Nat.Coprime a m := by
    have := a.2.2.gcd_eq
    rwa [Nat.gcd_one_left] at this
  have hcopN : Nat.Coprime a N := by
    rw [hm]
    exact Nat.Coprime.mul_right hcopp hcopm
  refine ⟨ZMod.unitOfCoprime a hcopN, fun hu => ?_⟩
  rw [mem_eulerLiarSubgroup, ZMod.coe_unitOfCoprime, jacobiSymZMod_natCast] at hu
  have hJp : jacobiSym (a : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff' (p := p), ha1]
    exact hb
  have hJm : jacobiSym (a : ℤ) m = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1), jacobiSym.one_left]
    exact_mod_cast a.2.2
  have hJ : jacobiSym (a : ℤ) N = -1 := by
    rw [hm, jacobiSym.mul_right' _ hp.ne_zero hm0, hJp, hJm, mul_one]
  rw [hJ] at hu
  have hmN : m ∣ N := ⟨p, by rw [hm, mul_comm]⟩
  have h := congrArg (ZMod.castHom hmN (ZMod m)) hu
  simp only [Int.cast_neg, Int.cast_one, map_neg, map_one, map_pow, map_natCast] at h
  rw [ha2, one_pow] at h
  have h2 : ((2 : ℕ) : ZMod m) = 0 := by
    push_cast
    linear_combination -h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  obtain ⟨j, hj⟩ := hmodd
  omega

/-- **Fact 3, subgroup form.** For odd composite `N`, the Euler liars form a *proper* subgroup
of `(ZMod N)ˣ`. [AB09, §7.2.2, fact 3]

**Proof sketch.** Exhibit a non-liar unit. If `p² ∣ N` for a prime `p`, take `u = 1 + N/p`:
`(N/p)² ≡ 0`, so `u^n = 1 + n·N/p` and `u^{N−1} = 1 − N/p ≠ 1`, while every liar has
`u^{N−1} = ((u/N))² = 1`. Otherwise `N = p·m` with `p ∤ m`, `m > 1` odd; by CRT pick
`A ≡ b (mod p)` with `b` a non-square and `A ≡ 1 (mod m)`. Then
`(A/N) = (A/p)(A/m) = −1·1`, and if `A^{(N−1)/2} ≡ −1 (mod N)` then reducing mod `m` gives
`1 ≡ −1 (mod m)`, i.e. `m ∣ 2`, impossible. -/
theorem eulerLiarSubgroup_ne_top {N : ℕ} [NeZero N] (hN : 1 < N) (hodd : Odd N)
    (hnp : ¬ N.Prime) : eulerLiarSubgroup N ≠ ⊤ := by
  have hex : ∃ u : (ZMod N)ˣ, u ∉ eulerLiarSubgroup N := by
    by_cases h : ∃ p, p.Prime ∧ p * p ∣ N
    · obtain ⟨p, hp, hpN⟩ := h
      exact exists_not_mem_of_sq_dvd hN hodd hp hpN
    · push_neg at h
      exact exists_not_mem_of_not_sq_dvd hN hodd hnp h
  obtain ⟨u, hu⟩ := hex
  intro htop
  exact hu (htop ▸ Subgroup.mem_top u)

/-- **Fact 3.** For odd composite `N`, at most half of the units `A ∈ (ℤ/N)ˣ` satisfy
`(A/N) ≡ A^{(N−1)/2} (mod N)`. [AB09, §7.2.2, fact 3] -/
theorem two_mul_card_eulerLiarSubgroup_le {N : ℕ} [NeZero N] (hN : 1 < N) (hodd : Odd N)
    (hnp : ¬ N.Prime) : 2 * Nat.card (eulerLiarSubgroup N) ≤ N.totient := by
  have hne := eulerLiarSubgroup_ne_top hN hodd hnp
  have hidx : (eulerLiarSubgroup N).index ≠ 1 := mt Subgroup.index_eq_one.1 hne
  have hidx0 : (eulerLiarSubgroup N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard := Subgroup.card_mul_index (eulerLiarSubgroup N)
  rw [Nat.card_eq_fintype_card (α := (ZMod N)ˣ), ZMod.card_units_eq_totient] at hcard
  rw [← hcard, mul_comm 2]
  exact Nat.mul_le_mul_left _ (by omega)

/-- **Fact 3, over `[1, N)`.** For odd composite `N`, at most `(N−1)/2` of the `A ∈ [1, N)`
pass the test. [AB09, §7.2.2, p.128]

**Proof sketch.** A liar is coprime to `N`, so `A ↦ (A : ZMod N)` injects the liars of
`[1, N)` into the subgroup of Euler liars, whose order is at most `φ(N)/2 ≤ (N−1)/2`
(`two_mul_card_eulerLiarSubgroup_le`, `Nat.totient_lt`). -/
theorem two_mul_card_filter_isEulerLiar_le {N : ℕ} (hN : 1 < N) (hodd : Odd N)
    (hnp : ¬ N.Prime) : 2 * ((Ico 1 N).filter (IsEulerLiar N)).card ≤ N - 1 := by
  classical
  haveI : NeZero N := ⟨by omega⟩
  have hle : ((Ico 1 N).filter (IsEulerLiar N)).card ≤
      ((univ.filter (· ∈ eulerLiarSubgroup N)).map ⟨Units.val, Units.val_injective⟩).card := by
    refine Finset.card_le_card_of_injOn (fun A => (A : ZMod N)) ?_ ?_
    · intro A hA
      rw [coe_filter] at hA
      obtain ⟨-, hcop, hliar⟩ := hA
      rw [coe_map, Set.mem_image]
      refine ⟨ZMod.unitOfCoprime A hcop, ?_, ZMod.coe_unitOfCoprime A hcop⟩
      rw [coe_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [mem_eulerLiarSubgroup, ZMod.coe_unitOfCoprime, jacobiSymZMod_natCast]
      exact hliar
    · intro A hA B hB hAB
      rw [coe_filter, Set.mem_setOf_eq, mem_Ico] at hA hB
      have := (ZMod.natCast_eq_natCast_iff' A B N).1 hAB
      rwa [Nat.mod_eq_of_lt hA.1.2, Nat.mod_eq_of_lt hB.1.2] at this
  have hH : (univ.filter (· ∈ eulerLiarSubgroup N)).card = Nat.card (eulerLiarSubgroup N) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  rw [card_map] at hle
  replace hle := hle.trans (le_of_eq (by convert hH))
  have h1 := two_mul_card_eulerLiarSubgroup_le hN hodd hnp
  have h2 := Nat.totient_lt N hN
  omega

/-! ### Sampling `A` from random bits -/

open Complexity.LogProg (bitsVal bitsVal_lt_two_pow eq_of_bitsVal_eq)

/-- The candidate `A := 1 + (val r mod (N−1)) ∈ [1, N)` drawn from the random string `r`,
read little-endian by `Complexity.LogProg.bitsVal`. -/
def eulerSample (N : ℕ) (r : List Bool) : ℕ :=
  1 + bitsVal r % (N - 1)

/-- For `N > 1`, the sampled candidate lies in `[1, N)`. -/
theorem eulerSample_mem_Ico {N : ℕ} (hN : 1 < N) (r : List Bool) :
    eulerSample N r ∈ Ico 1 N := by
  have := Nat.mod_lt (bitsVal r) (show 0 < N - 1 by omega)
  rw [mem_Ico, eulerSample]
  omega

/-- **Single round.** For odd composite `N`, `A = eulerSample N r` with `r ∈ {0,1}^ℓ` is an
Euler liar with probability at most `1/2 + (N−1)/2^{ℓ+1}`. [AB09, §7.2.2, p.128]

**Proof sketch.** Write `K = N − 1` and `v = val r < 2^ℓ`. The map
`r ↦ (1 + v mod K, v / K)` is injective (bit strings are determined by their value, and `v` by
quotient and remainder) and sends liar strings into `S × [0, 2^ℓ/K]`, with `S` the liars in
`[1, N)`, `2|S| ≤ K`. Hence `2·#liar strings ≤ 2|S|(2^ℓ/K + 1) ≤ K·(2^ℓ/K) + K ≤ 2^ℓ + K`. -/
theorem randProb_isEulerLiar_le {N : ℕ} (hN : 1 < N) (hodd : Odd N) (hnp : ¬ N.Prime)
    (ℓ : ℕ) :
    randProb ℓ (fun r => IsEulerLiar N (eulerSample N r)) ≤
      1 / 2 + ((N - 1 : ℕ) : ℚ) / 2 ^ (ℓ + 1) := by
  classical
  set K := N - 1 with hK
  have hK0 : 0 < K := by omega
  set S := (Ico 1 N).filter (IsEulerLiar N)
  have hS : 2 * S.card ≤ K := two_mul_card_filter_isEulerLiar_le hN hodd hnp
  set F := univ.filter fun r : Fin ℓ → Bool => IsEulerLiar N (eulerSample N (List.ofFn r))
  have hF : F.card ≤ (S ×ˢ range (2 ^ ℓ / K + 1)).card := by
    refine Finset.card_le_card_of_injOn
      (fun r => (eulerSample N (List.ofFn r), bitsVal (List.ofFn r) / K)) ?_ ?_
    · intro r hr
      rw [coe_filter, Set.mem_setOf_eq] at hr
      rw [coe_product, Set.mem_prod, coe_filter, coe_range, Set.mem_setOf_eq, Set.mem_Iio]
      refine ⟨⟨eulerSample_mem_Ico hN _, hr.2⟩, Nat.lt_succ_of_le ?_⟩
      have := bitsVal_lt_two_pow (List.ofFn r)
      rw [List.length_ofFn] at this
      exact Nat.div_le_div_right this.le
    · intro r _ r' _ h
      simp only [Prod.mk.injEq, eulerSample, Nat.add_left_cancel_iff] at h
      have hv : bitsVal (List.ofFn r) = bitsVal (List.ofFn r') := by
        rw [← Nat.div_add_mod (bitsVal (List.ofFn r)) K,
          ← Nat.div_add_mod (bitsVal (List.ofFn r')) K, h.1, h.2]
      exact List.ofFn_injective (eq_of_bitsVal_eq (by simp) hv)
  rw [card_product, card_range] at hF
  have hcount : 2 * F.card ≤ 2 ^ ℓ + K := by
    have h1 : 2 * F.card ≤ 2 * S.card * (2 ^ ℓ / K) + 2 * S.card := by nlinarith
    have h2 : 2 * S.card * (2 ^ ℓ / K) ≤ K * (2 ^ ℓ / K) := Nat.mul_le_mul_right _ hS
    have h3 : K * (2 ^ ℓ / K) ≤ 2 ^ ℓ := Nat.mul_div_le (2 ^ ℓ) K
    omega
  have hq : (2 * F.card : ℚ) ≤ 2 ^ ℓ + K := by exact_mod_cast hcount
  unfold randProb
  rw [div_le_iff₀ (by positivity)]
  have e : (1 / 2 + (K : ℚ) / 2 ^ (ℓ + 1)) * 2 ^ ℓ = ((2 : ℚ) ^ ℓ + K) / 2 := by
    rw [pow_succ]
    field_simp
  rw [e]
  linarith

/-- `k` independent rounds of the test on consecutive `ℓ`-bit blocks of `r`: `true` iff every
round's candidate is an Euler liar. [AB09, §7.2.2, p.128: "repeating the test"] -/
def eulerLiarRounds (N ℓ : ℕ) : ℕ → List Bool → Bool
  | 0, _ => true
  | k + 1, r => decide (IsEulerLiar N (eulerSample N (r.take ℓ))) &&
      eulerLiarRounds N ℓ k (r.drop ℓ)

/-- Two rounds on `ℓ`-bit blocks read only the first `2ℓ` bits. -/
theorem eulerLiarRounds_two_take (N ℓ : ℕ) (r : List Bool) :
    eulerLiarRounds N ℓ 2 (r.take (ℓ * 2)) = eulerLiarRounds N ℓ 2 r := by
  simp [eulerLiarRounds, List.take_take, List.drop_take, show ℓ * 2 - ℓ = ℓ by omega,
    show min ℓ (ℓ * 2) = ℓ by omega]

/-- For an odd prime `p`, every round passes on every random string. [AB09, §7.2.2, p.128] -/
theorem eulerLiarRounds_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ℓ k : ℕ)
    (r : List Bool) : eulerLiarRounds p ℓ k r = true := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    simp only [eulerLiarRounds, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨isEulerLiar_of_prime_of_mem_Ico hp hp2 (eulerSample_mem_Ico hp.one_lt _), ih _⟩

/-- **`k` rounds.** For odd composite `N`, all `k` rounds pass with probability at most
`(1/2 + (N−1)/2^{ℓ+1})^k`. [AB09, §7.2.2, p.128] -/
theorem randProb_eulerLiarRounds_le {N : ℕ} (hN : 1 < N) (hodd : Odd N) (hnp : ¬ N.Prime)
    (ℓ k : ℕ) :
    randProb (ℓ * k) (fun r => eulerLiarRounds N ℓ k r = true) ≤
      (1 / 2 + ((N - 1 : ℕ) : ℚ) / 2 ^ (ℓ + 1)) ^ k := by
  induction k with
  | zero => simpa using randProb_le_one
  | succ k ih =>
    rw [show ℓ * (k + 1) = ℓ + ℓ * k by ring, pow_succ']
    rw [randProb_congr (B := fun r => IsEulerLiar N (eulerSample N (r.take ℓ)) ∧
      eulerLiarRounds N ℓ k (r.drop ℓ) = true) (fun r => by simp [eulerLiarRounds])]
    rw [randProb_split ℓ (ℓ * k) (fun r => IsEulerLiar N (eulerSample N r))
      (fun r => eulerLiarRounds N ℓ k r = true)]
    exact mul_le_mul (randProb_isEulerLiar_le hN hodd hnp ℓ) ih randProb_nonneg
      (by positivity)

/-- **Two rounds suffice for coRP.** If `8N ≤ 2^ℓ`, two rounds on `2ℓ` random bits both pass
for odd composite `N` with probability at most `1/3`. [AB09, §7.2.2, p.128] -/
theorem randProb_eulerLiarRounds_two_le {N ℓ : ℕ} (hN : 1 < N) (hodd : Odd N)
    (hnp : ¬ N.Prime) (hℓ : 8 * N ≤ 2 ^ ℓ) :
    randProb (ℓ * 2) (fun r => eulerLiarRounds N ℓ 2 r = true) ≤ 1 / 3 := by
  refine (randProb_eulerLiarRounds_le hN hodd hnp ℓ 2).trans ?_
  set δ : ℚ := ((N - 1 : ℕ) : ℚ) / 2 ^ (ℓ + 1)
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : δ ≤ 1 / 16 := by
    have h : (16 * (N - 1 : ℕ) : ℚ) ≤ 2 ^ (ℓ + 1) := by
      rw [pow_succ]
      exact_mod_cast (by omega : 16 * (N - 1) ≤ 2 ^ ℓ * 2)
    rw [div_le_iff₀ (by positivity)]
    linarith
  nlinarith

end Randomized
