/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Div
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Bertrand

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finding Lovász's prime in polynomial time

Infrastructure for [AB09 §7.2.4] (the prime field of the matching test); not itself a result
of the book. For `n` given in **unary** (the length of the input word), the least prime `p`
with `2^k < p`, `k = ⌈log₂ 2n⌉`, satisfies `p ≤ 2^{k+1}` (Bertrand) and is found by trial
division in polynomial time: `p < 8n + 3`, so the search needs `O(n²)` divisibility tests.
The exponent `k` is `Nat.clog 2 (2 * n)`, which is `Complexity.BinArith.lovaszBits n` by
definition.

## Main definitions

* `Complexity.BinArith.lovaszBits` — `k = ⌈log₂ 2n⌉`, the coins per entry of Lovász's test.
* `Complexity.BinArith.lovaszPrime` — the least prime above `2^{clog₂ (2n)}`.
* `Complexity.BinArith.countStep`, `Complexity.BinArith.dblStep`,
  `Complexity.BinArith.searchStep` — the rounds of the three loops (binary length, the power
  `2^k`, trial division).

## Main results

* `Complexity.BinArith.lovaszPrime_prime`, `Complexity.BinArith.two_pow_lt_lovaszPrime`,
  `Complexity.BinArith.lovaszPrime_le` — the prime lies in `(2^k, 2^{k+1}]`.
* `Complexity.BinArith.polyTimeComputable_lovaszPrime` — `z ↦ Nat.bits (lovaszPrime |z|)`
  is polynomial-time.

## Divergences

* `n` is read in unary (as `|z|`): in binary, trial division would be exponential.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.4.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### The prime -/

/-! ### Coins per entry -/

/-- Coins per entry: `k = ⌈log₂ 2n⌉`, the least `k` with `2n ≤ 2^k`. -/
def lovaszBits (n : ℕ) : ℕ := Nat.clog 2 (2 * n)

/-- `2n ≤ 2^{lovaszBits n}`. -/
theorem two_mul_le_two_pow_lovaszBits (n : ℕ) : 2 * n ≤ 2 ^ lovaszBits n :=
  Nat.le_pow_clog one_lt_two _

/-- `lovaszBits n ≤ n + 1`, so Lovász's test uses polynomially many coins. -/
theorem lovaszBits_le (n : ℕ) : lovaszBits n ≤ n + 1 := by
  refine (Nat.clog_le_iff_le_pow one_lt_two).mpr ?_
  rw [pow_succ]
  have := Nat.lt_two_pow_self (n := n)
  omega

/-- For `n ≥ 1`, `2^{lovaszBits n} < 4n`. -/
theorem two_pow_lovaszBits_lt {n : ℕ} (hn : n ≠ 0) : 2 ^ lovaszBits n < 4 * n := by
  have h1 : 1 < 2 * n := by omega
  have hpred := Nat.pow_pred_clog_lt_self one_lt_two h1
  have hpos : 0 < lovaszBits n := Nat.clog_pos one_lt_two (by omega)
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hpos
  rw [zero_add] at hj
  change 2 ^ (lovaszBits n).pred < 2 * n at hpred
  rw [hj, Nat.pred_succ] at hpred
  rw [hj, pow_succ]
  omega

/-- Bertrand's postulate for the prime-field variant: a prime in `(2^k, 2^{k+1}]` for
`k = lovaszBits n`, hence `p ≥ 2^k ≥ 2n` and, for `n ≥ 1`, `p < 8n`. -/
theorem exists_prime_lovaszBits (n : ℕ) :
    ∃ p, p.Prime ∧ 2 ^ lovaszBits n < p ∧ p ≤ 2 ^ (lovaszBits n + 1) := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul _ (pow_ne_zero (lovaszBits n)
    two_ne_zero)
  exact ⟨p, hp, h1, by rwa [pow_succ, mul_comm]⟩

/-! ### The prime -/

/-- The least prime `p ≥ 2^{clog₂ (2n)} + 1`. -/
noncomputable def lovaszPrime (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (2 ^ Nat.clog 2 (2 * n) + 1))

/-- `lovaszPrime n` is prime. -/
theorem lovaszPrime_prime (n : ℕ) : (lovaszPrime n).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 ^ Nat.clog 2 (2 * n) + 1))).2

/-- `2^{clog₂ (2n)} < lovaszPrime n`. -/
theorem two_pow_lt_lovaszPrime (n : ℕ) : 2 ^ Nat.clog 2 (2 * n) < lovaszPrime n :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 ^ Nat.clog 2 (2 * n) + 1))).1

/-- No prime lies strictly between `2^{clog₂ (2n)}` and `lovaszPrime n`. -/
theorem not_prime_of_lt_lovaszPrime {n q : ℕ} (h1 : 2 ^ Nat.clog 2 (2 * n) < q)
    (h2 : q < lovaszPrime n) : ¬ q.Prime := fun hq =>
  Nat.find_min (Nat.exists_infinite_primes (2 ^ Nat.clog 2 (2 * n) + 1)) h2 ⟨h1, hq⟩

/-- Bertrand: `lovaszPrime n ≤ 2^{clog₂ (2n) + 1}`. -/
theorem lovaszPrime_le (n : ℕ) : lovaszPrime n ≤ 2 ^ (Nat.clog 2 (2 * n) + 1) := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ Nat.clog 2 (2 * n))
    (pow_ne_zero _ two_ne_zero)
  exact (Nat.find_min' _ ⟨h1, hp⟩).trans (by rw [pow_succ]; omega)

/-- `2^{clog₂ (2n)} ≤ 4n + 1`. -/
theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 (2 * n) ≤ 4 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpred := Nat.pow_pred_clog_lt_self one_lt_two (by omega : 1 < 2 * n)
  have hpos : 0 < Nat.clog 2 (2 * n) := Nat.clog_pos one_lt_two (by omega)
  obtain ⟨j, hj⟩ : ∃ j, Nat.clog 2 (2 * n) = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hj, Nat.pred_succ] at hpred
  rw [hj, pow_succ]
  omega

/-- `lovaszPrime n ≤ 8n + 2`. -/
theorem lovaszPrime_le_linear (n : ℕ) : lovaszPrime n ≤ 8 * n + 2 := by
  have h1 := lovaszPrime_le n
  have h2 := two_pow_clog_le n
  rw [pow_succ] at h1
  omega

/-! ### The binary length of the input -/

/-- One round of counting on `⟨acc, rest⟩`: add one to `acc` and drop a letter of `rest`. -/
def countStep (S : List Bool) : List Bool :=
  if isNilB (pairSndD S) then S
  else pairEncode (add (pairEncode (pairFstD S) [true])) ((pairSndD S).drop 1)

/-- The counting loop: `Nat.bits |z|`, by `|z| + 1` rounds from `⟨[], z⟩`. -/
def countLoop (z : List Bool) : List Bool := countStep^[1 * (z.length + 1) ^ 1] (pairEncode [] z)

/-- The counting invariant: `acc` is normalized and `acc + |rest| = |z|`. -/
def CountInv (z S : List Bool) : Prop :=
  ∃ acc rest, S = pairEncode acc rest ∧ acc = Nat.bits (bitsVal acc) ∧
    bitsVal acc + rest.length = z.length

/-- The counting round preserves the invariant and shortens a nonempty `rest`. -/
theorem countInv_step {z S : List Bool} (h : CountInv z S) :
    CountInv z (countStep S) ∧
      (0 < (pairSndD S).length → (pairSndD (countStep S)).length < (pairSndD S).length) ∧
      ((pairSndD S).length = 0 → countStep S = S) := by
  obtain ⟨acc, rest, rfl, ha, hv⟩ := h
  simp only [pairSndD_pairEncode]
  by_cases hr : rest = []
  · subst hr
    have he : countStep (pairEncode acc []) = pairEncode acc [] := by simp [countStep, isNilB]
    rw [he]; exact ⟨⟨acc, [], rfl, ha, hv⟩, by simp, fun _ => rfl⟩
  have he : countStep (pairEncode acc rest) =
      pairEncode (Nat.bits (bitsVal acc + 1)) (rest.drop 1) := by
    simp [countStep, isNilB, hr, add, bitsVal]
  rw [he]
  have := List.length_pos_iff.mpr hr
  refine ⟨⟨_, _, rfl, by simp [bitsVal_bits], ?_⟩, fun _ => by simp; omega,
    fun h0 => absurd h0 (by omega)⟩
  simp [bitsVal_bits]; omega

/-- The counting loop computes the binary length of its input. -/
theorem countLoop_eq (z : List Bool) : countLoop z = pairEncode (Nat.bits z.length) [] := by
  have h0 : CountInv z (pairEncode [] z) := ⟨[], z, rfl, by simp [bitsVal, Nat.zero_bits],
    by simp [bitsVal]⟩
  have hμ := iterate_measure_eq_zero (g := countStep) (CountInv z) (fun S => (pairSndD S).length)
    (fun _ h => (countInv_step h).1) (fun _ h => (countInv_step h).2.1)
    (fun _ h => (countInv_step h).2.2) (1 * (z.length + 1) ^ 1) _ h0 (by simp)
  obtain ⟨acc, rest, he, ha, hv⟩ :=
    iterate_invariant (CountInv z) (fun _ h => (countInv_step h).1) (1 * (z.length + 1) ^ 1) h0
  rw [countLoop, he]
  rw [he] at hμ
  dsimp only at hμ
  rw [pairSndD_pairEncode, List.length_eq_zero_iff] at hμ
  subst hμ
  simp only [List.length_nil, add_zero] at hv
  rw [ha, hv]

/-- The counting loop is polynomial-time. -/
theorem polyTimeComputable_countLoop : PolyTimeComputable countLoop := by
  have hs : PolyTimeComputable countStep := by
    unfold countStep
    exact polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
      polyTimeComputable_id ((polyTimeComputable_add.comp
        (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_const [true]))).pairEncode
        (polyTimeComputable_tail.comp polyTimeComputable_pairSndD))
  have h0 : ∀ z : List Bool, CountInv z (pairEncode [] z) := fun z =>
    ⟨[], z, rfl, by simp [bitsVal, Nat.zero_bits], by simp [bitsVal]⟩
  exact polyTimeComputable_iterate hs ((polyTimeComputable_const []).pairEncode
    polyTimeComputable_id) 1 1 4 1 (fun z i _ => by
      dsimp only [id]
      obtain ⟨acc, rest, he, ha, hv⟩ :=
        iterate_invariant (CountInv z) (fun _ h => (countInv_step h).1) i (h0 z)
      have hacc : acc.length ≤ z.length := by
        rw [ha]; exact length_bits_le ((Nat.lt_two_pow_self).trans_le' (by omega))
      rw [he, length_pairEncode]; simp; omega)

/-! ### The power `2^k` -/

/-- The value of `0^j 1`. -/
theorem bitsVal_replicate_false_one (j : ℕ) :
    bitsVal (List.replicate j false ++ [true]) = 2 ^ j := by
  rw [bitsVal_append_singleton, (bitsVal_eq_zero_iff _).mpr (by simp)]
  simp

/-- One doubling round on `⟨x, m⟩`: double `x` while `x < m`. -/
def dblStep (S : List Bool) : List Bool :=
  if lt S then pairEncode (false :: pairFstD S) (pairSndD S) else S

/-- The doubling loop from `⟨1, 2n⟩`, `n = |z|`: `2(|z| + 1)` rounds. -/
def dblLoop (z : List Bool) : List Bool :=
  dblStep^[2 * (z.length + 1) ^ 1] (pairEncode [true] (false :: pairFstD (countLoop z)))

/-- The doubling invariant: the state is `⟨0^j 1, 2n⟩` with `j ≤ clog₂ (2n)`. -/
def DblInv (n : ℕ) (S : List Bool) : Prop :=
  ∃ j, S = pairEncode (List.replicate j false ++ [true]) (false :: Nat.bits n) ∧
    j ≤ Nat.clog 2 (2 * n)

/-- The doubling round preserves the invariant, raises a short `j`, and fixes
`j = clog₂ (2n)`.

**Proof sketch.** On `⟨0^j 1, 2n⟩` the round compares `2^j` with `2n`; by minimality of `clog`,
`2^j < 2n` holds exactly when `j < clog₂ (2n)`, in which case the round prepends a `0`
(raising `j` and lowering the measure), and otherwise it leaves the state fixed. -/
theorem dblInv_step {n : ℕ} {S : List Bool} (h : DblInv n S) :
    DblInv n (dblStep S) ∧
      (0 < Nat.clog 2 (2 * n) - ((pairFstD S).length - 1) →
        Nat.clog 2 (2 * n) - ((pairFstD (dblStep S)).length - 1) <
          Nat.clog 2 (2 * n) - ((pairFstD S).length - 1)) ∧
      (Nat.clog 2 (2 * n) - ((pairFstD S).length - 1) = 0 → dblStep S = S) := by
  obtain ⟨j, rfl, hj⟩ := h
  have hm : bitsVal (false :: Nat.bits n) = 2 * n := by simp [bitsVal, bitsVal_bits]
  have hlt : lt (pairEncode (List.replicate j false ++ [true]) (false :: Nat.bits n)) =
      decide (2 ^ j < 2 * n) := by
    simp only [lt, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_replicate_false_one, hm]
  simp only [pairFstD_pairEncode, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, Nat.add_sub_cancel]
  by_cases hc : 2 ^ j < 2 * n
  · have he : dblStep (pairEncode (List.replicate j false ++ [true]) (false :: Nat.bits n)) =
        pairEncode (List.replicate (j + 1) false ++ [true]) (false :: Nat.bits n) := by
      simp [dblStep, hlt, hc, List.replicate_succ]
    have hj' : j < Nat.clog 2 (2 * n) := by
      by_contra hle
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hle)
      have := Nat.le_pow_clog one_lt_two (2 * n)
      omega
    rw [he]
    refine ⟨⟨j + 1, rfl, hj'⟩, fun _ => ?_, fun h0 => absurd h0 (by omega)⟩
    simp only [pairFstD_pairEncode, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  · have he : dblStep (pairEncode (List.replicate j false ++ [true]) (false :: Nat.bits n)) =
        pairEncode (List.replicate j false ++ [true]) (false :: Nat.bits n) := by
      simp [dblStep, hlt, hc]
    rw [he]
    refine ⟨⟨j, rfl, hj⟩, fun hpos => ?_, fun _ => rfl⟩
    exfalso
    have := Nat.le_pow_clog one_lt_two (2 * n)
    have hj2 : Nat.clog 2 (2 * n) ≤ j := (Nat.clog_le_iff_le_pow one_lt_two).mpr (by omega)
    omega

/-- The doubling loop ends at `⟨2^{clog₂ (2n)}, 2n⟩` (by value of the first slot). -/
theorem dblLoop_spec (z : List Bool) :
    pairFstD (dblLoop z) = List.replicate (Nat.clog 2 (2 * z.length)) false ++ [true] := by
  have h0 : DblInv z.length (pairEncode [true] (false :: pairFstD (countLoop z))) :=
    ⟨0, by simp [countLoop_eq], Nat.zero_le _⟩
  have hμ := iterate_measure_eq_zero (g := dblStep) (DblInv z.length)
    (fun S => Nat.clog 2 (2 * z.length) - ((pairFstD S).length - 1))
    (fun _ h => (dblInv_step h).1) (fun _ h => (dblInv_step h).2.1)
    (fun _ h => (dblInv_step h).2.2) (2 * (z.length + 1) ^ 1) _ h0
    (by
      have : Nat.clog 2 (2 * z.length) ≤ z.length + 1 := lovaszBits_le z.length
      simp; omega)
  obtain ⟨j, he, hj⟩ :=
    iterate_invariant (DblInv z.length) (fun _ h => (dblInv_step h).1) (2 * (z.length + 1) ^ 1) h0
  rw [dblLoop, he, pairFstD_pairEncode]
  rw [he] at hμ
  dsimp only at hμ
  simp only [pairFstD_pairEncode, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, Nat.add_sub_cancel] at hμ
  have hjc : j = Nat.clog 2 (2 * z.length) := by omega
  rw [hjc]

/-- The doubling loop is polynomial-time.

**Proof sketch.** The round is a composition of the closure kit. Along the orbit the
invariant `DblInv` holds (`iterate_invariant`), so the state is `⟨0^j 1, 2n⟩` with
`j ≤ clog₂ (2n) ≤ |z| + 1` (`lovaszBits_le`), of length linear in `|z|`; then
`polyTimeComputable_iterate` applies. -/
theorem polyTimeComputable_dblLoop : PolyTimeComputable dblLoop := by
  have hs : PolyTimeComputable dblStep := by
    unfold dblStep
    exact polyTimeComputable_ite polyTimeComputable_lt
      ((polyTimeComputable_cons (polyTimeComputable_const [false])
        polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD) polyTimeComputable_id
  have hinit : PolyTimeComputable
      (fun z => pairEncode [true] (false :: pairFstD (countLoop z))) :=
    (polyTimeComputable_const [true]).pairEncode (polyTimeComputable_cons
      (polyTimeComputable_const [false]) (polyTimeComputable_pairFstD.comp
        polyTimeComputable_countLoop))
  have h0 : ∀ z : List Bool, DblInv z.length
      (pairEncode [true] (false :: pairFstD (countLoop z))) := fun z =>
    ⟨0, by simp [countLoop_eq], Nat.zero_le _⟩
  exact polyTimeComputable_iterate hs hinit 2 1 7 1 (fun z i _ => by
    obtain ⟨j, he, hj⟩ :=
      iterate_invariant (DblInv z.length) (fun _ h => (dblInv_step h).1) i (h0 z)
    have h1 : Nat.clog 2 (2 * z.length) ≤ z.length + 1 := lovaszBits_le z.length
    have h2 : (Nat.bits z.length).length ≤ z.length :=
      length_bits_le (Nat.lt_two_pow_self)
    rw [he, length_pairEncode]; simp; omega)

/-! ### Trial division -/

/-- One round of trial division on `⟨c, ⟨d, [done]⟩⟩`: stop when done; if `d = c`, `c` is
prime and the search is done; if `d ∣ c`, move to `c + 1` with `d = 2`; else `d := d + 1`. -/
def searchStep (S : List Bool) : List Bool :=
  if (pairSndD (pairSndD S)).headD false then S
  else if beq (pairEncode (pairFstD (pairSndD S)) (pairFstD S)) then
    pairEncode (pairFstD S) (pairEncode (pairFstD (pairSndD S)) [true])
  else if decide (bitsVal (mod (pairEncode (pairFstD S) (pairFstD (pairSndD S)))) = 0) then
    pairEncode (add (pairEncode (pairFstD S) [true])) (pairEncode [false, true] [false])
  else pairEncode (pairFstD S)
    (pairEncode (add (pairEncode (pairFstD (pairSndD S)) [true])) [false])

/-- The search invariant for `P = lovaszPrime n`, `L = 2^{clog₂ (2n)}`: the state is
`⟨c, ⟨d, [b]⟩⟩` (normalized) with `L < c ≤ P`, `2 ≤ d ≤ c`, no divisor of `c` in `[2, d)`, and
`b` only once `c = P`. -/
def SearchInv (n : ℕ) (S : List Bool) : Prop :=
  ∃ c d : ℕ, ∃ b : Bool, S = pairEncode (Nat.bits c) (pairEncode (Nat.bits d) [b]) ∧
    2 ^ Nat.clog 2 (2 * n) < c ∧ c ≤ lovaszPrime n ∧ 2 ≤ d ∧ d ≤ c ∧
    (∀ m, 2 ≤ m → m < d → ¬ m ∣ c) ∧ (b = true → c = lovaszPrime n)

/-- The potential of the search: `0` once done, else `(P - c)(P + 1) + (c - d) + 1`. -/
noncomputable def searchMeasure (n : ℕ) (S : List Bool) : ℕ :=
  if (pairSndD (pairSndD S)).headD false then 0
  else (lovaszPrime n - bitsVal (pairFstD S)) * (lovaszPrime n + 1) +
    (bitsVal (pairFstD S) - bitsVal (pairFstD (pairSndD S))) + 1

/-- The search round preserves the invariant, lowers a positive potential, and fixes
potential `0`.

**Proof sketch.** If `d = c`, `c` has no divisor in `[2, c)`, so it is prime, and as no prime
lies in `(L, P)`, `c = P`. If `d ∣ c` with `2 ≤ d < c`, `c` is composite, so `c < P`; the
potential drops since `(P - c)(P + 1)` loses `P + 1 > c - 2`. Otherwise `d` grows by one. -/
theorem searchInv_step {n : ℕ} {S : List Bool} (h : SearchInv n S) :
    SearchInv n (searchStep S) ∧
      (0 < searchMeasure n S → searchMeasure n (searchStep S) < searchMeasure n S) ∧
      (searchMeasure n S = 0 → searchStep S = S) := by
  obtain ⟨c, d, b, rfl, hL, hP, hd2, hdc, hdiv, hb⟩ := h
  set P := lovaszPrime n
  cases b
  swap
  · have he : searchStep (pairEncode (Nat.bits c) (pairEncode (Nat.bits d) [true])) =
        pairEncode (Nat.bits c) (pairEncode (Nat.bits d) [true]) := by simp [searchStep]
    rw [he]
    exact ⟨⟨c, d, true, rfl, hL, hP, hd2, hdc, hdiv, hb⟩, fun h => by simp [searchMeasure] at h,
      fun _ => rfl⟩
  have hμ : searchMeasure n (pairEncode (Nat.bits c) (pairEncode (Nat.bits d) [false])) =
      (P - c) * (P + 1) + (c - d) + 1 := by
    simp [searchMeasure, bitsVal_bits, P]
  have hpos : searchMeasure n (pairEncode (Nat.bits c) (pairEncode (Nat.bits d) [false])) ≠ 0 :=
    by rw [hμ]; omega
  by_cases hdc' : d = c
  · subst hdc'
    have hprime : d.Prime := Nat.prime_def_lt'.mpr ⟨hd2, hdiv⟩
    have hdP : d = P := by
      by_contra hne
      exact not_prime_of_lt_lovaszPrime hL (lt_of_le_of_ne hP hne) hprime
    have he : searchStep (pairEncode (Nat.bits d) (pairEncode (Nat.bits d) [false])) =
        pairEncode (Nat.bits d) (pairEncode (Nat.bits d) [true]) := by
      simp [searchStep, beq, bitsVal_bits]
    rw [he]
    refine ⟨⟨d, d, true, rfl, hL, hP, hd2, le_rfl, hdiv, fun _ => hdP⟩, fun _ => ?_,
      fun h0 => absurd h0 hpos⟩
    rw [hμ]; simp [searchMeasure]
  have hdlt : d < c := lt_of_le_of_ne hdc hdc'
  by_cases hdvd : c % d = 0
  · have hcP : c < P := by
      refine lt_of_le_of_ne hP fun hcP => ?_
      have := (Nat.prime_def_lt'.mp (hcP ▸ lovaszPrime_prime n)).2 d hd2 hdlt
      exact this (Nat.dvd_of_mod_eq_zero hdvd)
    have he : searchStep (pairEncode (Nat.bits c) (pairEncode (Nat.bits d) [false])) =
        pairEncode (Nat.bits (c + 1)) (pairEncode (Nat.bits 2) [false]) := by
      have h2 : Nat.bits 2 = [false, true] := by
        rw [show (2 : ℕ) = 2 * 1 by rfl, Nat.bit0_bits 1 one_ne_zero, Nat.one_bits]
      simp [searchStep, beq, mod, add, bitsVal_bits, bitsVal, hdc', hdvd, h2]
    rw [he]
    refine ⟨⟨c + 1, 2, false, rfl, by omega, by omega, le_rfl, by omega,
      fun m h1 h2 => absurd h2 (by omega), by simp⟩, fun _ => ?_, fun h0 => absurd h0 hpos⟩
    rw [hμ]
    simp only [searchMeasure, pairSndD_pairEncode, pairFstD_pairEncode, bitsVal_bits]
    simp only [List.headD_cons, Bool.false_eq_true, if_false]
    obtain ⟨t, ht⟩ : ∃ t, P - c = t + 1 := ⟨P - c - 1, by omega⟩
    have hPe : lovaszPrime n = P := rfl
    rw [hPe, show P - (c + 1) = t by omega, ht]
    have : (t + 1) * (P + 1) = t * (P + 1) + (P + 1) := by ring
    omega
  · have he : searchStep (pairEncode (Nat.bits c) (pairEncode (Nat.bits d) [false])) =
        pairEncode (Nat.bits c) (pairEncode (Nat.bits (d + 1)) [false]) := by
      simp [searchStep, beq, mod, add, bitsVal_bits, bitsVal, hdc', hdvd]
    rw [he]
    refine ⟨⟨c, d + 1, false, rfl, hL, hP, by omega, by omega, fun m h1 h2 => ?_, by simp⟩,
      fun _ => ?_, fun h0 => absurd h0 hpos⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | rfl
      · exact hdiv m h1 h
      · exact fun hm => hdvd (Nat.mod_eq_zero_of_dvd hm)
    · rw [hμ]; simp [searchMeasure, bitsVal_bits, P]; omega

/-- The search input `⟨L + 1, ⟨2, [false]⟩⟩` from the doubling loop's power `L`. -/
def searchInit (z : List Bool) : List Bool :=
  pairEncode (add (pairEncode (pairFstD (dblLoop z)) [true])) (pairEncode [false, true] [false])

/-- The search input satisfies the invariant for `n = |z|`. -/
theorem searchInv_init (z : List Bool) : SearchInv z.length (searchInit z) := by
  have h2 : Nat.bits 2 = [false, true] := by
    rw [show (2 : ℕ) = 2 * 1 by rfl, Nat.bit0_bits 1 one_ne_zero, Nat.one_bits]
  refine ⟨2 ^ Nat.clog 2 (2 * z.length) + 1, 2, false, ?_, by omega, ?_, le_rfl, ?_,
    fun m h1 h2 => absurd h2 (by omega), by simp⟩
  · simp [searchInit, add, dblLoop_spec, bitsVal_replicate_false_one, bitsVal, h2]
  · exact two_pow_lt_lovaszPrime _
  · have := Nat.one_le_two_pow (n := Nat.clog 2 (2 * z.length)); omega

/-- The search loop: `64(|z| + 1)²` trial-division rounds from `searchInit z`. -/
def searchLoop (z : List Bool) : List Bool := searchStep^[64 * (z.length + 1) ^ 2] (searchInit z)

/-- **Lovász's prime is found in polynomial time** (infrastructure for [AB09 §7.2.4]; not
itself a result of the book): `z ↦ Nat.bits (lovaszPrime |z|)`.

**Proof sketch.** Count `|z|` in binary and double `1` up to `L = 2^{clog₂ (2|z|)}` (two
loops of `|z| + 1` and `2(|z| + 1)` rounds), then search `c = L + 1, L + 2, …` by trial
division (`SearchInv`). The potential `(P - c)(P + 1) + (c - d) + 1 ≤ (P + 1)²` with
`P ≤ 8|z| + 2` drops every round until the search is done with `c = P`; all numbers stay
below `P`, so the states are linear in length. -/
theorem polyTimeComputable_lovaszPrime :
    PolyTimeComputable (fun z => Nat.bits (lovaszPrime z.length)) := by
  have hs : PolyTimeComputable searchStep := by
    unfold searchStep
    refine polyTimeComputable_ite (polyTimeComputable_headD.comp polyTimeComputable_slot3)
      polyTimeComputable_id ?_
    refine polyTimeComputable_ite (polyTimeComputable_beq.comp
      (polyTimeComputable_slot2.pairEncode polyTimeComputable_pairFstD))
      (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_slot2.pairEncode
        (polyTimeComputable_const [true]))) ?_
    exact polyTimeComputable_ite (polyTimeComputable_isZero.comp (polyTimeComputable_mod.comp
        (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot2)))
      ((polyTimeComputable_add.comp (polyTimeComputable_pairFstD.pairEncode
        (polyTimeComputable_const [true]))).pairEncode (polyTimeComputable_const _))
      (polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_add.comp
        (polyTimeComputable_slot2.pairEncode (polyTimeComputable_const [true]))).pairEncode
        (polyTimeComputable_const [false])))
  have hinit : PolyTimeComputable searchInit :=
    (polyTimeComputable_add.comp ((polyTimeComputable_pairFstD.comp
      polyTimeComputable_dblLoop).pairEncode (polyTimeComputable_const [true]))).pairEncode
      (polyTimeComputable_const _)
  have hloop : PolyTimeComputable searchLoop :=
    polyTimeComputable_iterate hs hinit 64 2 64 1 (fun z i _ => by
      obtain ⟨c, d, b, he, -, hP, -, hdc, -, -⟩ :=
        iterate_invariant (SearchInv z.length) (fun _ h => (searchInv_step h).1) i
          (searchInv_init z)
      have hPl := lovaszPrime_le_linear z.length
      have hc : (Nat.bits c).length ≤ z.length + 4 :=
        length_bits_le (by
          have := Nat.lt_two_pow_self (n := z.length)
          rw [pow_add]; omega)
      have hd : (Nat.bits d).length ≤ z.length + 4 :=
        (length_bits_mono hdc).trans hc
      rw [he]; simp only [length_pairEncode, List.length_cons, List.length_nil, pow_one]
      omega)
  convert polyTimeComputable_pairFstD.comp hloop using 1
  funext z
  have hμ := iterate_measure_eq_zero (g := searchStep) (SearchInv z.length)
    (searchMeasure z.length) (fun _ h => (searchInv_step h).1)
    (fun _ h => (searchInv_step h).2.1) (fun _ h => (searchInv_step h).2.2)
    (64 * (z.length + 1) ^ 2) _ (searchInv_init z) (by
      obtain ⟨c, d, b, he, -, hP, hd2, -, -, -⟩ := searchInv_init z
      have hPl := lovaszPrime_le_linear z.length
      rw [he]
      unfold searchMeasure
      split_ifs
      · exact Nat.zero_le _
      · simp only [pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_bits]
        have h1 : (lovaszPrime z.length - c) * (lovaszPrime z.length + 1) ≤
            (lovaszPrime z.length + 1) * (lovaszPrime z.length + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (lovaszPrime z.length + 1) * (lovaszPrime z.length + 1) + 8 * (z.length + 1) ≤
            64 * (z.length + 1) ^ 2 := by nlinarith
        omega)
  obtain ⟨c, d, b, he, -, -, -, -, -, hb⟩ :=
    iterate_invariant (SearchInv z.length) (fun _ h => (searchInv_step h).1)
      (64 * (z.length + 1) ^ 2) (searchInv_init z)
  rw [he] at hμ
  cases b
  · simp [searchMeasure] at hμ
  · simp only [Function.comp_apply, searchLoop, he, pairFstD_pairEncode, hb rfl]

end BinArith

end Complexity
