/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.ModPow
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Jacobi symbol in polynomial time

[AB09, §7.2.2] (p. 128, second fact): for odd `N` the Jacobi symbol `(A/N)` is computable in
polynomial time. The algorithm is the binary recursion: strip factors `2` from `A` using
`(2/N) = χ₈(N)`, swap by quadratic reciprocity when `A` is odd and reduce `N mod A`, until
`A = 0`, when `(0/N) = [N = 1]`. Mathlib's `jacobiSym` is the specification.

## Main definitions

* `Complexity.BinArith.jacobi` — the symbol `(a/n)` of the two components of a pair, encoded
  as the binary word of `(a/n) + 1 ∈ {0, 1, 2}`.
* `Complexity.BinArith.jacobiAlg` — the algorithm; it agrees with `jacobi` for odd `n`.
* `Complexity.BinArith.jacobiModAlg` — the algorithm's answer as the residue `(a/n) mod n`.

## Main results

* `Complexity.BinArith.polyTimeComputable_jacobiAlg`, `Complexity.BinArith.jacobiAlg_eq`.
* `Complexity.BinArith.polyTimeComputable_jacobiModAlg`,
  `Complexity.BinArith.jacobiModAlg_pairEncode`.

## Divergences

* The book states the bound `O(log A · log N)`; we prove polynomial time only.
* The algorithm is specified for odd `n` only, as in the book; on even `n` its output is
  unspecified.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.2, p. 128.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-- The value of a word modulo `8`, read off its three low bits. -/
theorem bitsVal_mod_eight (w : List Bool) :
    bitsVal w % 8 = (w.headD false).toNat + 2 * ((w.drop 1).headD false).toNat +
      4 * ((w.drop 2).headD false).toNat := by
  have h1 := bitsVal_eq_headD w
  have h2 := bitsVal_eq_headD (w.drop 1)
  have h3 := bitsVal_eq_headD (w.drop 2)
  simp only [List.drop_drop, Nat.reduceAdd] at h2 h3
  have := Bool.toNat_le (w.headD false)
  have := Bool.toNat_le ((w.drop 1).headD false)
  have := Bool.toNat_le ((w.drop 2).headD false)
  omega

/-- An odd value is `3 mod 4` exactly when its second bit is set. -/
theorem mod_four_eq_three_iff {w : List Bool} (h : bitsVal w % 2 = 1) :
    bitsVal w % 4 = 3 ↔ (w.drop 1).headD false = true := by
  have e := bitsVal_mod_eight w
  have m := bitsVal_mod_two w
  have := Bool.toNat_le (w.headD false)
  cases h1 : (w.drop 1).headD false <;> cases h2 : (w.drop 2).headD false <;>
    simp only [h1, h2, Bool.toNat_false, Bool.toNat_true] at e <;> simp <;> omega

/-- The sign `±1` stored in a one-bit word (`1` means `-1`). -/
def signOf (s : List Bool) : ℤ := if s.headD false then -1 else 1

/-- The one-bit word with the opposite sign. -/
def flipSign (s : List Bool) : List Bool := [!(s.headD false)]

/-- Flipping negates the sign. -/
@[simp] theorem signOf_flipSign (s : List Bool) : signOf (flipSign s) = -signOf s := by
  simp only [signOf, flipSign, List.headD_cons]
  split_ifs <;> simp_all

/-- One round of the Jacobi recursion on `⟨A, ⟨N, s⟩⟩`: for `A = 0` stop; for odd `A`
swap to `⟨N mod A, ⟨A, ·⟩⟩` and flip `s` when `A ≡ N ≡ 3 (mod 4)`; for even `A` halve it and
flip `s` when `N ≡ 3, 5 (mod 8)`. -/
def jacStep (S : List Bool) : List Bool :=
  if decide (bitsVal (pairFstD S) = 0) then S
  else if (pairFstD S).headD false then
    pairEncode (mod (pairEncode (pairFstD (pairSndD S)) (pairFstD S)))
      (pairEncode (pairFstD S)
        (if ((pairFstD S).drop 1).headD false && ((pairFstD (pairSndD S)).drop 1).headD false
          then flipSign (pairSndD (pairSndD S)) else pairSndD (pairSndD S)))
  else
    pairEncode ((pairFstD S).drop 1)
      (pairEncode (pairFstD (pairSndD S))
        (if ((pairFstD (pairSndD S)).drop 1).headD false ^^
            ((pairFstD (pairSndD S)).drop 2).headD false
          then flipSign (pairSndD (pairSndD S)) else pairSndD (pairSndD S)))

/-- A Jacobi round is polynomial-time. -/
theorem polyTimeComputable_jacStep : PolyTimeComputable jacStep := by
  have hA := polyTimeComputable_pairFstD
  have hN := polyTimeComputable_slot2
  have hs := polyTimeComputable_slot3
  have hbit : ∀ {f : List Bool → List Bool} (i : ℕ), PolyTimeComputable f →
      PolyTimeComputable (fun S => [((f S).drop i).headD false]) := by
    intro f i hf
    exact polyTimeComputable_headD.comp ((polyTimeComputable_drop i).comp hf)
  have hflip : PolyTimeComputable (fun S => flipSign (pairSndD (pairSndD S))) :=
    polyTimeComputable_not (hbit 0 hs)
  unfold jacStep
  refine polyTimeComputable_ite (polyTimeComputable_isZero.comp hA) polyTimeComputable_id ?_
  refine polyTimeComputable_ite (hbit 0 hA) ?_ ?_
  · exact (polyTimeComputable_mod.comp (hN.pairEncode hA)).pairEncode (hA.pairEncode
      (polyTimeComputable_ite (polyTimeComputable_and (hbit 1 hA) (hbit 1 hN)) hflip hs))
  · exact (polyTimeComputable_tail.comp hA).pairEncode (hN.pairEncode
      (polyTimeComputable_ite (polyTimeComputable_xor (hbit 1 hN) (hbit 2 hN)) hflip hs))

/-- The Jacobi symbol of the two components of `z`, encoded as `Nat.bits ((a/n) + 1)`. -/
def jacobi (z : List Bool) : List Bool :=
  Nat.bits (jacobiSym (bitsVal (pairFstD z)) (bitsVal (pairSndD z)) + 1).toNat

/-- The invariant of the Jacobi loop on `z = ⟨a, n⟩`: the slots are no longer than `z`, and
for odd `n` the modulus slot is odd and `sign · (A/N) = (a/n)`. -/
def JacInv (z S : List Bool) : Prop :=
  ∃ A N s, S = pairEncode A (pairEncode N s) ∧ A.length ≤ z.length ∧ N.length ≤ z.length ∧
    s.length ≤ 1 ∧
    (Odd (bitsVal (pairSndD z)) → Odd (bitsVal N) ∧
      signOf s * jacobiSym (bitsVal A) (bitsVal N) =
        jacobiSym (bitsVal (pairFstD z)) (bitsVal (pairSndD z)))

/-- The potential of the Jacobi loop: the bit size of `A·N`, plus one while `N ≤ A`. -/
def jacMeasure (S : List Bool) : ℕ :=
  Nat.size (bitsVal (pairFstD S) * bitsVal (pairFstD (pairSndD S))) +
    if bitsVal (pairFstD (pairSndD S)) ≤ bitsVal (pairFstD S) then 1 else 0

/-- `(2/N)` read off the bits of an odd `N`: `-1` exactly when `N ≡ 3, 5 (mod 8)`. -/
private theorem jacobiSym_two_bits {N : List Bool} (hN : Odd (bitsVal N)) :
    jacobiSym 2 (bitsVal N) =
      if ((N.drop 1).headD false ^^ (N.drop 2).headD false) then -1 else 1 := by
  rw [jacobiSym.at_two hN, ZMod.χ₈_nat_eq_if_mod_eight]
  have e := bitsVal_mod_eight N
  have m := bitsVal_mod_two N
  have h2 : bitsVal N % 2 = 1 := Nat.odd_iff.mp hN
  have := Bool.toNat_le (N.headD false)
  cases h1 : (N.drop 1).headD false <;> cases h3 : (N.drop 2).headD false <;>
    simp only [h1, h3, Bool.toNat_false, Bool.toNat_true] at e <;>
    simp only [Bool.xor_self, Bool.xor_false, Bool.xor_true, Bool.not_false] <;> split_ifs <;>
    first | rfl | omega

/-- Halving step of the recursion: `(2A'/N) = (2/N)(A'/N)`. -/
private theorem jacobiSym_even {A N : ℕ} (hA : A % 2 = 0) :
    jacobiSym A N = jacobiSym 2 N * jacobiSym (A / 2 : ℕ) N := by
  rw [← jacobiSym.mul_left]; congr 1; push_cast; omega

/-- Reciprocity step of the recursion for odd `A`, `N`. -/
private theorem jacobiSym_odd {A N : ℕ} (hA : A % 2 = 1) (hN : N % 2 = 1) :
    jacobiSym A N =
      (if A % 4 = 3 ∧ N % 4 = 3 then -1 else 1) * jacobiSym (N % A : ℕ) A := by
  rw [← jacobiSym.quadratic_reciprocity_if hA hN, jacobiSym.mod_left (N : ℤ) A]
  push_cast
  split_ifs <;> simp

/-- The Jacobi round preserves the invariant.

**Proof sketch.** For odd `A`, reciprocity and `(N/A) = ((N mod A)/A)` (`jacobiSym_odd`) give
the swap, with sign `-1` exactly when `A ≡ N ≡ 3 (mod 4)`, read off the second bits
(`mod_four_eq_three_iff`). For even `A`, `(A/N) = (2/N)·((A/2)/N)` and `(2/N) = χ₈(N)`, read off
bits one and two of `N` (`jacobiSym_two_bits`). Slots never grow: `N mod A < A`. -/
theorem jacInv_step {z S : List Bool} (h : JacInv z S) : JacInv z (jacStep S) := by
  obtain ⟨A, N, s, rfl, hA, hN, hs, hv⟩ := h
  unfold jacStep
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, mod]
  split_ifs with h0 h1 h2 h3
  · exact ⟨A, N, s, rfl, hA, hN, hs, hv⟩
  all_goals have hApos : 0 < bitsVal A := Nat.pos_of_ne_zero (by simpa using h0)
  · -- odd `A`, both `≡ 3 (mod 4)`: swap and flip
    have hA2 : bitsVal A % 2 = 1 := by rw [bitsVal_mod_two, h1]; rfl
    refine ⟨_, A, _, rfl, (length_bits_le_of_le A (Nat.mod_lt _ hApos).le le_rfl).trans hA, hA,
      by simp [flipSign], fun hn => ?_⟩
    obtain ⟨hNo, hJ⟩ := hv hn
    have hN2 := Nat.odd_iff.mp hNo
    refine ⟨Nat.odd_iff.mpr hA2, ?_⟩
    rw [Bool.and_eq_true] at h2
    have h4 : bitsVal A % 4 = 3 ∧ bitsVal N % 4 = 3 :=
      ⟨(mod_four_eq_three_iff hA2).mpr h2.1, (mod_four_eq_three_iff hN2).mpr h2.2⟩
    rw [← hJ, jacobiSym_odd hA2 hN2, if_pos h4, signOf_flipSign, bitsVal_bits]; ring
  · -- odd `A`, otherwise: swap
    have hA2 : bitsVal A % 2 = 1 := by rw [bitsVal_mod_two, h1]; rfl
    refine ⟨_, A, _, rfl, (length_bits_le_of_le A (Nat.mod_lt _ hApos).le le_rfl).trans hA, hA,
      hs, fun hn => ?_⟩
    obtain ⟨hNo, hJ⟩ := hv hn
    have hN2 := Nat.odd_iff.mp hNo
    refine ⟨Nat.odd_iff.mpr hA2, ?_⟩
    have h4 : ¬ (bitsVal A % 4 = 3 ∧ bitsVal N % 4 = 3) := fun ⟨h5, h6⟩ => h2 (by
      rw [(mod_four_eq_three_iff hA2).mp h5, (mod_four_eq_three_iff hN2).mp h6]; rfl)
    rw [← hJ, jacobiSym_odd hA2 hN2, if_neg h4, bitsVal_bits]; ring
  all_goals have hA2 : bitsVal A % 2 = 0 := by simp_all [bitsVal_mod_two]
  · -- even `A`, `N ≡ 3, 5 (mod 8)`: halve and flip
    refine ⟨_, N, _, rfl, by simp; omega, hN, by simp [flipSign], fun hn => ?_⟩
    obtain ⟨hNo, hJ⟩ := hv hn
    refine ⟨hNo, ?_⟩
    rw [← hJ, jacobiSym_even hA2, jacobiSym_two_bits hNo, if_pos h3, signOf_flipSign,
      bitsVal_drop_one]
    ring
  · -- even `A`, otherwise: halve
    refine ⟨_, N, _, rfl, by simp; omega, hN, hs, fun hn => ?_⟩
    obtain ⟨hNo, hJ⟩ := hv hn
    refine ⟨hNo, ?_⟩
    rw [← hJ, jacobiSym_even hA2, jacobiSym_two_bits hNo, if_neg h3, bitsVal_drop_one]
    ring

/-- For an odd modulus `N`, the Jacobi round strictly lowers the potential of `⟨A, ⟨N, s⟩⟩`
when `A ≠ 0`, and fixes states of potential `0`.

**Proof sketch.** Halving `A` halves the product `A·N` (`N > 0` as `N` is odd). An odd round
gives `(N mod A)·A`: if `N ≤ A` the product does not grow and the flag `[N ≤ A]` clears;
otherwise `2(N mod A) ≤ N` halves it (`size_lt_of_two_mul_le`). -/
theorem jacMeasure_step (A N s : List Bool) (hN : Odd (bitsVal N)) :
    (0 < jacMeasure (pairEncode A (pairEncode N s)) →
        jacMeasure (jacStep (pairEncode A (pairEncode N s))) <
          jacMeasure (pairEncode A (pairEncode N s))) ∧
      (jacMeasure (pairEncode A (pairEncode N s)) = 0 →
        jacStep (pairEncode A (pairEncode N s)) = pairEncode A (pairEncode N s)) := by
  have hNpos := hN.pos
  by_cases h0 : bitsVal A = 0
  · have hfix : jacStep (pairEncode A (pairEncode N s)) = pairEncode A (pairEncode N s) := by
      simp [jacStep, h0]
    have hμ : jacMeasure (pairEncode A (pairEncode N s)) = 0 := by
      unfold jacMeasure
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, h0, zero_mul, Nat.size_zero]
      rw [if_neg (by omega)]
    exact ⟨fun h => by omega, fun _ => hfix⟩
  have hApos := Nat.pos_of_ne_zero h0
  have hP : 0 < bitsVal A * bitsVal N := Nat.mul_pos hApos hNpos
  refine ⟨fun _ => ?_, fun hμ => absurd hμ ?_⟩
  swap
  · unfold jacMeasure
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    have := Nat.size_pos.mpr hP
    omega
  unfold jacStep
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, h0, decide_false, Bool.false_eq_true,
    if_false]
  by_cases h1 : A.headD false = true
  · -- odd `A`: the product becomes `(N mod A)·A` and the flag clears
    rw [if_pos h1]
    unfold jacMeasure
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, mod, bitsVal_bits]
    have hlt := Nat.mod_lt (bitsVal N) hApos
    rw [if_neg (by omega), add_zero]
    by_cases hNA : bitsVal N ≤ bitsVal A
    · rw [if_pos hNA]
      have : Nat.size (bitsVal N % bitsVal A * bitsVal A) ≤ Nat.size (bitsVal A * bitsVal N) :=
        Nat.size_le_size (by
          rw [Nat.mul_comm (bitsVal A)]; exact Nat.mul_le_mul_right _ (Nat.mod_le _ _))
      omega
    · rw [if_neg hNA, add_zero]
      apply size_lt_of_two_mul_le hP
      have h1 := Nat.div_add_mod (bitsVal N) (bitsVal A)
      have h2 : 1 ≤ bitsVal N / bitsVal A := (Nat.one_le_div_iff hApos).mpr (by omega)
      have h3 : 2 * (bitsVal N % bitsVal A) ≤ bitsVal N := by nlinarith
      nlinarith
  · -- even `A`: the product halves
    rw [if_neg h1]
    unfold jacMeasure
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_drop_one]
    have h2 : bitsVal A % 2 = 0 := by
      rw [bitsVal_mod_two]; simp only [Bool.not_eq_true] at h1; rw [h1]; rfl
    have hs := size_lt_of_two_mul_le (P' := bitsVal A / 2 * bitsVal N) hP (by
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2); nlinarith)
    have : (if bitsVal N ≤ bitsVal A / 2 then 1 else 0) ≤
        (if bitsVal N ≤ bitsVal A then 1 else 0) := by split_ifs <;> omega
    omega

/-- The answer read off a final state `⟨0, ⟨N, s⟩⟩`: `sign + 1` if `N = 1`, else `1`. -/
def jacOut (S : List Bool) : List Bool :=
  if beq (pairEncode (pairFstD (pairSndD S)) [true]) then
    (if (pairSndD (pairSndD S)).headD false then [] else [false, true])
  else [true]

/-- The Jacobi algorithm: `2(|z| + 1)` rounds from `⟨a, ⟨n, +1⟩⟩`, then `jacOut`. -/
def jacobiAlg (z : List Bool) : List Bool :=
  jacOut (jacStep^[2 * (z.length + 1) ^ 1]
    (pairEncode (pairFstD z) (pairEncode (pairSndD z) [false])))

/-- **The Jacobi symbol is computable in polynomial time** [AB09, §7.2.2, p. 128, second
fact] (polynomial rather than the book's `O(log A · log N)`): `jacobiAlg` is polynomial-time.

**Proof sketch.** The rounds never lengthen the slots (`JacInv`), so
`polyTimeComputable_iterate` applies with a linear envelope; `jacOut` is a comparison and a
bit test. -/
theorem polyTimeComputable_jacobiAlg : PolyTimeComputable jacobiAlg := by
  have h0 : ∀ z : List Bool, JacInv z (pairEncode (pairFstD z) (pairEncode (pairSndD z) [false])) :=
    fun z => ⟨_, _, _, rfl, length_pairFstD_le z, length_pairSndD_le z, by simp,
      fun hn => ⟨hn, by simp [signOf]⟩⟩
  have hinit : PolyTimeComputable
      (fun z => pairEncode (pairFstD z) (pairEncode (pairSndD z) [false])) :=
    polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const _))
  have hloop := polyTimeComputable_iterate polyTimeComputable_jacStep hinit 2 1 5 1
    (fun z i _ => by
      obtain ⟨A, N, s, he, hA, hN, hs, -⟩ :=
        iterate_invariant (JacInv z) (fun _ h => jacInv_step h) i (h0 z)
      rw [he]; simp only [length_pairEncode, pow_one]; omega)
  have hout : PolyTimeComputable jacOut := by
    unfold jacOut
    exact polyTimeComputable_ite (polyTimeComputable_beq.comp
        (polyTimeComputable_slot2.pairEncode (polyTimeComputable_const [true])))
      (polyTimeComputable_ite (polyTimeComputable_headD.comp polyTimeComputable_slot3)
        (polyTimeComputable_const []) (polyTimeComputable_const _))
      (polyTimeComputable_const _)
  exact hout.comp hloop

/-- **Correctness of the Jacobi algorithm** [AB09, §7.2.2]: for odd `n`, `jacobiAlg` returns
the encoded Jacobi symbol `(a/n)`.

**Proof sketch.** `JacInv` keeps `sign · (A/N) = (a/n)` with `N` odd: halving uses
`(2/N) = χ₈(N)`, the odd round uses reciprocity and `(N/A) = ((N mod A)/A)`. The potential
`size(A·N) + [N ≤ A]` (at most `|z| + 1`) drops on every round with `A ≠ 0`, so after
`2(|z| + 1)` rounds `A = 0`, where `(0/N) = [N = 1]`. -/
theorem jacobiAlg_eq (z : List Bool) (hn : Odd (bitsVal (pairSndD z))) :
    jacobiAlg z = jacobi z := by
  have h0 : JacInv z (pairEncode (pairFstD z) (pairEncode (pairSndD z) [false])) :=
    ⟨_, _, _, rfl, length_pairFstD_le z, length_pairSndD_le z, by simp,
      fun hn => ⟨hn, by simp [signOf]⟩⟩
  let I : List Bool → Prop := fun S => JacInv z S
  have hμ := iterate_measure_eq_zero (g := jacStep) I jacMeasure (fun _ h => jacInv_step h)
    (fun S h => by
      obtain ⟨A, N, s, rfl, -, -, -, hv⟩ := h
      exact (jacMeasure_step A N s (hv hn).1).1)
    (fun S h => by
      obtain ⟨A, N, s, rfl, -, -, -, hv⟩ := h
      exact (jacMeasure_step A N s (hv hn).1).2)
    (2 * (z.length + 1) ^ 1) _ h0 (by
      simp only [jacMeasure, pairFstD_pairEncode, pairSndD_pairEncode, pow_one]
      have hs : Nat.size (bitsVal (pairFstD z) * bitsVal (pairSndD z)) ≤ z.length := by
        rw [Nat.size_le]
        calc bitsVal (pairFstD z) * bitsVal (pairSndD z)
            < 2 ^ (pairFstD z).length * 2 ^ (pairSndD z).length := by
              rcases Nat.eq_zero_or_pos (bitsVal (pairSndD z)) with h0 | h0
              · rw [h0, mul_zero]; positivity
              · exact Nat.mul_lt_mul_of_lt_of_le (bitsVal_lt_two_pow _)
                  (bitsVal_lt_two_pow _).le (by positivity)
          _ ≤ 2 ^ z.length := by
              rw [← pow_add]; apply Nat.pow_le_pow_right (by norm_num)
              have := length_pair_components_le z; omega
      split_ifs <;> omega)
  obtain ⟨A, N, s, he, -, -, hs, hv⟩ :=
    iterate_invariant I (fun _ h => jacInv_step h) (2 * (z.length + 1) ^ 1) h0
  obtain ⟨hNo, hJ⟩ := hv hn
  rw [he] at hμ
  simp only [jacMeasure, pairFstD_pairEncode, pairSndD_pairEncode] at hμ
  have hA : bitsVal A = 0 := by
    have hs0 := Nat.size_eq_zero.mp (by omega : Nat.size (bitsVal A * bitsVal N) = 0)
    have hN0 := hNo.pos
    rcases Nat.mul_eq_zero.mp hs0 with h | h <;> omega
  rw [hA] at hJ
  unfold jacobiAlg jacobi jacOut
  rw [he]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, beq, bitsVal, Bool.toNat_true,
    mul_zero, add_zero]
  rw [← hJ]
  have hb2 : Nat.bits 2 = [false, true] := by
    rw [show (2 : ℕ) = 2 * 1 by rfl, Nat.bit0_bits 1 one_ne_zero, Nat.one_bits]
  by_cases hN1 : bitsVal N = 1
  · simp only [hN1, decide_true, if_true, jacobiSym.one_right, mul_one, signOf]
    cases s.headD false <;> simp [Nat.zero_bits, hb2]
  · have hN1' : 1 < bitsVal N := by have := hNo.pos; omega
    simp only [hN1, decide_false, Bool.false_eq_true, if_false, Nat.cast_zero,
      jacobiSym.zero_left hN1', mul_zero, zero_add]
    simp [Nat.one_bits]

/-- `jacobiAlg` on encoded numbers with `n` odd is the encoded Jacobi symbol. -/
theorem jacobiAlg_pairEncode (a n : ℕ) (hn : Odd n) :
    jacobiAlg (pairEncode (Nat.bits a) (Nat.bits n)) = Nat.bits (jacobiSym a n + 1).toNat := by
  rw [jacobiAlg_eq _ (by simpa [bitsVal_bits] using hn)]
  simp [jacobi, bitsVal_bits]

/-- The Jacobi symbol as a residue: `((a/n) + 1 + n - 1) mod n`, i.e. `(a/n) mod n`. -/
def jacobiModAlg (z : List Bool) : List Bool :=
  mod (pairEncode (sub (pairEncode (add (pairEncode (jacobiAlg z) (pairSndD z))) [true]))
    (pairSndD z))

/-- **The Jacobi symbol modulo `n` is polynomial-time** (the form compared with
`A^((N-1)/2) mod N` in the test of [AB09, §7.2.2]). -/
theorem polyTimeComputable_jacobiModAlg : PolyTimeComputable jacobiModAlg :=
  polyTimeComputable_mod.comp ((polyTimeComputable_sub.comp
    ((polyTimeComputable_add.comp (polyTimeComputable_jacobiAlg.pairEncode
      polyTimeComputable_pairSndD)).pairEncode (polyTimeComputable_const [true]))).pairEncode
    polyTimeComputable_pairSndD)

/-- `jacobiModAlg` on encoded numbers with `n` odd is the residue `(a/n) mod n`. -/
theorem jacobiModAlg_pairEncode (a n : ℕ) (hn : Odd n) :
    jacobiModAlg (pairEncode (Nat.bits a) (Nat.bits n)) =
      Nat.bits (jacobiSym a n % (n : ℤ)).toNat := by
  have hn1 : 1 ≤ n := hn.pos
  simp only [jacobiModAlg, jacobiAlg_pairEncode a n hn, pairSndD_pairEncode, add_pairEncode,
    mod, sub, pairFstD_pairEncode, bitsVal_bits]
  congr 1
  rcases jacobiSym.trichotomy a n with h | h | h <;> rw [h] <;> simp [bitsVal]
  · rw [show (1 : ℤ) % n = ((1 % n : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]
  · have e : (-1 : ℤ) = ((n : ℤ) - 1) + n * (-1) := by ring
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

end BinArith

end Complexity
