/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.AddSub

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary multiplication and word reversal in polynomial time

Infrastructure for [AB09 §7.2]; not itself a result of the book. Multiplication is the
shift-and-add loop, run through `Complexity.BinArith.polyTimeComputable_iterate`; reversal
(used by long division, which reads the dividend from its top bit) is the same kind of loop.

## Main definitions

* `Complexity.BinArith.mul` — the product of the two components of a pair.
* `Complexity.BinArith.mulStep` — one round of shift-and-add on `⟨A, ⟨B, acc⟩⟩`.
* `Complexity.BinArith.revStep` — one round of reversal on `⟨src, acc⟩`.

## Main results

* `Complexity.BinArith.polyTimeComputable_mul` — binary multiplication is polynomial-time.
* `Complexity.BinArith.polyTimeComputable_reverse` — word reversal is polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### Reversal -/

/-- One round of reversal on `⟨src, acc⟩`: move the head of `src` onto `acc`. -/
def revStep (S : List Bool) : List Bool :=
  if isNilB (pairFstD S) then S
  else pairEncode ((pairFstD S).drop 1) ((pairFstD S).headD false :: pairSndD S)

/-- A reversal round is polynomial-time. -/
theorem polyTimeComputable_revStep : PolyTimeComputable revStep := by
  unfold revStep
  refine polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
    polyTimeComputable_id ?_
  exact (polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_cons (polyTimeComputable_headD.comp polyTimeComputable_pairFstD)
      polyTimeComputable_pairSndD)

/-- Reversal rounds keep `reverse src ++ acc` and the total length. -/
theorem revStep_pairEncode (u v : List Bool) :
    ∃ u' v', revStep (pairEncode u v) = pairEncode u' v' ∧ u'.reverse ++ v' = u.reverse ++ v ∧
      u'.length + v'.length = u.length + v.length ∧ (u ≠ [] → u'.length < u.length) ∧
      (u = [] → u' = []) := by
  cases u with
  | nil => exact ⟨[], v, by simp [revStep, isNilB], rfl, rfl, by simp, fun _ => rfl⟩
  | cons b u =>
    refine ⟨u, b :: v, by simp [revStep, isNilB], by simp, by simp; omega, by simp, by simp⟩

/-- **Word reversal is polynomial-time**: `|w| + 1` reversal rounds from `⟨w, []⟩`.

**Proof sketch.** Each round moves the head of `src` onto `acc`, keeping
`reverse src ++ acc = reverse w` and the total length; `|src|` reaches `0` within `|w|`
rounds, after which the state is fixed and `acc = reverse w`. -/
theorem polyTimeComputable_reverse : PolyTimeComputable (fun w : List Bool => w.reverse) := by
  let I : List Bool → List Bool → Prop := fun w S => ∃ u v, S = pairEncode u v ∧
    u.reverse ++ v = w.reverse ∧ u.length + v.length = w.length
  have hI : ∀ w S, I w S → I w (revStep S) := by
    rintro w S ⟨u, v, rfl, h1, h2⟩
    obtain ⟨u', v', he, h1', h2', -, -⟩ := revStep_pairEncode u v
    exact ⟨u', v', he, h1'.trans h1, h2'.trans h2⟩
  have h0 : ∀ w, I w (pairEncode w []) := fun w => ⟨w, [], rfl, by simp, by simp⟩
  have hinit : PolyTimeComputable (fun w : List Bool => pairEncode w []) :=
    polyTimeComputable_id.pairEncode (polyTimeComputable_const [])
  have hloop := polyTimeComputable_iterate polyTimeComputable_revStep hinit 1 1 3 1
    (fun w i _ => by
      obtain ⟨u, v, he, -, h2⟩ := iterate_invariant (I w) (hI w) i (h0 w)
      rw [he, length_pairEncode]; simp; omega)
  convert polyTimeComputable_pairSndD.comp hloop using 1
  funext w
  obtain ⟨u, v, he, h1, -⟩ := iterate_invariant (I w) (hI w) (1 * (w.length + 1) ^ 1) (h0 w)
  have hμ := iterate_measure_eq_zero (g := revStep) (I w) (fun S => (pairFstD S).length) (hI w)
    (by
      rintro S ⟨u, v, rfl, -, -⟩ hpos
      obtain ⟨u', v', he', -, -, hlt, -⟩ := revStep_pairEncode u v
      rw [he']; simp only [pairFstD_pairEncode] at hpos ⊢
      exact hlt (List.ne_nil_of_length_pos hpos))
    (by
      rintro S ⟨u, v, rfl, -, -⟩ h0
      simp only [pairFstD_pairEncode, List.length_eq_zero_iff] at h0
      subst h0; simp [revStep, isNilB])
    (1 * (w.length + 1) ^ 1) (pairEncode w []) (h0 w) (by simp)
  rw [he] at hμ
  simp only [pairFstD_pairEncode, List.length_eq_zero_iff] at hμ
  subst hμ
  simp only [Function.comp_apply, he, pairSndD_pairEncode]
  simpa using h1.symm

/-! ### Multiplication -/

/-- The product of the values of the two components of `z`, as a binary word. -/
def mul (z : List Bool) : List Bool := Nat.bits (bitsVal (pairFstD z) * bitsVal (pairSndD z))

/-- `mul` on encoded numbers is multiplication. -/
@[simp] theorem mul_pairEncode (a b : ℕ) :
    mul (pairEncode (Nat.bits a) (Nat.bits b)) = Nat.bits (a * b) := by
  simp [mul, bitsVal_bits]

/-- One round of shift-and-add on `⟨A, ⟨B, acc⟩⟩`: if the low bit of `B` is set add `A` to
`acc`; then double `A` and halve `B`. A state with `B = []` is fixed. -/
def mulStep (S : List Bool) : List Bool :=
  if isNilB (pairFstD (pairSndD S)) then S
  else pairEncode (false :: pairFstD S)
    (pairEncode ((pairFstD (pairSndD S)).drop 1)
      (if (pairFstD (pairSndD S)).headD false then
        add (pairEncode (pairSndD (pairSndD S)) (pairFstD S))
      else pairSndD (pairSndD S)))

/-- A shift-and-add round is polynomial-time. -/
theorem polyTimeComputable_mulStep : PolyTimeComputable mulStep := by
  unfold mulStep
  refine polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_slot2)
    polyTimeComputable_id ?_
  refine (polyTimeComputable_cons (polyTimeComputable_const [false])
    polyTimeComputable_pairFstD).pairEncode
    ((polyTimeComputable_tail.comp polyTimeComputable_slot2).pairEncode ?_)
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp polyTimeComputable_slot2)
    (polyTimeComputable_add.comp (polyTimeComputable_slot3.pairEncode polyTimeComputable_pairFstD))
    polyTimeComputable_slot3

/-- The invariant of the multiplication loop on input `z`: `acc + A·B = a·b`, `acc` is
normalized, and `|A| + |B|` does not grow. -/
def MulInv (z S : List Bool) : Prop :=
  ∃ A B C, S = pairEncode A (pairEncode B C) ∧
    bitsVal C + bitsVal A * bitsVal B = bitsVal (pairFstD z) * bitsVal (pairSndD z) ∧
    C = Nat.bits (bitsVal C) ∧ A.length + B.length ≤ (pairFstD z).length + (pairSndD z).length

/-- The shift-and-add round preserves the invariant, and shortens a nonempty `B`.

**Proof sketch.** With `B = b₀ + 2B'`, the round maps `acc + A·B` to `(acc + b₀A) + 2A·B'`,
the same value; `|A|` grows by one while `|B|` drops by one. -/
theorem mulInv_step {z S : List Bool} (h : MulInv z S) :
    MulInv z (mulStep S) ∧
      ((pairFstD (pairSndD S)) ≠ [] →
        (pairFstD (pairSndD (mulStep S))).length < (pairFstD (pairSndD S)).length) ∧
      ((pairFstD (pairSndD S)) = [] → mulStep S = S) := by
  obtain ⟨A, B, C, rfl, hv, hC, hl⟩ := h
  have hB := bitsVal_eq_headD B
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨?_, fun hne => ?_, fun he => by simp [mulStep, isNilB, he]⟩
  · unfold mulStep
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    split_ifs with h1 h2
    · exact ⟨A, B, C, rfl, hv, hC, hl⟩
    · have hne : B ≠ [] := by simpa [isNilB] using h1
      refine ⟨false :: A, B.drop 1, _, rfl, ?_, by simp [add, bitsVal_bits], ?_⟩
      · simp only [add, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_bits, bitsVal,
          Bool.toNat_false, zero_add]
        rw [h2, Bool.toNat_true] at hB
        rw [← hv, hB]; ring
      · have := List.length_pos_iff.mpr hne
        simp; omega
    · have hne : B ≠ [] := by simpa [isNilB] using h1
      refine ⟨false :: A, B.drop 1, C, rfl, ?_, hC, ?_⟩
      · simp only [bitsVal, Bool.toNat_false, zero_add]
        simp only [Bool.not_eq_true] at h2
        rw [h2, Bool.toNat_false, zero_add] at hB
        rw [← hv, hB]; ring
      · have := List.length_pos_iff.mpr hne
        simp; omega
  · have hne' : isNilB B = false := by simpa [isNilB] using hne
    simp only [mulStep, pairFstD_pairEncode, pairSndD_pairEncode, hne', Bool.false_eq_true,
      if_false, List.length_drop]
    have := List.length_pos_iff.mpr hne
    omega

/-- A state satisfying the multiplication invariant has length at most `4(|z| + 1)`
(`acc ≤ a·b < 2^{|a|+|b|}` bounds the normalized `acc`). -/
theorem length_le_of_mulInv {z S : List Bool} (h : MulInv z S) : S.length ≤ 4 * (z.length + 1) := by
  obtain ⟨A, B, C, rfl, hv, hC, hl⟩ := h
  have hCl : C.length ≤ (pairFstD z).length + (pairSndD z).length := by
    rw [hC]
    apply length_bits_le
    calc bitsVal C ≤ bitsVal (pairFstD z) * bitsVal (pairSndD z) := by omega
      _ < 2 ^ (pairFstD z).length * 2 ^ (pairSndD z).length := by
          rcases Nat.eq_zero_or_pos (bitsVal (pairSndD z)) with h0 | h0
          · rw [h0, mul_zero]; positivity
          · exact Nat.mul_lt_mul_of_lt_of_le (bitsVal_lt_two_pow _)
              (bitsVal_lt_two_pow _).le (by positivity)
      _ = 2 ^ ((pairFstD z).length + (pairSndD z).length) := by rw [pow_add]
  have hz := length_pair_components_le z
  simp only [length_pairEncode]
  omega

/-- The input state `⟨a, ⟨b, []⟩⟩` of the multiplication loop. -/
def mulInit (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairEncode (pairSndD z) [])

/-- The input state satisfies the multiplication invariant. -/
theorem mulInv_init (z : List Bool) : MulInv z (mulInit z) :=
  ⟨_, _, [], rfl, by simp [bitsVal], by simp [bitsVal, Nat.zero_bits], le_rfl⟩

/-- **Binary multiplication is polynomial-time** (infrastructure for [AB09 §7.2]; not
itself a result of the book).

**Proof sketch.** Run `|z| + 1` shift-and-add rounds from `⟨a, ⟨b, []⟩⟩`
(`polyTimeComputable_iterate`). The invariant `acc + A·B = a·b` (`MulInv`) holds throughout
and bounds the state length linearly; `|B|` drops each round until `B = []`, which is then
fixed (`iterate_measure_eq_zero`), so the final `acc` is `Nat.bits (a·b)`. -/
theorem polyTimeComputable_mul : PolyTimeComputable mul := by
  have hinit : PolyTimeComputable mulInit :=
    polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))
  have hloop := polyTimeComputable_iterate polyTimeComputable_mulStep hinit 1 1 4 1
    (fun z i _ => by
      simpa using length_le_of_mulInv
        (iterate_invariant (MulInv z) (fun _ h => (mulInv_step h).1) i (mulInv_init z)))
  convert polyTimeComputable_slot3.comp hloop using 1
  funext z
  have hμ := iterate_measure_eq_zero (g := mulStep) (MulInv z)
    (fun S => (pairFstD (pairSndD S)).length) (fun _ h => (mulInv_step h).1)
    (fun S h hpos => (mulInv_step h).2.1 (List.ne_nil_of_length_pos hpos))
    (fun S h h0 => (mulInv_step h).2.2 (List.length_eq_zero_iff.mp h0))
    (1 * (z.length + 1) ^ 1) (mulInit z) (mulInv_init z)
    (by simp [mulInit]; have := length_pairSndD_le z; omega)
  obtain ⟨A, B, C, he, hv, hC, -⟩ :=
    iterate_invariant (MulInv z) (fun _ h => (mulInv_step h).1) (1 * (z.length + 1) ^ 1)
      (mulInv_init z)
  rw [he] at hμ
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_eq_zero_iff] at hμ
  subst hμ
  simp only [Function.comp_apply, he, pairSndD_pairEncode, mul]
  rw [hC]
  simp only [bitsVal, mul_zero, add_zero] at hv
  rw [hv]

end BinArith

end Complexity
