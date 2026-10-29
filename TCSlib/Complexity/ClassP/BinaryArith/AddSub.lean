/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Basic
import TCSlib.Complexity.ClassNP.PClosure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary comparison, addition and subtraction in polynomial time

Infrastructure for [AB09 §7.2]; not itself a result of the book. A pair of numbers is the
word `pairEncode (Nat.bits a) (Nat.bits b)`; every operation is defined on all words, reading
the components with `Complexity.LogProg.bitsVal` (so malformed words count as `0`), and
outputs a normalized word `Nat.bits n` or a one-bit answer.

## Main definitions

* `Complexity.BinArith.add`, `Complexity.BinArith.sub` — sum and truncated difference.
* `Complexity.BinArith.lt`, `Complexity.BinArith.le`, `Complexity.BinArith.beq` — comparisons.

## Main results

* `Complexity.BinArith.polyTimeComputable_add`, `polyTimeComputable_sub` — the carry and
  borrow chains are one finite-state scan (`Complexity.BinArith.polyTimeComputable_serial`)
  followed by normalization.
* `Complexity.BinArith.polyTimeComputable_lt`, `polyTimeComputable_le`,
  `polyTimeComputable_beq`, and the languages `lt_mem_P`, `le_mem_P`, `beq_mem_P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### Carry and borrow chains -/

/-- The carry out of a full adder with carry in `c` and bits `x`, `y`. -/
def carry (c x y : Bool) : Bool := (x && y) || (c && (x ^^ y))

/-- The sum (and difference) bit `x ⊕ y ⊕ c`. -/
def sumBit (c x y : Bool) : Bool := (x ^^ y) ^^ c

/-- The borrow out of a full subtractor computing `x - y - c`. -/
def borrow (c x y : Bool) : Bool := (!x && y) || (!(x ^^ y) && c)

/-- **The carry chain adds**: over `N` padded pairs of words of length at most `N`, the
output plus `2^N` times the final carry is `bitsVal a + bitsVal b + c`.

**Proof sketch.** Induction on `N`: a full-adder step satisfies `s + 2c' = x + y + c`, and
the scan of the tails accounts for the rest at weight `2`. -/
theorem serial_add : ∀ (N : ℕ) (a b : List Bool) (c : Bool), a.length ≤ N → b.length ≤ N →
    bitsVal (serialOut carry sumBit c (padZip a b N)) +
        2 ^ N * (serialState carry c (padZip a b N)).toNat =
      bitsVal a + bitsVal b + c.toNat := by
  intro N
  induction N with
  | zero =>
    intro a b c ha hb
    rw [List.eq_nil_of_length_eq_zero (by omega : a.length = 0),
      List.eq_nil_of_length_eq_zero (by omega : b.length = 0)]
    simp [padZip, serialOut, serialState, bitsVal]
  | succ N ih =>
    intro a b c ha hb
    have hbit : ∀ c x y : Bool,
        (sumBit c x y).toNat + 2 * (carry c x y).toNat = x.toNat + y.toNat + c.toNat := by
      decide
    have h := ih (a.drop 1) (b.drop 1) (carry c (a.headD false) (b.headD false))
      (by simp; omega) (by simp; omega)
    have h2 := hbit c (a.headD false) (b.headD false)
    rw [bitsVal_eq_headD a, bitsVal_eq_headD b]
    simp only [padZip, serialOut, serialState, bitsVal, pow_succ]
    linarith

/-- **The borrow chain subtracts**: over `N` padded pairs of words of length at most `N`, the
output plus `bitsVal b + c` is `bitsVal a` plus `2^N` times the final borrow.

**Proof sketch.** Induction on `N`: a full-subtractor step satisfies `d + y + c = x + 2c'`. -/
theorem serial_sub : ∀ (N : ℕ) (a b : List Bool) (c : Bool), a.length ≤ N → b.length ≤ N →
    bitsVal (serialOut borrow sumBit c (padZip a b N)) + bitsVal b + c.toNat =
      bitsVal a + 2 ^ N * (serialState borrow c (padZip a b N)).toNat := by
  intro N
  induction N with
  | zero =>
    intro a b c ha hb
    rw [List.eq_nil_of_length_eq_zero (by omega : a.length = 0),
      List.eq_nil_of_length_eq_zero (by omega : b.length = 0)]
    cases c <;> simp [padZip, serialOut, serialState, bitsVal]
  | succ N ih =>
    intro a b c ha hb
    have hbit : ∀ c x y : Bool,
        (sumBit c x y).toNat + y.toNat + c.toNat = x.toNat + 2 * (borrow c x y).toNat := by
      decide
    have h := ih (a.drop 1) (b.drop 1) (borrow c (a.headD false) (b.headD false))
      (by simp; omega) (by simp; omega)
    have h2 := hbit c (a.headD false) (b.headD false)
    rw [bitsVal_eq_headD a, bitsVal_eq_headD b]
    simp only [padZip, serialOut, serialState, bitsVal, pow_succ]
    linarith

/-- Both component values of `z` are below `2^(|z|+2)`, the scan length used on `z`. -/
private theorem serial_bounds (z : List Bool) :
    bitsVal (pairFstD z) < 2 ^ (z.length + 2) ∧ bitsVal (pairSndD z) < 2 ^ (z.length + 2) := by
  have h1 := (bitsVal_lt_two_pow (pairFstD z)).trans_le
    (Nat.pow_le_pow_right (by norm_num) ((length_pairFstD_le z).trans (Nat.le_add_right _ 2)))
  have h2 := (bitsVal_lt_two_pow (pairSndD z)).trans_le
    (Nat.pow_le_pow_right (by norm_num) ((length_pairSndD_le z).trans (Nat.le_add_right _ 2)))
  exact ⟨h1, h2⟩

/-- On a word `z`, the final borrow of the subtraction scan decides `fst < snd`, and when it
is clear the scan's output is the difference. -/
theorem serial_sub_spec (z : List Bool) :
    serialState borrow false (padZip (pairFstD z) (pairSndD z) (z.length + 2)) =
        decide (bitsVal (pairFstD z) < bitsVal (pairSndD z)) ∧
      (bitsVal (pairSndD z) ≤ bitsVal (pairFstD z) →
        bitsVal (serialOut borrow sumBit false (padZip (pairFstD z) (pairSndD z) (z.length + 2)))
          = bitsVal (pairFstD z) - bitsVal (pairSndD z)) := by
  have h := serial_sub (z.length + 2) (pairFstD z) (pairSndD z) false
    (by have := length_pairFstD_le z; omega) (by have := length_pairSndD_le z; omega)
  have hR := bitsVal_lt_two_pow
    (serialOut borrow sumBit false (padZip (pairFstD z) (pairSndD z) (z.length + 2)))
  rw [length_serialOut, length_padZip] at hR
  obtain ⟨ha, hb⟩ := serial_bounds z
  generalize 2 ^ (z.length + 2) = P at h hR ha hb
  cases hs : serialState borrow false (padZip (pairFstD z) (pairSndD z) (z.length + 2)) <;>
    simp only [hs, Bool.toNat_false, Bool.toNat_true] at h <;> simp at h ⊢ <;> omega

/-! ### Addition and subtraction -/

/-- The sum of the values of the two components of `z`, as a binary word. -/
def add (z : List Bool) : List Bool := Nat.bits (bitsVal (pairFstD z) + bitsVal (pairSndD z))

/-- The truncated difference `fst ∸ snd` of the values of the components of `z`. -/
def sub (z : List Bool) : List Bool := Nat.bits (bitsVal (pairFstD z) - bitsVal (pairSndD z))

/-- `add` on encoded numbers is addition. -/
@[simp] theorem add_pairEncode (a b : ℕ) :
    add (pairEncode (Nat.bits a) (Nat.bits b)) = Nat.bits (a + b) := by
  simp [add, bitsVal_bits]

/-- `sub` on encoded numbers is truncated subtraction. -/
@[simp] theorem sub_pairEncode (a b : ℕ) :
    sub (pairEncode (Nat.bits a) (Nat.bits b)) = Nat.bits (a - b) := by
  simp [sub, bitsVal_bits]

/-- **Binary addition is polynomial-time** (infrastructure for [AB09 §7.2]; not itself a
result of the book): the carry chain, then normalization.

**Proof sketch.** Scan `|z| + 2` padded pairs (`serial_add`); since `a + b < 2^{|z|+2}` the
final carry is `0`, so the output has value `a + b`, and `polyTimeComputable_normBits`
normalizes it. -/
theorem polyTimeComputable_add : PolyTimeComputable add := by
  convert polyTimeComputable_normBits.comp (polyTimeComputable_serial carry sumBit false) using 1
  funext z
  simp only [Function.comp_apply, add]
  congr 1
  have h := serial_add (z.length + 2) (pairFstD z) (pairSndD z) false
    (by have := length_pairFstD_le z; omega) (by have := length_pairSndD_le z; omega)
  have hlt : bitsVal (pairFstD z) + bitsVal (pairSndD z) < 2 ^ (z.length + 2) := by
    have h1 := (bitsVal_lt_two_pow (pairFstD z)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (length_pairFstD_le z))
    have h2 := (bitsVal_lt_two_pow (pairSndD z)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (length_pairSndD_le z))
    have : 2 ^ (z.length + 2) = 4 * 2 ^ z.length := by ring
    omega
  generalize 2 ^ (z.length + 2) = P at h hlt
  cases hs : serialState carry false (padZip (pairFstD z) (pairSndD z) (z.length + 2)) <;>
    simp only [hs, Bool.toNat_false, Bool.toNat_true] at h <;> omega

/-! ### Comparisons -/

/-- The test `fst < snd` on the values of the components of `z`. -/
def lt (z : List Bool) : Bool := decide (bitsVal (pairFstD z) < bitsVal (pairSndD z))

/-- The test `fst ≤ snd` on the values of the components of `z`. -/
def le (z : List Bool) : Bool := decide (bitsVal (pairFstD z) ≤ bitsVal (pairSndD z))

/-- The test `fst = snd` on the values of the components of `z`. -/
def beq (z : List Bool) : Bool := decide (bitsVal (pairFstD z) = bitsVal (pairSndD z))

/-- `lt` on encoded numbers is `<`. -/
@[simp] theorem lt_pairEncode (a b : ℕ) :
    lt (pairEncode (Nat.bits a) (Nat.bits b)) = decide (a < b) := by simp [lt, bitsVal_bits]

/-- `le` on encoded numbers is `≤`. -/
@[simp] theorem le_pairEncode (a b : ℕ) :
    le (pairEncode (Nat.bits a) (Nat.bits b)) = decide (a ≤ b) := by simp [le, bitsVal_bits]

/-- `beq` on encoded numbers is `=`. -/
@[simp] theorem beq_pairEncode (a b : ℕ) :
    beq (pairEncode (Nat.bits a) (Nat.bits b)) = decide (a = b) := by simp [beq, bitsVal_bits]

/-- **Binary comparison `<` is polynomial-time**: the last bit of the scan emitting the
running borrow is the final borrow. -/
theorem polyTimeComputable_lt : PolyTimeComputable (fun z => [lt z]) := by
  convert polyTimeComputable_lastBit.comp (polyTimeComputable_serial borrow borrow false) using 1
  funext z
  simp only [Function.comp_apply, lt]
  rw [getLastD_serialOut_self _ _ _ (by
    rw [← List.length_pos_iff, length_padZip]; omega), (serial_sub_spec z).1]

/-- **Binary comparison `≤` is polynomial-time** (`¬ snd < fst`). -/
theorem polyTimeComputable_le : PolyTimeComputable (fun z => [le z]) := by
  convert polyTimeComputable_not (polyTimeComputable_lt.comp polyTimeComputable_pairSwap)
    using 1
  funext z
  by_cases h : bitsVal (pairSndD z) < bitsVal (pairFstD z) <;> simp [h, le, lt]
  omega

/-- **Binary equality is polynomial-time** (`≤` both ways). -/
theorem polyTimeComputable_beq : PolyTimeComputable (fun z => [beq z]) := by
  convert polyTimeComputable_and polyTimeComputable_le
    (polyTimeComputable_le.comp polyTimeComputable_pairSwap) using 1
  funext z
  simp only [le, beq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.cons.injEq, and_true]
  by_cases h : bitsVal (pairFstD z) = bitsVal (pairSndD z)
  · simp [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h' <;> simp [h, h'.le, Nat.not_le_of_lt h']

/-- **Binary subtraction is polynomial-time**: `0` when `fst < snd`, else the borrow chain's
output, normalized. -/
theorem polyTimeComputable_sub : PolyTimeComputable sub := by
  convert polyTimeComputable_ite polyTimeComputable_lt (polyTimeComputable_const [])
    (polyTimeComputable_normBits.comp (polyTimeComputable_serial borrow sumBit false)) using 1
  funext z
  simp only [Function.comp_apply, sub, lt]
  by_cases h : bitsVal (pairFstD z) < bitsVal (pairSndD z)
  · simp [h, Nat.sub_eq_zero_of_le h.le, Nat.zero_bits]
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    rw [(serial_sub_spec z).2 (by omega)]

/-- The language `{⟨a, b⟩ : a < b}` is in `P` (components read by `bitsVal`; malformed words
read as 0). -/
theorem lt_mem_P : {z | lt z = true} ∈ P := mem_P_of_test polyTimeComputable_lt

/-- The language `{⟨a, b⟩ : a ≤ b}` is in `P` (components read by `bitsVal`; malformed words
read as 0). -/
theorem le_mem_P : {z | le z = true} ∈ P := mem_P_of_test polyTimeComputable_le

/-- The language `{⟨a, b⟩ : a = b}` is in `P` (components read by `bitsVal`; malformed words
read as 0). -/
theorem beq_mem_P : {z | beq z = true} ∈ P := mem_P_of_test polyTimeComputable_beq

end BinArith

end Complexity
