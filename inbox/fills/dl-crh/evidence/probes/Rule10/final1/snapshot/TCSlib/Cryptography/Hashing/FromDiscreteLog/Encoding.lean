/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounded exponents with a selector bit

The domain in Protocol 142.2 consists of an `n`-bit numeral below a bound `m`, followed
by one unrestricted selector bit. These encoding lemmas identify that domain with
`Fin m × Bool`.

## Main definitions

* `boundedInputEquiv` pairs a bounded exponent with its final selector bit.

## Main results

* `ofFn_splitBits_fst`, `ofFn_splitBits_snd` read the words of two consecutive bit vectors.
* `inputWord_num_ext` reconstructs an input from its exponent value and selector bit.
* `card_boundedInput` gives `2 * m` inputs when `m ≤ 2 ^ n`.
* `card_boundedRange` gives `p - 1` positive `n`-bit numerals below `p`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, Protocol 142.2 and the proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open TCSlib.Cryptography TCSlib.Cryptography.Candidates TCSlib.Cryptography.NumberTheory

/-- The word of the first component of `splitBits w` is the first `a` bits of `w`. -/
theorem ofFn_splitBits_fst {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).1 = (List.ofFn w).take a := by
  have hfst : (splitBits w).1 = fun j : Fin a => w (Fin.castAdd b j) :=
    funext fun j => splitBits_fst w j
  rw [hfst]
  have hwindow := ofFn_drop_take w 0 a (by omega)
  simpa only [List.drop_zero, Nat.zero_add] using hwindow.symm

/-- The word of the second component of `splitBits w` is the word of `w` after its first
`a` bits. -/
theorem ofFn_splitBits_snd {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).2 = (List.ofFn w).drop a := by
  have hsnd : (splitBits w).2 = fun j : Fin b => w (Fin.natAdd a j) :=
    funext fun j => splitBits_snd w j
  rw [hsnd]
  have hwindow := ofFn_drop_take w a b (by omega)
  have hlen : ((List.ofFn w).drop a).length = b := by
    simp only [List.length_drop, List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.take_of_length_le hlen.le] at hwindow
  exact hwindow.symm

/-- The word of an `(n + 1)`-bit vector is its first `n` bits followed by its final bit. -/
theorem inputWord_split {n : ℕ} (x : Fin (n + 1) → Bool) :
    List.ofFn x = List.ofFn (fun j : Fin n => x j.castSucc) ++ [x (Fin.last n)] := by
  rw [List.ofFn_succ', List.concat_eq_append]

/-- Taking the first `n` bits of an `(n + 1)`-bit word gives its restricted vector. -/
theorem inputWord_take {n : ℕ} (x : Fin (n + 1) → Bool) :
    (List.ofFn x).take n = List.ofFn (fun j : Fin n => x j.castSucc) := by
  rw [inputWord_split, List.take_left' (by simp)]

/-- Dropping the first `n` bits of an `(n + 1)`-bit word leaves its final bit. -/
theorem inputWord_drop {n : ℕ} (x : Fin (n + 1) → Bool) :
    (List.ofFn x).drop n = [x (Fin.last n)] := by
  rw [inputWord_split, List.drop_left' (by simp)]

/-- An `(n + 1)`-bit input is determined by its first `n` bits and its final bit. -/
theorem inputWord_ext {n : ℕ} {x y : Fin (n + 1) → Bool}
    (hprefix : (List.ofFn x).take n = (List.ofFn y).take n)
    (hlast : x (Fin.last n) = y (Fin.last n)) : x = y := by
  apply List.ofFn_injective
  rw [inputWord_split x, inputWord_split y, ← inputWord_take x, ← inputWord_take y,
    hprefix, hlast]

/-- An `(n + 1)`-bit input is determined by the number read from its first `n` bits
and its final selector bit. -/
theorem inputWord_num_ext {n : ℕ} {x y : Fin (n + 1) → Bool}
    (hnum : listToNat ((List.ofFn x).take n) = listToNat ((List.ofFn y).take n))
    (hlast : x (Fin.last n) = y (Fin.last n)) : x = y := by
  refine inputWord_ext ?_ hlast
  have hxlen : ((List.ofFn x).take n).length = n := by
    rw [inputWord_take, List.length_ofFn]
  have hylen : ((List.ofFn y).take n).length = n := by
    rw [inputWord_take, List.length_ofFn]
  have hxcanon := natToList_length_listToNat ((List.ofFn x).take n)
  have hycanon := natToList_length_listToNat ((List.ofFn y).take n)
  rw [hxlen] at hxcanon
  rw [hylen] at hycanon
  have hword := congrArg (natToList n) hnum
  rw [hxcanon, hycanon] at hword
  exact hword

/-- Bounded `(n + 1)`-bit inputs are exactly pairs of an exponent in `Fin m` and a selector
bit, provided `m ≤ 2 ^ n` [PS10, Protocol 142.2].

**Proof sketch.** Read the first `n` bits as the exponent and keep the last bit. In the other
direction write the exponent as an `n`-bit numeral and append the selector. Numeral
canonicity and the decomposition of an `(n + 1)`-bit vector prove the inverse laws. -/
noncomputable def boundedInputEquiv (n m : ℕ) (hm : m ≤ 2 ^ n) :
    {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m} ≃ Fin m × Bool where
  toFun x := (⟨listToNat ((List.ofFn x.1).take n), x.2⟩, x.1 (Fin.last n))
  invFun z := ⟨padFin (n + 1) (natToList n z.1.val ++ [z.2]), by
    rw [ofFn_padFin_of_length (by simp), List.take_left' (by simp),
      listToNat_natToList (z.1.2.trans_le hm)]
    exact z.1.2⟩
  left_inv x := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ofFn_padFin_of_length (by simp)]
    have hlen : ((List.ofFn x.1).take n).length = n := by
      simp
    have hcanon := natToList_length_listToNat ((List.ofFn x.1).take n)
    rw [hlen] at hcanon
    rw [hcanon, inputWord_take, inputWord_split x.1]
  right_inv z := by
    apply Prod.ext
    · apply Fin.ext
      change listToNat ((List.ofFn
        (padFin (n + 1) (natToList n z.1.val ++ [z.2]))).take n) = z.1.val
      rw [ofFn_padFin_of_length (by simp), List.take_left' (by simp),
        listToNat_natToList (z.1.2.trans_le hm)]
    · have hword := inputWord_drop
        (padFin (n + 1) (natToList n z.1.val ++ [z.2]))
      rw [ofFn_padFin_of_length (by simp), List.drop_left' (by simp)] at hword
      exact List.singleton_inj.mp hword.symm

/-- The bounded-input equivalence reads the exponent and the final selector bit. -/
theorem boundedInputEquiv_apply (n m : ℕ) (hm : m ≤ 2 ^ n)
    (x : {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m}) :
    boundedInputEquiv n m hm x =
      (⟨listToNat ((List.ofFn x.1).take n), x.2⟩, x.1 (Fin.last n)) := rfl

/-- The inverse equivalence writes an `n`-bit exponent and appends its selector bit. -/
theorem boundedInputEquiv_symm_apply (n m : ℕ) (hm : m ≤ 2 ^ n) (z : Fin m × Bool) :
    ((boundedInputEquiv n m hm).symm z).1 =
      padFin (n + 1) (natToList n z.1.val ++ [z.2]) := rfl

/-- There are `2 * m` bounded exponents with a selector bit when `m ≤ 2 ^ n`
[PS10, proof of Theorem 142.3]. -/
theorem card_boundedInput (n m : ℕ) (hm : m ≤ 2 ^ n) :
    Fintype.card {x : Fin (n + 1) → Bool // listToNat ((List.ofFn x).take n) < m} = 2 * m := by
  classical
  rw [Fintype.card_congr (boundedInputEquiv n m hm), Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Nat.mul_comm]

/-- There are `p - 1` positive `n`-bit numerals below `p` when `0 < p ≤ 2 ^ n`
[PS10, proof of Theorem 142.3].

**Proof sketch.** Subtract one from the numeral's value to identify the range with
`Fin (p - 1)`. The inverse writes `j + 1` in `n` bits. Reading and writing numerals are
inverse on values below `2 ^ n`. -/
theorem card_boundedRange (n p : ℕ) (hp : 0 < p) (hpw : p ≤ 2 ^ n) :
    Fintype.card {y : Fin n → Bool //
      0 < listToNat (List.ofFn y) ∧ listToNat (List.ofFn y) < p} = p - 1 := by
  classical
  let e : {y : Fin n → Bool //
      0 < listToNat (List.ofFn y) ∧ listToNat (List.ofFn y) < p} ≃ Fin (p - 1) :=
    { toFun := fun y => ⟨listToNat (List.ofFn y.1) - 1, by
        have hpos := y.2.1
        have hlt := y.2.2
        omega⟩
      invFun := fun j => ⟨natToBits n (j.val + 1), by
        have hj : j.val + 1 < p := by have := j.2; omega
        rw [← bitsToNat_eq_listToNat, bitsToNat_natToBits (hj.trans_le hpw)]
        exact ⟨by omega, hj⟩⟩
      left_inv := fun y => by
        apply Subtype.ext
        change natToBits n (listToNat (List.ofFn y.1) - 1 + 1) = y.1
        have hpos : 1 ≤ listToNat (List.ofFn y.1) := by have := y.2.1; omega
        rw [Nat.sub_add_cancel hpos, ← bitsToNat_eq_listToNat, natToBits_bitsToNat]
      right_inv := fun j => by
        apply Fin.ext
        change listToNat (List.ofFn (natToBits n (j.val + 1))) - 1 = j.val
        have hj : j.val + 1 < p := by have := j.2; omega
        rw [← bitsToNat_eq_listToNat, bitsToNat_natToBits (hj.trans_le hpw)]
        omega }
  rw [Fintype.card_congr e, Fintype.card_fin]

end TCSlib.Cryptography.Authentication.FromDiscreteLog
