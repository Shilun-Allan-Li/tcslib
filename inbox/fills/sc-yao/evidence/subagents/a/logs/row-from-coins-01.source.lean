/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinGarbling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A polynomial-time row garbler from coin words

The row machine receives polynomial-time unary data maps, a kind code, encoded unary
argument indices, and a coin word. Its arity and pre-shift assignment are fixed constants.
All maps are total on arbitrary input strings; short coin words are padded with false bits.

## Main definitions

* `RowFromCoins.assignmentBit`: a fixed assignment bit after the supplied XOR shift.
* `RowFromCoins.gateBit`: the output bit from a kind code and at most two assignment bits.
* `RowFromCoins.keyWord`, `nonceWord`: addressed key and row-nonce words.
* `RowFromCoins.rowWord`: assemble the addressed words and perform nested encryption.

## Main results

* `RowFromCoins.rowWord_poly`: polynomial time on every input word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (garbling from keys and encryption coins).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*,
  STOC 1990, pp. 503–513 (point-and-permute row relabelling).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins

open Complexity Turing TCSlib.Cryptography.EncodingMachines

/-- Position `j` of a fixed assignment to `l` positions, XOR its shift coin at
`10 · bound z · width z + 2 · gate z + j`; absent positions are false. [BMR90] -/
def assignmentBit (width bound gate : List Bool → ℕ) (coins : List Bool → List Bool)
    (l : ℕ) (a : Fin l → Bool) (j : ℕ) (z : List Bool) : Bool :=
  if j < l then xor ((List.ofFn a).getD j false)
    ((coins z).getD (10 * bound z * width z + 2 * gate z + j) false) else false

/-- `assignmentBit ... j z` is the assignment/shift XOR for `j < l`, and false otherwise. -/
theorem assignmentBit_eq (width bound gate : List Bool → ℕ) (coins : List Bool → List Bool)
    (l : ℕ) (a : Fin l → Bool) (j : ℕ) (z : List Bool) :
    assignmentBit width bound gate coins l a j z =
      if j < l then xor ((List.ofFn a).getD j false)
        ((coins z).getD (10 * bound z * width z + 2 * gate z + j) false) else false := rfl

/-- Every fixed shifted-assignment bit is polynomial-time from polynomial-time unary
width, bound, and gate maps and a polynomial-time coin word. [BMR90] -/
theorem assignmentBit_poly {width bound gate : List Bool → ℕ} {coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hcoins : PolyTimeComputable coins) (l : ℕ) (a : Fin l → Bool) (j : ℕ) :
    PolyTimeComputable fun z => [assignmentBit width bound gate coins l a j z] := by
  by_cases h : j < l
  · simpa only [assignmentBit_eq, if_pos h] using
      BinArith.polyTimeComputable_xor (polyTimeComputable_const [((List.ofFn a).getD j false)])
        (CoinGarbling.shiftBit_poly j hcoins hwidth hbound hgate)
  · simpa only [assignmentBit_eq, if_neg h] using polyTimeComputable_const [false]

/-- A gate's output on `l ≤ 2` supplied bits, selected by its two-bit kind code:
`00` selects conjunction, `01` disjunction, and other codes negated conjunction.
The zero- and one-position cases use their usual empty/one-bit values. -/
def gateBit (kind : List Bool → List Bool) (l : ℕ) (b₀ b₁ : List Bool → Bool)
    (z : List Bool) : Bool :=
  if kind z = [false, false] then
    if l = 0 then true else if l = 1 then b₀ z else b₀ z && b₁ z
  else if kind z = [false, true] then
    if l = 0 then false else if l = 1 then b₀ z else b₀ z || b₁ z
  else !(if l = 0 then true else if l = 1 then b₀ z else b₀ z && b₁ z)

/-- `gateBit kind l b₀ b₁ z` is the conjunction, disjunction, or negated conjunction
selected by the `00`, `01`, or remaining kind-code cases, with empty/one-bit cases. -/
theorem gateBit_eq (kind : List Bool → List Bool) (l : ℕ) (b₀ b₁ : List Bool → Bool)
    (z : List Bool) :
    gateBit kind l b₀ b₁ z =
      if kind z = [false, false] then
        if l = 0 then true else if l = 1 then b₀ z else b₀ z && b₁ z
      else if kind z = [false, true] then
        if l = 0 then false else if l = 1 then b₀ z else b₀ z || b₁ z
      else !(if l = 0 then true else if l = 1 then b₀ z else b₀ z && b₁ z) := rfl

/-- The finite gate-output calculation is polynomial-time if the kind word and the two
supplied bits are polynomial-time: `z ↦ [gateBit kind l b₀ b₁ z]`.

**Proof sketch.** Fixed arity makes conjunction and disjunction either constants, the first
bit, or one Boolean operation on the two bits. Compare the kind word with its two constant
codes, and select one of these results or its negation. All word comparisons and Boolean
branches use the existing polynomial-time closure calculus. -/
theorem gateBit_poly {kind : List Bool → List Bool} (hkind : PolyTimeComputable kind)
    (l : ℕ) {b₀ b₁ : List Bool → Bool}
    (h₀ : PolyTimeComputable fun z => [b₀ z])
    (h₁ : PolyTimeComputable fun z => [b₁ z]) :
    PolyTimeComputable fun z => [gateBit kind l b₀ b₁ z] := by
  -- Fixed arity selects the conjunction and disjunction leaf calculations.
  have hAnd : PolyTimeComputable fun z =>
      [if l = 0 then true else if l = 1 then b₀ z else b₀ z && b₁ z] := by
    by_cases hzero : l = 0
    · simpa only [if_pos hzero] using polyTimeComputable_const [true]
    · by_cases hone : l = 1
      · simpa only [if_neg hzero, if_pos hone] using h₀
      · simpa only [if_neg hzero, if_neg hone] using polyTimeComputable_and h₀ h₁
  have hOr : PolyTimeComputable fun z =>
      [if l = 0 then false else if l = 1 then b₀ z else b₀ z || b₁ z] := by
    by_cases hzero : l = 0
    · simpa only [if_pos hzero] using polyTimeComputable_const [false]
    · by_cases hone : l = 1
      · simpa only [if_neg hzero, if_pos hone] using h₀
      · simpa only [if_neg hzero, if_neg hone] using polyTimeComputable_or h₀ h₁
  -- Kind tests are ordinary word equality tests, including on malformed words.
  have hkAnd : PolyTimeComputable fun z => [decide (kind z = [false, false])] := by
    convert polyTimeComputable_pairEq.comp
      (hkind.pairEncode (polyTimeComputable_const [false, false])) using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hkOr : PolyTimeComputable fun z => [decide (kind z = [false, true])] := by
    convert polyTimeComputable_pairEq.comp
      (hkind.pairEncode (polyTimeComputable_const [false, true])) using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h := polyTimeComputable_ite hkAnd hAnd
    (polyTimeComputable_ite hkOr hOr (polyTimeComputable_not hAnd))
  refine h.congr fun z => ?_
  simp only [gateBit_eq, decide_eq_true_eq]
  split_ifs <;> rfl

/-- The addressed key word consists of `width z` coins from
`((bit z).toNat · bound z + vertex z) · width z`, padded with false bits. -/
def keyWord (width bound vertex : List Bool → ℕ) (bit : List Bool → Bool)
    (coins : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.ofFn fun t : Fin (width z) =>
    (coins z).getD (((bit z).toNat * bound z + vertex z) * width z + t) false

/-- `keyWord ... z` is the addressed `List.ofFn` coin window of width `width z`. -/
theorem keyWord_eq (width bound vertex : List Bool → ℕ) (bit : List Bool → Bool)
    (coins : List Bool → List Bool) (z : List Bool) :
    keyWord width bound vertex bit coins z =
      List.ofFn fun t : Fin (width z) =>
        (coins z).getD (((bit z).toNat * bound z + vertex z) * width z + t) false := rfl

/-- The addressed key-word map is polynomial-time from polynomial-time coins, unary
width/bound/vertex maps, and its selection bit. [PS10, Protocol 162.6] -/
theorem keyWord_poly {width bound vertex : List Bool → ℕ} {bit : List Bool → Bool}
    {coins : List Bool → List Bool} (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hvertex : PolyTimeComputable fun z => List.replicate (vertex z) true)
    (hbit : PolyTimeComputable fun z => [bit z]) :
    PolyTimeComputable (keyWord width bound vertex bit coins) :=
  CoinGarbling.keyWord_poly hcoins hwidth hbound hvertex hbit
    (key := fun z t =>
      (coins z).getD (((bit z).toNat * bound z + vertex z) * width z + t) false)
    (fun _ _ => rfl)

/-- The selected row-nonce half is `width z` coins from
`2 · bound z · width z + (4 · gate z + index z) · (2 · width z) + half.toNat · width z`. -/
def nonceWord (width bound gate index : List Bool → ℕ) (coins : List Bool → List Bool)
    (half : Bool) (z : List Bool) : List Bool :=
  List.ofFn fun t : Fin (width z) =>
    (coins z).getD (2 * bound z * width z + (4 * gate z + index z) * (2 * width z) +
      half.toNat * width z + t) false

/-- `nonceWord ... half z` is the addressed `List.ofFn` nonce window of width `width z`. -/
theorem nonceWord_eq (width bound gate index : List Bool → ℕ) (coins : List Bool → List Bool)
    (half : Bool) (z : List Bool) :
    nonceWord width bound gate index coins half z =
      List.ofFn fun t : Fin (width z) =>
        (coins z).getD (2 * bound z * width z + (4 * gate z + index z) * (2 * width z) +
          half.toNat * width z + t) false := rfl

/-- Either addressed row-nonce half is polynomial-time from polynomial-time coins and
unary width/bound/gate/assignment-index maps. [PS10, Protocol 162.6] -/
theorem nonceWord_poly {width bound gate index : List Bool → ℕ}
    {coins : List Bool → List Bool} (half : Bool) (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hindex : PolyTimeComputable fun z => List.replicate (index z) true) :
    PolyTimeComputable (nonceWord width bound gate index coins half) :=
  CoinGarbling.rowCoinWord_poly half hcoins hwidth hbound hgate hindex
    (nonce := fun z t => (coins z).getD
      (2 * bound z * width z + (4 * gate z + index z) * (2 * width z) +
        half.toNat * width z + t) false) (fun _ _ => rfl)

/-- Assemble one garbled row from unary numeric maps, a kind word, encoded unary argument
indices, and a coin word. The fixed assignment is XOR-shifted; its selected argument keys,
output key, and two addressed nonce halves are passed to `nestedWordEnc`.
[PS10, Protocol 162.6; BMR90] -/
def rowWord (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (kind args coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool)
    (z : List Bool) : List Bool :=
  let b₀ := assignmentBit width bound gate coins l a 0
  let b₁ := assignmentBit width bound gate coins l a 1
  let k₀ := keyWord width bound (fun w => (pairFstD (args w)).length) b₀ coins
  let k₁ := keyWord width bound (fun w => (pairFstD (pairSndD (args w))).length) b₁ coins
  let keys := if l = 0 then [] else if l = 1 then pairEncode (k₀ z) []
    else pairEncode (k₀ z) (pairEncode (k₁ z) [])
  let out := keyWord width bound (fun w => inputs w + gate w) (gateBit kind l b₀ b₁) coins
  let index := fun w => (b₀ w).toNat + 2 * (b₁ w).toNat
  Garbling.nestedWordEnc E₁ E₂
    (pairEncode keys (pairEncode (out z)
      (pairEncode (nonceWord width bound gate index coins false z)
        (nonceWord width bound gate index coins true z))))

/-- `rowWord ... z` encrypts its addressed output key under the zero, one, or two addressed
argument keys with the two addressed nonce halves. All addressing is given explicitly
by `keyWord_eq`, `nonceWord_eq`, and `assignmentBit_eq`. -/
theorem rowWord_eq (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (kind args coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWord E₁ E₂ width bound inputs gate kind args coins l a z =
      let b₀ := assignmentBit width bound gate coins l a 0
      let b₁ := assignmentBit width bound gate coins l a 1
      let k₀ := keyWord width bound (fun w => (pairFstD (args w)).length) b₀ coins
      let k₁ := keyWord width bound (fun w => (pairFstD (pairSndD (args w))).length) b₁ coins
      let keys := if l = 0 then [] else if l = 1 then pairEncode (k₀ z) []
        else pairEncode (k₀ z) (pairEncode (k₁ z) [])
      let out := keyWord width bound (fun w => inputs w + gate w) (gateBit kind l b₀ b₁) coins
      let index := fun w => (b₀ w).toNat + 2 * (b₁ w).toNat
      Garbling.nestedWordEnc E₁ E₂
        (pairEncode keys (pairEncode (out z)
          (pairEncode (nonceWord width bound gate index coins false z)
            (nonceWord width bound gate index coins true z)))) := rfl

/-- The complete row machine is polynomial-time on every string when its evaluators, coin
word, kind/argument words, and unary numeric maps are polynomial-time.
[PS10, Protocol 162.6; BMR90]

**Proof sketch.** Read the two shifted assignment bits. The kind code determines the output
bit by a finite Boolean calculation. Read the two argument vertex numbers from the encoded
argument-word list; arithmetic on their unary codes supplies polynomial-time key addresses.
The same arithmetic supplies the output-key address and the two row-nonce addresses. Assemble
the at most two argument keys as an encoded word list, and apply the polynomial-time nested
encryption adapter. Every operation uses total projections or false-padded coin windows. -/
theorem rowWord_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs gate : List Bool → ℕ}
    {kind args coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hkind : PolyTimeComputable kind) (hargs : PolyTimeComputable args)
    (hcoins : PolyTimeComputable coins) (l : ℕ) (a : Fin l → Bool) :
    PolyTimeComputable (rowWord E₁ E₂ width bound inputs gate kind args coins l a) := by
  -- Read the two assignment bits and the key words at their argument positions.
  let b₀ := assignmentBit width bound gate coins l a 0
  let b₁ := assignmentBit width bound gate coins l a 1
  have h₀ : PolyTimeComputable fun z => [b₀ z] :=
    assignmentBit_poly hwidth hbound hgate hcoins l a 0
  have h₁ : PolyTimeComputable fun z => [b₁ z] :=
    assignmentBit_poly hwidth hbound hgate hcoins l a 1
  let k₀ := keyWord width bound (fun w => (pairFstD (args w)).length) b₀ coins
  let k₁ := keyWord width bound (fun w => (pairFstD (pairSndD (args w))).length) b₁ coins
  have hk₀ : PolyTimeComputable k₀ := keyWord_poly hcoins hwidth hbound
    (unaryLength_poly (polyTimeComputable_pairFstD.comp hargs)) h₀
  have hk₁ : PolyTimeComputable k₁ := keyWord_poly hcoins hwidth hbound
    (unaryLength_poly (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp hargs))) h₁
  have hkeys : PolyTimeComputable fun z =>
      if l = 0 then [] else if l = 1 then pairEncode (k₀ z) []
      else pairEncode (k₀ z) (pairEncode (k₁ z) []) := by
    by_cases hzero : l = 0
    · simpa only [if_pos hzero] using polyTimeComputable_const []
    · by_cases hone : l = 1
      · simpa only [if_neg hzero, if_pos hone] using
          hk₀.pairEncode (polyTimeComputable_const [])
      · simpa only [if_neg hzero, if_neg hone] using
          hk₀.pairEncode (hk₁.pairEncode (polyTimeComputable_const []))
  -- The plaintext and both nonce halves use polynomial-time numeric addresses.
  have hout := keyWord_poly hcoins hwidth hbound (unaryAdd_poly hinputs hgate)
    (gateBit_poly hkind l h₀ h₁)
  have hindex := CoinGarbling.assignmentIndex_poly h₀ h₁
  have hr₀ := nonceWord_poly false hcoins hwidth hbound hgate hindex
  have hr₁ := nonceWord_poly true hcoins hwidth hbound hgate hindex
  exact (Garbling.nestedWordEnc_poly hE₁ hE₂).comp
    (hkeys.pairEncode (hout.pairEncode (hr₀.pairEncode hr₁)))

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins
