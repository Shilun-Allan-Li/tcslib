/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinGarbling
import TCSlib.Complexity.ClassP.BinaryArith.Loops

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

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

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

/-- Assemble one garbled row from unary numeric maps, an output-bit map, encoded unary argument
indices, and a coin word. The fixed assignment is XOR-shifted; its selected argument keys,
output key for the supplied bit, and two addressed nonce halves are passed to `nestedWordEnc`.
[PS10, Protocol 162.6; BMR90] -/
def rowWordWith (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (args coins : List Bool → List Bool) (outputBit : List Bool → Bool) (l : ℕ) (a : Fin l → Bool)
    (z : List Bool) : List Bool :=
  let b₀ := assignmentBit width bound gate coins l a 0
  let b₁ := assignmentBit width bound gate coins l a 1
  let k₀ := keyWord width bound
    (fun w => (BinArith.getW (pairEncode [] (args w))).length) b₀ coins
  let k₁ := keyWord width bound
    (fun w => (BinArith.getW (pairEncode [true] (args w))).length) b₁ coins
  let keys := if l = 0 then [] else if l = 1 then pairEncode (k₀ z) []
    else pairEncode (k₀ z) (pairEncode (k₁ z) [])
  let out := keyWord width bound (fun w => inputs w + gate w) outputBit coins
  let index := fun w => (b₀ w).toNat + 2 * (b₁ w).toNat
  Garbling.nestedWordEnc E₁ E₂
    (pairEncode keys (pairEncode (out z)
      (pairEncode (nonceWord width bound gate index coins false z)
        (nonceWord width bound gate index coins true z))))

/-- `rowWordWith ... z` encrypts its addressed output key under the zero, one, or two addressed
argument keys with the two addressed nonce halves. All addressing is given explicitly
by `keyWord_eq`, `nonceWord_eq`, and `assignmentBit_eq`. -/
theorem rowWordWith_eq (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (args coins : List Bool → List Bool) (outputBit : List Bool → Bool)
    (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWordWith E₁ E₂ width bound inputs gate args coins outputBit l a z =
      let b₀ := assignmentBit width bound gate coins l a 0
      let b₁ := assignmentBit width bound gate coins l a 1
      let k₀ := keyWord width bound
        (fun w => (BinArith.getW (pairEncode [] (args w))).length) b₀ coins
      let k₁ := keyWord width bound
        (fun w => (BinArith.getW (pairEncode [true] (args w))).length) b₁ coins
      let keys := if l = 0 then [] else if l = 1 then pairEncode (k₀ z) []
        else pairEncode (k₀ z) (pairEncode (k₁ z) [])
      let out := keyWord width bound (fun w => inputs w + gate w) outputBit coins
      let index := fun w => (b₀ w).toNat + 2 * (b₁ w).toNat
      Garbling.nestedWordEnc E₁ E₂
        (pairEncode keys (pairEncode (out z)
          (pairEncode (nonceWord width bound gate index coins false z)
            (nonceWord width bound gate index coins true z)))) := rfl

/-- Assemble one garbled row from unary numeric maps, a kind word, encoded unary argument
indices, and a coin word. The fixed assignment is XOR-shifted; its selected argument keys,
output key, and two addressed nonce halves are passed to `nestedWordEnc`.
[PS10, Protocol 162.6; BMR90] -/
def rowWord (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (kind args coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool)
    (z : List Bool) : List Bool :=
  rowWordWith E₁ E₂ width bound inputs gate args coins
    (gateBit kind l (assignmentBit width bound gate coins l a 0)
      (assignmentBit width bound gate coins l a 1)) l a z

/-- `rowWord ... z` encrypts its addressed output key under the zero, one, or two addressed
argument keys with the two addressed nonce halves. All addressing is given explicitly
by `keyWord_eq`, `nonceWord_eq`, and `assignmentBit_eq`. -/
theorem rowWord_eq (E₁ E₂ : List Bool → List Bool) (width bound inputs gate : List Bool → ℕ)
    (kind args coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWord E₁ E₂ width bound inputs gate kind args coins l a z =
      let b₀ := assignmentBit width bound gate coins l a 0
      let b₁ := assignmentBit width bound gate coins l a 1
      let k₀ := keyWord width bound
        (fun w => (BinArith.getW (pairEncode [] (args w))).length) b₀ coins
      let k₁ := keyWord width bound
        (fun w => (BinArith.getW (pairEncode [true] (args w))).length) b₁ coins
      let keys := if l = 0 then [] else if l = 1 then pairEncode (k₀ z) []
        else pairEncode (k₀ z) (pairEncode (k₁ z) [])
      let out := keyWord width bound (fun w => inputs w + gate w) (gateBit kind l b₀ b₁) coins
      let index := fun w => (b₀ w).toNat + 2 * (b₁ w).toNat
      Garbling.nestedWordEnc E₁ E₂
        (pairEncode keys (pairEncode (out z)
          (pairEncode (nonceWord width bound gate index coins false z)
            (nonceWord width bound gate index coins true z)))) := rfl

/-- The complete row machine is polynomial-time on every string when its evaluators, coin
word, output-bit map, argument word, and unary numeric maps are polynomial-time.
[PS10, Protocol 162.6; BMR90]

**Proof sketch.** Read the two shifted assignment bits. The output-key bit is supplied as a
polynomial-time parameter. Read the two argument vertex numbers from the encoded
argument-word list; arithmetic on their unary codes supplies polynomial-time key addresses.
The same arithmetic supplies the output-key address and the two row-nonce addresses. Assemble
the at most two argument keys as an encoded word list, and apply the polynomial-time nested
encryption adapter. Every operation uses total projections or false-padded coin windows. -/
theorem rowWordWith_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs gate : List Bool → ℕ}
    {args coins : List Bool → List Bool} {outputBit : List Bool → Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hargs : PolyTimeComputable args) (hcoins : PolyTimeComputable coins)
    (houtputBit : PolyTimeComputable fun z => [outputBit z]) (l : ℕ) (a : Fin l → Bool) :
    PolyTimeComputable (rowWordWith E₁ E₂ width bound inputs gate args coins outputBit l a) := by
  -- Read the two assignment bits and the key words at their argument positions.
  let b₀ := assignmentBit width bound gate coins l a 0
  let b₁ := assignmentBit width bound gate coins l a 1
  have h₀ : PolyTimeComputable fun z => [b₀ z] :=
    assignmentBit_poly hwidth hbound hgate hcoins l a 0
  have h₁ : PolyTimeComputable fun z => [b₁ z] :=
    assignmentBit_poly hwidth hbound hgate hcoins l a 1
  let k₀ := keyWord width bound
    (fun w => (BinArith.getW (pairEncode [] (args w))).length) b₀ coins
  let k₁ := keyWord width bound
    (fun w => (BinArith.getW (pairEncode [true] (args w))).length) b₁ coins
  have hk₀ : PolyTimeComputable k₀ := keyWord_poly hcoins hwidth hbound
    (unaryLength_poly (BinArith.polyTimeComputable_getW.comp
      ((polyTimeComputable_const []).pairEncode hargs))) h₀
  have hk₁ : PolyTimeComputable k₁ := keyWord_poly hcoins hwidth hbound
    (unaryLength_poly (BinArith.polyTimeComputable_getW.comp
      ((polyTimeComputable_const [true]).pairEncode hargs))) h₁
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
    houtputBit
  have hindex := CoinGarbling.assignmentIndex_poly h₀ h₁
  have hr₀ := nonceWord_poly false hcoins hwidth hbound hgate hindex
  have hr₁ := nonceWord_poly true hcoins hwidth hbound hgate hindex
  exact (Garbling.nestedWordEnc_poly hE₁ hE₂).comp
    (hkeys.pairEncode (hout.pairEncode (hr₀.pairEncode hr₁)))


/-- The real row machine is polynomial-time on every string when its evaluators, coin
word, kind/argument words, and unary numeric maps are polynomial-time.
[PS10, Protocol 162.6; BMR90]

**Proof sketch.** Apply the shared `rowWordWith_poly` core, using `gateBit_poly` on the
two polynomial-time shifted assignment bits as its output-key selection bit. -/
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
  exact rowWordWith_poly hE₁ hE₂ hwidth hbound hinputs hgate hargs hcoins
    (gateBit_poly hkind l (assignmentBit_poly hwidth hbound hgate hcoins l a 0)
      (assignmentBit_poly hwidth hbound hgate hcoins l a 1)) l a

/-- If the supplied row permutation satisfies the pointwise XOR-shift equation, the raw
assignment-bit reader is exactly its output word's `j`-th bit, with false defaults. [BMR90] -/
theorem assignmentBit_of_perm (width bound gate : List Bool → ℕ)
    (coins : List Bool → List Bool) (l : ℕ) (a : Fin l → Bool)
    (p : Equiv.Perm (Fin l → Bool)) (z : List Bool) (j : ℕ)
    (hp : ∀ t, p a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * gate z + t) false)) :
    assignmentBit width bound gate coins l a j z = (List.ofFn (p a)).getD j false := by
  by_cases h : j < l
  · rw [assignmentBit_eq, if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h, Option.getD_some]
    exact (hp ⟨j, h⟩).symm
  · simp only [assignmentBit_eq, if_neg h, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, dif_neg h, Option.getD_none]


/-- On a genuine gate-kind code and assignment-word bits, the raw finite calculation is
`gateOut g a` for every gate with at most two arguments. [PS10, Protocol 162.6] -/
theorem gateBit_eq_gateOut (g : DAGGate) (a : Fin g.args.length → Bool)
    (kind : List Bool → List Bool) (b₀ b₁ : List Bool → Bool) (z : List Bool)
    (hfan : g.args.length ≤ 2) (hkind : kind z = g.kind.encode)
    (h₀ : b₀ z = (List.ofFn a).getD 0 false)
    (h₁ : b₁ z = (List.ofFn a).getD 1 false) :
    gateBit kind g.args.length b₀ b₁ z = gateOut g a := by
  rw [gateBit_eq, hkind, h₀, h₁, Garbling.gateOut_small g a hfan]
  cases g.kind <;> simp [GateKind.encode_and, GateKind.encode_or, GateKind.encode_not]


/-- For at most two positions, the assignment's binary fold is its first bit plus twice
its second bit, with false defaults for absent positions. [PS10, Protocol 162.6] -/
theorem assignmentFold_eq_two {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 =
      ((List.ofFn a).getD 0 false).toNat + 2 * ((List.ofFn a).getD 1 false).toNat := by
  have hc : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> simp [List.ofFn_succ]


/-- The generic raw row encrypts the output key selected by `outputBit z` under the
permuted assignment's argument keys, with the supplied seed's row coins. The output bit
is independent of the gate truth function. [PS10, Theorem 163.7; Protocol 162.6]

**Proof sketch.** Read the two shifted assignment bits through the permutation equation.
Canonical argument-word lookup gives the two argument vertices. Circuit acyclicity and the
published size equation put every addressed argument and output key in the seed's range.
The seed key equation identifies each key window, including the arbitrary output-bit key.
The bounded-arity assignment fold identifies the nonce address, and both seed nonce equations
identify its two halves. Finally the generic nested word-encryption contract turns these
encoded vectors into the multi-key encryption of the requested output key. -/
theorem rowWordWith_enc (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (args coins : List Bool → List Bool)
    (outputBit : List Bool → Bool)
    (z : List Bool) (C : DAGCircuit (inputs z))
    (s : GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (hfan : (C.gates[i]).args.length ≤ 2) (hgate : gate z = i)
    (hargs : args z = BinArith.encWords ((C.gates[i]).args.map fun v => List.replicate v true))
    (hkey : ∀ (v : ℕ), v < C.size → ∀ b,
      keyAt C s v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ a t, (s.2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * gate z + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ a t, (s.2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * gate z + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ a t, s.2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * gate z + t) false)) :
    rowWordWith E₁ E₂ width bound inputs gate args coins outputBit
        (C.gates[i]).args.length a z =
      (nestedSpecial E₁ E₂ (width z)).enc (argKeys C s i (s.2.2 i a))
        (keyAt C s (inputs z + i) (outputBit z)) (s.2.1 i (s.2.2 i a)) := by
  let b₀ := assignmentBit width bound gate coins (C.gates[i]).args.length a 0
  let b₁ := assignmentBit width bound gate coins (C.gates[i]).args.length a 1
  let a' := s.2.2 i a
  have hb₀ : b₀ z = (List.ofFn a').getD 0 false :=
    assignmentBit_of_perm width bound gate coins _ a (s.2.2 i) z 0 (hperm a)
  have hb₁ : b₁ z = (List.ofFn a').getD 1 false :=
    assignmentBit_of_perm width bound gate coins _ a (s.2.2 i) z 1 (hperm a)
  -- Canonical lookup reads argument numbers, including its zero default.
  have hlookup (j : ℕ) :
      (BinArith.getW (pairEncode (List.replicate j true) (args z))).length =
        (C.gates[i]).args.getD j 0 := by
    rw [hargs, BinArith.getW_pairEncode, List.length_replicate]
    change (((C.gates[i]).args.map (fun v => List.replicate v true)).getD j
      (List.replicate 0 true)).length = (C.gates[i]).args.getD j 0
    rw [List.getD_map, List.length_replicate]
  have hlookup₀ : (BinArith.getW (pairEncode [] (args z))).length =
      (C.gates[i]).args.getD 0 0 := by simpa using hlookup 0
  have hlookup₁ : (BinArith.getW (pairEncode [true] (args z))).length =
      (C.gates[i]).args.getD 1 0 := by simpa using hlookup 1
  have houtlt : inputs z + i < C.size := by
    rw [DAGCircuit.size_eq]
    exact Nat.add_lt_add_left i.isLt _
  have hwire (j : ℕ) : (C.gates[i]).args.getD j 0 < C.size := by
    by_cases hj : j < (C.gates[i]).args.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact (C.args_lt i i.isLt _ (List.getElem_mem hj)).trans houtlt
    · rw [List.getD_eq_default _ _ (by omega), DAGCircuit.size_eq]
      exact (Nat.zero_le C.output).trans_lt C.output_lt
  have hkeyWord (vertex : List Bool → ℕ) (bit : List Bool → Bool)
      (hv : vertex z < C.size) :
      keyWord width bound vertex bit coins z = List.ofFn (keyAt C s (vertex z) (bit z)) := by
    rw [keyWord_eq]
    exact congrArg List.ofFn (hkey (vertex z) hv (bit z)).symm
  have hk₀ : keyWord width bound
      (fun w => (BinArith.getW (pairEncode [] (args w))).length) b₀ coins z =
        List.ofFn (keyAt C s ((C.gates[i]).args.getD 0 0) ((List.ofFn a').getD 0 false)) := by
    rw [hkeyWord _ _ (by rw [hlookup₀]; exact hwire 0), hlookup₀, hb₀]
  have hk₁ : keyWord width bound
      (fun w => (BinArith.getW (pairEncode [true] (args w))).length) b₁ coins z =
        List.ofFn (keyAt C s ((C.gates[i]).args.getD 1 0) ((List.ofFn a').getD 1 false)) := by
    rw [hkeyWord _ _ (by rw [hlookup₁]; exact hwire 1), hlookup₁, hb₁]
  have hkeys :
      (if (C.gates[i]).args.length = 0 then []
       else if (C.gates[i]).args.length = 1 then pairEncode
         (keyWord width bound (fun w =>
           (BinArith.getW (pairEncode [] (args w))).length) b₀ coins z) []
       else pairEncode
         (keyWord width bound (fun w =>
           (BinArith.getW (pairEncode [] (args w))).length) b₀ coins z)
         (pairEncode (keyWord width bound (fun w =>
           (BinArith.getW (pairEncode [true] (args w))).length) b₁ coins z) [])) =
        BinArith.encWords ((argKeys C s i a').map List.ofFn) := by
    rw [hk₀, hk₁, Garbling.argKeys_small C s i a' hfan]
  have hout : keyWord width bound (fun w => inputs w + gate w)
      outputBit coins z =
        List.ofFn (keyAt C s (inputs z + i) (outputBit z)) := by
    rw [hkeyWord _ _ (by simpa only [hgate] using houtlt), hgate]
  -- The assignment fold gives the exact address of both nonce halves.
  let index := fun w => (b₀ w).toNat + 2 * (b₁ w).toNat
  have hindex : index z = (List.ofFn a').foldr (fun b k => b.toNat + 2 * k) 0 := by
    dsimp only [index]
    rw [hb₀, hb₁, assignmentFold_eq_two a' hfan]
  have hrzero : nonceWord width bound gate index coins false z = List.ofFn (s.2.1 i a').1 := by
    rw [nonceWord_eq, hindex]
    simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
    apply congrArg List.ofFn
    funext t
    exact (hr₀ a' t).symm
  have hrone : nonceWord width bound gate index coins true z = List.ofFn (s.2.1 i a').2 := by
    rw [nonceWord_eq, hindex]
    simp only [Bool.toNat_true, Nat.one_mul]
    apply congrArg List.ofFn
    funext t
    exact (hr₁ a' t).symm
  rw [rowWordWith_eq]
  dsimp only
  rw [hkeys, hout, hrzero, hrone]
  apply Garbling.nestedWordEnc_vectors
  rw [argKeys_eq, List.length_ofFn]
  exact hfan


/-- The raw row machine equals the garbled row selected by a supplied XOR row permutation,
when the gate-description fields and the key/nonce block equations hold.
The contract is generic in the circuit and seed. [PS10, Protocol 162.6; BMR90]

**Proof sketch.** The permutation equation identifies the two raw assignment bits with the
first two bits of the permuted assignment. The kind-code equation then identifies the raw
output bit with the gate truth function. Apply the arbitrary-output-bit row contract, which
already identifies every key and nonce window, and read the public garbled-row equation. -/
theorem rowWord_garbledRow (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (z : List Bool) (C : DAGCircuit (inputs z))
    (s : GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (hfan : (C.gates[i]).args.length ≤ 2) (hgate : gate z = i)
    (hkind : kind z = (C.gates[i]).kind.encode)
    (hargs : args z = BinArith.encWords ((C.gates[i]).args.map fun v => List.replicate v true))
    (hkey : ∀ (v : ℕ), v < C.size → ∀ b,
      keyAt C s v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ a t, (s.2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * gate z + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ a t, (s.2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * gate z + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ a t, s.2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * gate z + t) false)) :
    rowWord E₁ E₂ width bound inputs gate kind args coins (C.gates[i]).args.length a z =
      garbledRow (nestedSpecial E₁ E₂ (width z)) C s i (s.2.2 i a) := by
  let b₀ := assignmentBit width bound gate coins (C.gates[i]).args.length a 0
  let b₁ := assignmentBit width bound gate coins (C.gates[i]).args.length a 1
  let a' := s.2.2 i a
  have hb₀ : b₀ z = (List.ofFn a').getD 0 false :=
    assignmentBit_of_perm width bound gate coins _ a (s.2.2 i) z 0 (hperm a)
  have hb₁ : b₁ z = (List.ofFn a').getD 1 false :=
    assignmentBit_of_perm width bound gate coins _ a (s.2.2 i) z 1 (hperm a)
  have houtput := gateBit_eq_gateOut (C.gates[i]) a' kind b₀ b₁ z hfan hkind hb₀ hb₁
  change rowWordWith E₁ E₂ width bound inputs gate args coins
    (gateBit kind (C.gates[i]).args.length b₀ b₁) (C.gates[i]).args.length a z = _
  rw [rowWordWith_enc E₁ E₂ width bound inputs gate args coins
    (gateBit kind (C.gates[i]).args.length b₀ b₁) z C s i a hfan hgate hargs
    hkey hr₀ hr₁ hperm]
  rw [houtput, garbledRow_eq]


/-- A generic raw row depends only on the data maps and output bit at its input:
freezing every map to its value at `z` and running at `[]` gives the same encrypted row. -/
theorem rowWordWith_value (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (args coins : List Bool → List Bool)
    (outputBit : List Bool → Bool) (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWordWith E₁ E₂ width bound inputs gate args coins outputBit l a z =
      rowWordWith E₁ E₂ (fun _ => width z) (fun _ => bound z)
        (fun _ => inputs z) (fun _ => gate z) (fun _ => args z) (fun _ => coins z)
        (fun _ => outputBit z) l a [] := by
  rw [rowWordWith_eq, rowWordWith_eq]
  simp only [keyWord_eq, nonceWord_eq, assignmentBit_eq]

/-- A raw row depends only on the supplied data maps' values at its input:
freezing each map to its value at `z` and running at `[]` gives the same row.
This exposes pointwise field normalization without reducing any foreign implementation. -/
theorem rowWord_value (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (l : ℕ) (a : Fin l → Bool) (z : List Bool) :
    rowWord E₁ E₂ width bound inputs gate kind args coins l a z =
      rowWord E₁ E₂ (fun _ => width z) (fun _ => bound z)
        (fun _ => inputs z) (fun _ => gate z) (fun _ => kind z)
        (fun _ => args z) (fun _ => coins z) l a [] := by
  rw [rowWord_eq, rowWord_eq]
  simp only [keyWord_eq, nonceWord_eq, assignmentBit_eq, gateBit_eq]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.RowFromCoins
