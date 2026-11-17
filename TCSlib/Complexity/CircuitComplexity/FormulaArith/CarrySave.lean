/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.CircuitComplexity.Adder
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators

/-!
# Formula arithmetic: carry-save addition

Numbers as little-endian lists of `BoolCircuit.TreeCircuit` formulas, and the carry-save (3:2)
reduction of many such numbers to two.  A list `U` denotes, under the assignment `x`, the number
`FormulaArith.val x U = bitsVal (U.map (·.eval x))` (`Adder.lean`'s `bitsVal`).  One carry-save
step turns three numbers `A, B, C` into two, the bitwise sum `S` (`xor3`) and the shifted
carries `K` (`maj3`), with `val A + val B + val C = val S + val K` at a cost of four levels of
depth and none in the bit length.  Applying a layer of steps to the triples of a list of `k`
numbers, `csaLevels k ≤ 2⌈log₂ k⌉` times, leaves two numbers with the same total.  This is the
summation step of the decryption formula ([BV11, Lemma 4.5 proof]; r3 §H3.3–H3.4): its depth is
logarithmic in the number of summands and does not depend on their bit length.

## Main definitions

* `BoolCircuit.FormulaArith.val` — the number a list of formulas denotes.
* `BoolCircuit.FormulaArith.csaStep` — one 3:2 step `(A, B, C) ↦ (S, K)`.
* `BoolCircuit.FormulaArith.csaLayer` — one layer of steps over a list of numbers.
* `BoolCircuit.FormulaArith.csaLevels` — the number of layers needed to reach two numbers.
* `BoolCircuit.FormulaArith.csaReduce` — the reduction of a list of numbers to two.

## Main results

* `BoolCircuit.FormulaArith.csaStep_val`, `depth_csaStep_le`, `maxFaninL_csaStep_le` — F5:
  the value equation, depth `+4`, fan-in two (targets).
* `BoolCircuit.FormulaArith.csaReduce_val`, `depth_csaReduce_le`, `maxFaninL_csaReduce_le`,
  `csaLevels_le` — F6: the total is kept, depth `4 · csaLevels k` over the inputs (at least
  `1`), and `csaLevels k ≤ 2⌈log₂ k⌉` (targets).

## References

* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011, pp. 97–106; full version, IACR ePrint 2011/344 (39 pages,
  2 March 2012), §4.5, Lemma 4.5 and its proof.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

namespace FormulaArith

variable {n : ℕ}

/-! ### Numbers denoted by lists of formulas -/

/-- The number denoted by a little-endian list of formulas under the assignment `x`: formula
`j` is bit `j`, of weight `2 ^ j`, `val x U = bitsVal (U.map (·.eval x))` (`Adder.lean`).
Glue. -/
def val (x : Fin n → Bool) (U : List (TreeCircuit n)) : ℕ :=
  bitsVal (U.map fun c => c.eval x)

/-- The value of a list of formulas is `bitsVal` of their values:
`val x U = bitsVal (U.map fun c => c.eval x)`. -/
theorem val_eq (x : Fin n → Bool) (U : List (TreeCircuit n)) :
    val x U = bitsVal (U.map fun c => c.eval x) := rfl

/-! ### One carry-save step (F5) -/

/-- One carry-save (3:2) step on three little-endian numbers: with `L` the longest length and
every number padded by `const false` to `L` bits, the sum word is the bitwise `xor3`,
`S_i = xor3 A_i B_i C_i` (`i < L`), and the carry word is the bitwise `maj3` shifted up by one,
`K = const false :: [maj3 A_i B_i C_i | i < L]`; so `|S| = L` and `|K| = L + 1`.
`csaStep A B C = (S, K)` with `val A + val B + val C = val S + val K` (`csaStep_val`).
[BV11, Lemma 4.5 proof, p029-b002]; the carry-save step is the deviation of r3 §H3.4. -/
def csaStep (A B C : List (TreeCircuit n)) : List (TreeCircuit n) × List (TreeCircuit n) :=
  ((List.range (max A.length (max B.length C.length))).map fun i =>
      TreeCircuit.xor3 (A.getD i (TreeCircuit.const false)) (B.getD i (TreeCircuit.const false))
        (C.getD i (TreeCircuit.const false)),
    TreeCircuit.const false ::
      (List.range (max A.length (max B.length C.length))).map fun i =>
        TreeCircuit.maj3 (A.getD i (TreeCircuit.const false))
          (B.getD i (TreeCircuit.const false)) (C.getD i (TreeCircuit.const false)))

/-- The carry-save step, written out: with `L = max |A| (max |B| |C|)` and `z = const false`,
`csaStep A B C = ((range L).map fun i => xor3 (A.getD i z) (B.getD i z) (C.getD i z),
z :: (range L).map fun i => maj3 (A.getD i z) (B.getD i z) (C.getD i z))`. -/
theorem csaStep_eq (A B C : List (TreeCircuit n)) :
    csaStep A B C =
      ((List.range (max A.length (max B.length C.length))).map fun i =>
          TreeCircuit.xor3 (A.getD i (TreeCircuit.const false))
            (B.getD i (TreeCircuit.const false)) (C.getD i (TreeCircuit.const false)),
        TreeCircuit.const false ::
          (List.range (max A.length (max B.length C.length))).map fun i =>
            TreeCircuit.maj3 (A.getD i (TreeCircuit.const false))
              (B.getD i (TreeCircuit.const false)) (C.getD i (TreeCircuit.const false))) :=
  rfl

/-- **F5, value.** One carry-save step keeps the total: for every assignment `x`,
`val x A + val x B + val x C = val x (csaStep A B C).1 + val x (csaStep A B C).2`.
[BV11, Lemma 4.5 proof, p029-b002: "The summation (over the integers) can be done in depth
O(log k + log log p)"].  *Deviation:* the paper does not say how; r3 §H3.4 fixes the carry-save
(3:2) tree, of which this is one step.

**Proof sketch.** Write every value through `val_eq` and `bitsVal_eq_prefixVal` as a
`prefixVal` of its bit sequence, extended to `L + 1` bits by `false` (`prefixVal_congr`; the
padding `const false` evaluates to `false` by `const_eval`).  Bit by bit, the full-adder
identity `a + b + c = (a ⊕ b ⊕ c) + 2 · maj(a, b, c)` holds by cases on three Booleans, with
`xor3_eval` and `maj3_eval` giving the values of `S_i` and `K_{i+1}`; summing it with weights
`2 ^ i` (induction on the number of bits, `prefixVal_succ`) gives the equation. -/
theorem csaStep_val (x : Fin n → Bool) (A B C : List (TreeCircuit n)) :
    val x A + val x B + val x C = val x (csaStep A B C).1 + val x (csaStep A B C).2 := by
  sorry

/-- **F5, depth `+4`.** Both output words of a carry-save step lie at most four levels above
the inputs (counted from at least `1`, the depth of the padding constants):
`TreeCircuit.maxDepth ((csaStep A B C).1 ++ (csaStep A B C).2) ≤
max 1 (TreeCircuit.maxDepth (A ++ B ++ C)) + 4`.  [BV11, Lemma 4.5 proof, p029-b002];
r3's `+4` *(fix)*, settled: `xor3` is `+4`, `maj3` is `+3`, the constant `const false` has
depth `1`.  No term depends on the bit length.

**Proof sketch.** `csaStep_eq`.  Each padded input bit `A.getD i (const false)` has depth at
most `max 1 (maxDepth (A ++ B ++ C))` (`depth_le_maxDepth` for a member, `depth_const` for the
padding).  Then `depth_xor3_le` bounds every `S_i` by that plus `4`, `depth_maj3_le` every
`K_{i+1}` by that plus `3`, and `depth_const` gives `K_0` depth `1`; a list induction with
`maxDepth_cons`/`maxDepth_nil` (and `maxDepth` of an append) bounds the maximum. -/
theorem depth_csaStep_le (A B C : List (TreeCircuit n)) :
    TreeCircuit.maxDepth ((csaStep A B C).1 ++ (csaStep A B C).2) ≤
      max 1 (TreeCircuit.maxDepth (A ++ B ++ C)) + 4 := by
  sorry

/-- **F5, fan-in two.** A carry-save step adds only fan-in-2 gates:
`TreeCircuit.maxFaninL ((csaStep A B C).1 ++ (csaStep A B C).2) ≤
max 2 (TreeCircuit.maxFaninL (A ++ B ++ C))`.  Glue.

**Proof sketch.** `csaStep_eq`; each padded input bit has fan-in at most
`maxFaninL (A ++ B ++ C)` (`maxFanin_le_maxFaninL`, `maxFanin_const`), and
`maxFanin_xor3_le`, `maxFanin_maj3_le` bound every output bit; a list induction with
`maxFaninL_cons`/`maxFaninL_nil` bounds the maximum. -/
theorem maxFaninL_csaStep_le (A B C : List (TreeCircuit n)) :
    TreeCircuit.maxFaninL ((csaStep A B C).1 ++ (csaStep A B C).2) ≤
      max 2 (TreeCircuit.maxFaninL (A ++ B ++ C)) := by
  sorry

/-! ### Reduction to two numbers (F6) -/

/-- One carry-save layer over a list of numbers: every consecutive triple `A, B, C` is replaced
by the two words of `csaStep A B C`, and a remainder of one or two numbers is kept,
`csaLayer (A :: B :: C :: Us) = (csaStep A B C).1 :: (csaStep A B C).2 :: csaLayer Us` and
`csaLayer Us = Us` for `|Us| ≤ 2`.  It sends `k` numbers to `2 ⌊k / 3⌋ + k % 3`.  Glue. -/
def csaLayer : List (List (TreeCircuit n)) → List (List (TreeCircuit n))
  | A :: B :: C :: Us => (csaStep A B C).1 :: (csaStep A B C).2 :: csaLayer Us
  | Us => Us

/-- A carry-save layer replaces the first triple by its two words:
`csaLayer (A :: B :: C :: Us) = (csaStep A B C).1 :: (csaStep A B C).2 :: csaLayer Us`. -/
theorem csaLayer_cons_cons_cons (A B C : List (TreeCircuit n))
    (Us : List (List (TreeCircuit n))) :
    csaLayer (A :: B :: C :: Us) = (csaStep A B C).1 :: (csaStep A B C).2 :: csaLayer Us := rfl

/-- A carry-save layer keeps a list of at most two numbers:
`Us.length ≤ 2 → csaLayer Us = Us`. -/
theorem csaLayer_of_length_le_two {Us : List (List (TreeCircuit n))} (h : Us.length ≤ 2) :
    csaLayer Us = Us := by
  match Us, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | _ :: _ :: _ :: _, h => simp only [List.length_cons] at h; omega

/-- The number of carry-save layers with fuel `f`: zero once at most two numbers are left,
`csaLevelsAux (f + 1) k = if k ≤ 2 then 0 else csaLevelsAux f (2 * (k / 3) + k % 3) + 1`. -/
private def csaLevelsAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, k => if k ≤ 2 then 0 else csaLevelsAux f (2 * (k / 3) + k % 3) + 1

/-- The fuel does not matter once it is at least the count. -/
private theorem csaLevelsAux_fuel :
    ∀ f g k : ℕ, k ≤ f → k ≤ g → csaLevelsAux f k = csaLevelsAux g k
  | 0, 0, _, _, _ => rfl
  | 0, g + 1, k, hf, _ => by
      obtain rfl : k = 0 := by omega
      show 0 = if 0 ≤ 2 then 0 else csaLevelsAux g (2 * (0 / 3) + 0 % 3) + 1
      rw [if_pos (by omega)]
  | f + 1, 0, k, _, hg => by
      obtain rfl : k = 0 := by omega
      show (if 0 ≤ 2 then 0 else csaLevelsAux f (2 * (0 / 3) + 0 % 3) + 1) = 0
      rw [if_pos (by omega)]
  | f + 1, g + 1, k, hf, hg => by
      show (if k ≤ 2 then 0 else csaLevelsAux f (2 * (k / 3) + k % 3) + 1) =
        (if k ≤ 2 then 0 else csaLevelsAux g (2 * (k / 3) + k % 3) + 1)
      by_cases hk : k ≤ 2
      · rw [if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk,
          csaLevelsAux_fuel f g (2 * (k / 3) + k % 3) (by omega) (by omega)]

/-- The number of carry-save layers that reduce `k` numbers to at most two: `0` for `k ≤ 2`,
and `csaLevels (2 * (k / 3) + k % 3) + 1` for `k > 2` (`csaLevels_of_le_two`,
`csaLevels_of_two_lt`).  Computed with fuel `k`, by structural recursion.  Glue. -/
def csaLevels (k : ℕ) : ℕ :=
  csaLevelsAux k k

/-- No carry-save layer is needed for at most two numbers: `k ≤ 2 → csaLevels k = 0`. -/
theorem csaLevels_of_le_two {k : ℕ} (h : k ≤ 2) : csaLevels k = 0 := by
  match k, h with
  | 0, _ => rfl
  | f + 1, h =>
      show (if f + 1 ≤ 2 then 0 else csaLevelsAux f (2 * ((f + 1) / 3) + (f + 1) % 3) + 1) = 0
      rw [if_pos h]

/-- More than two numbers need one layer more than their image under a layer:
`2 < k → csaLevels k = csaLevels (2 * (k / 3) + k % 3) + 1`. -/
theorem csaLevels_of_two_lt {k : ℕ} (h : 2 < k) :
    csaLevels k = csaLevels (2 * (k / 3) + k % 3) + 1 := by
  match k, h with
  | f + 1, h =>
      show (if f + 1 ≤ 2 then 0 else csaLevelsAux f (2 * ((f + 1) / 3) + (f + 1) % 3) + 1) =
        csaLevelsAux (2 * ((f + 1) / 3) + (f + 1) % 3) (2 * ((f + 1) / 3) + (f + 1) % 3) + 1
      rw [if_neg (by omega), csaLevelsAux_fuel f _ _ (by omega) le_rfl]

/-- The carry-save reduction of a list of numbers to two: apply `csaLayer`
`csaLevels |Us|` times and read the (at most two) numbers left, padding with `[]`,
`csaReduce Us = (Vs.getD 0 [], Vs.getD 1 [])` with `Vs = Nat.repeat csaLayer (csaLevels |Us|) Us`.
`val (csaReduce Us).1 + val (csaReduce Us).2 = Σ val Us` (`csaReduce_val`).
[BV11, Lemma 4.5 proof, p029-b002]; the carry-save tree is r3 §H3.4's deviation. -/
def csaReduce (Us : List (List (TreeCircuit n))) : List (TreeCircuit n) × List (TreeCircuit n) :=
  ((Nat.repeat csaLayer (csaLevels Us.length) Us).getD 0 [],
    (Nat.repeat csaLayer (csaLevels Us.length) Us).getD 1 [])

/-- The reduction reads the first two numbers after `csaLevels |Us|` layers:
`csaReduce Us = (Vs.getD 0 [], Vs.getD 1 [])` with
`Vs = Nat.repeat csaLayer (csaLevels Us.length) Us`. -/
theorem csaReduce_eq (Us : List (List (TreeCircuit n))) :
    csaReduce Us =
      ((Nat.repeat csaLayer (csaLevels Us.length) Us).getD 0 [],
        (Nat.repeat csaLayer (csaLevels Us.length) Us).getD 1 []) := rfl

/-- **F6, value.** The reduction keeps the total: for every assignment `x`,
`val x (csaReduce Us).1 + val x (csaReduce Us).2 = (Us.map (val x)).sum`.
[BV11, Lemma 4.5 proof, p029-b002]; *deviation:* the carry-save tree (r3 §H3.4).

**Proof sketch.** (1) One layer keeps the total, `((csaLayer Us).map (val x)).sum =
(Us.map (val x)).sum`: induction along `csaLayer`'s cases (`csaLayer_cons_cons_cons`,
`csaLayer_of_length_le_two`) with `csaStep_val` for each triple.  (2) One layer sends length
`k` to `2 (k / 3) + k % 3` (same induction, `List.length_cons`).  (3) Induction on `k` along
`csaLevels_of_le_two`/`csaLevels_of_two_lt`: after `csaLevels k` layers at most two numbers are
left, with the original total.  (4) For a list of length at most two the total is
`getD 0 [] + getD 1 []`, as `val x [] = 0` (`val_eq`, `bitsVal` of `[]` is `0` by
`bitsVal_eq_prefixVal` and `prefixVal_zero`). -/
theorem csaReduce_val (x : Fin n → Bool) (Us : List (List (TreeCircuit n))) :
    val x (csaReduce Us).1 + val x (csaReduce Us).2 = (Us.map (val x)).sum := by
  sorry

/-- **F6, depth.** The two numbers lie at most `4 · csaLevels |Us|` levels above the inputs
(counted from at least `1`): `TreeCircuit.maxDepth ((csaReduce Us).1 ++ (csaReduce Us).2) ≤
max 1 (TreeCircuit.maxDepth Us.flatten) + 4 * csaLevels Us.length`.  r3's
"`depth ≤ 4·csaLevels k + d₀`" *(fix)*, settled with `d₀ = max 1 (input depth)`.  No term
depends on the bit length.

**Proof sketch.** With `D = max 1 (maxDepth Us.flatten)`: one layer raises the bound by at
most `4` (`csaLayer`'s cases, `depth_csaStep_le` for each triple, the kept remainder
unchanged), so `j` layers give `D + 4 j` (induction on `j`, `Nat.repeat`); with
`j = csaLevels |Us|` the two read-off numbers are members (or `[]`) of the final list
(`List.getD`, `maxDepth_nil`). -/
theorem depth_csaReduce_le (Us : List (List (TreeCircuit n))) :
    TreeCircuit.maxDepth ((csaReduce Us).1 ++ (csaReduce Us).2) ≤
      max 1 (TreeCircuit.maxDepth Us.flatten) + 4 * csaLevels Us.length := by
  sorry

/-- **F6, fan-in two.** The reduction adds only fan-in-2 gates:
`TreeCircuit.maxFaninL ((csaReduce Us).1 ++ (csaReduce Us).2) ≤
max 2 (TreeCircuit.maxFaninL Us.flatten)`.  Glue.

**Proof sketch.** As `depth_csaReduce_le`, with `maxFaninL_csaStep_le` for each triple: the
bound `max 2 (maxFaninL Us.flatten)` is kept by every layer. -/
theorem maxFaninL_csaReduce_le (Us : List (List (TreeCircuit n))) :
    TreeCircuit.maxFaninL ((csaReduce Us).1 ++ (csaReduce Us).2) ≤
      max 2 (TreeCircuit.maxFaninL Us.flatten) := by
  sorry

/-- **F6, the number of layers.** At most `2⌈log₂ k⌉` carry-save layers reduce `k` numbers to
two: `csaLevels k ≤ 2 * Nat.clog 2 k`.  Glue (r3 §H5.7, F6); r3's draft constant
`2⌈log₂ k⌉ + 3` *(fix)* is settled at `2⌈log₂ k⌉`, which holds (probe P10: kernel `decide`
for `k < 512` against a structural surrogate of `Nat.clog 2`, `#eval` for `k < 100000`).

**Proof sketch.** Strong induction on `k`.  For `k ≤ 2`, `csaLevels_of_le_two`.  For `k > 2`,
let `k₁ = 2 (k / 3) + k % 3`; if `k₁ ≤ 2` then `csaLevels k = 1 ≤ 2 ≤ 2⌈log₂ k⌉`.  Otherwise
`csaLevels k = csaLevels k₂ + 2` with `k₂ = 2 (k₁ / 3) + k₁ % 3` (`csaLevels_of_two_lt` twice),
and `k₂ ≤ ⌈k / 2⌉` (by `omega` for `k ≥ 20`, from `k₂ ≤ (4k + 10) / 9`, and by cases below), so
`⌈log₂ k₂⌉ ≤ ⌈log₂ k⌉ - 1` (`Nat.clog_mono_right`, `Nat.clog_of_two_le`) and the induction
hypothesis closes it. -/
theorem csaLevels_le (k : ℕ) : csaLevels k ≤ 2 * Nat.clog 2 k := by
  sorry

end FormulaArith

end BoolCircuit
