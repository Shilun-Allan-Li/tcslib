/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave

/-!
# Formula arithmetic: carry-out and comparison with a constant

For two little-endian formula numbers `U, W` (`FormulaArith.val`), the carry into bit position
`b` of `U + W` is a formula of depth `2⌈log₂ b⌉ + 3` over the bits, by the generate/propagate
expansion `carry_b = ⋁_{j < b} (U_j ∧ W_j ∧ ⋀_{j < k < b} (U_k ∨ W_k))` with balanced fan-in-2
trees; its value is `Adder.lean`'s ripple carry `carryBit`.  The test `c ≤ val U + val W` for a
constant `c` is the carry-out of `U + W + (2^p - c)` after one more carry-save step.  No
construction here is a truth table over the bit length: the depth is logarithmic in it
(r3 §H3.3).

## Main definitions

* `BoolCircuit.FormulaArith.bitAt` — the bit sequence of a formula number under an assignment.
* `BoolCircuit.FormulaArith.carryOut` — the carry into position `b` of `U + W`.
* `BoolCircuit.FormulaArith.constBits` — the low `p` bits of a constant, as constant formulas.
* `BoolCircuit.FormulaArith.geConst` — the comparison `c ≤ val U + val W`.

## Main results

* `BoolCircuit.FormulaArith.carryOut_eval`, `carryOut_eval_le`, `depth_carryOut_le`,
  `maxFanin_carryOut_le` — F7: the value is `carryBit`, hence `2 ^ b ≤ val U + val W` for
  `b`-bit numbers; depth `2⌈log₂ b⌉ + 3` over the bits; fan-in two (targets).
* `BoolCircuit.FormulaArith.geConst_eval`, `depth_geConst_le`, `maxFanin_geConst_le` — F8:
  the comparison with a constant, its depth and fan-in (targets).

## References

* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011, pp. 97–106; full version, IACR ePrint 2011/344 (39 pages,
  2 March 2012), §4.5, Lemma 4.5.  Context only: the declarations of this file are glue for
  the comparison step of the modular interval sum (`ModSum.lean`) and carry no tag.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

namespace FormulaArith

variable {n : ℕ}

/-! ### Bit sequences and the carry-out (F7) -/

/-- The bit sequence of a little-endian formula number under the assignment `x`, padded with
`false`: `bitAt x U j = (U.map (·.eval x)).getD j false`, the bit sequence whose
`prefixVal` over `|U|` bits is `val x U` (`Adder.lean`'s `bitsVal_eq_prefixVal`).  Glue. -/
def bitAt (x : Fin n → Bool) (U : List (TreeCircuit n)) (j : ℕ) : Bool :=
  (U.map fun c => c.eval x).getD j false

/-- The bit sequence of a formula number: `bitAt x U j = (U.map fun c => c.eval x).getD j false`.
-/
theorem bitAt_eq (x : Fin n → Bool) (U : List (TreeCircuit n)) (j : ℕ) :
    bitAt x U j = (U.map fun c => c.eval x).getD j false := rfl

/-- The carry into bit position `b` of `U + W`, by generate/propagate: with `U_j, W_j` the bits
padded by `const false`, `carryOut U W b = ⋁_{j < b} ⋀ [U_j ∧ W_j, U_{j+1} ∨ W_{j+1}, …,
U_{b-1} ∨ W_{b-1}]` (bit `j` generates a carry and every higher bit below `b` transmits it),
the outer `∨` over `j < b` and each inner `∧` as `TreeCircuit.balanced` fan-in-2 trees.  Its
value is `carryBit` (`carryOut_eval`), its depth `2⌈log₂ b⌉ + 3` over the bits
(`depth_carryOut_le`).  Glue. -/
def carryOut (U W : List (TreeCircuit n)) (b : ℕ) : TreeCircuit n :=
  TreeCircuit.balanced false ((List.range b).map fun j =>
    TreeCircuit.balanced true
      (TreeCircuit.and2 (U.getD j (TreeCircuit.const false)) (W.getD j (TreeCircuit.const false)) ::
        (List.range (b - 1 - j)).map fun k =>
          TreeCircuit.or2 (U.getD (j + 1 + k) (TreeCircuit.const false))
            (W.getD (j + 1 + k) (TreeCircuit.const false))))

/-- The carry-out formula written out: with `z = const false`,
`carryOut U W b = balanced false ((range b).map fun j => balanced true
(and2 (U.getD j z) (W.getD j z) :: (range (b - 1 - j)).map fun k =>
or2 (U.getD (j + 1 + k) z) (W.getD (j + 1 + k) z)))`. -/
theorem carryOut_eq (U W : List (TreeCircuit n)) (b : ℕ) :
    carryOut U W b =
      TreeCircuit.balanced false ((List.range b).map fun j =>
        TreeCircuit.balanced true
          (TreeCircuit.and2 (U.getD j (TreeCircuit.const false))
              (W.getD j (TreeCircuit.const false)) ::
            (List.range (b - 1 - j)).map fun k =>
              TreeCircuit.or2 (U.getD (j + 1 + k) (TreeCircuit.const false))
                (W.getD (j + 1 + k) (TreeCircuit.const false)))) := rfl

/-- **F7, value.** The carry-out formula computes the ripple carry into position `b`:
`(carryOut U W b).eval x = carryBit (bitAt x U) (bitAt x W) b` (`Adder.lean:377`).  Glue
(r3 §H5.7, F7).  *Statement change:* r3's sketch writes `carryOut U W` with the position `b`
free; the position is the explicit third argument.

**Proof sketch.** Induction on `b` for the unrolled carry: `carryBit A B (i + 1) =
(A_i ∧ B_i) ∨ ((A_i ⊕ B_i) ∧ carryBit A B i)` (reader of `carryBit` missing; see the census)
equals `(A_i ∧ B_i) ∨ ((A_i ∨ B_i) ∧ carryBit A B i)` by cases, and unrolling gives
`carryBit A B b = ∃ j < b, A_j ∧ B_j ∧ ∀ k, j < k < b → A_k ∨ B_k`.  On the formula side
`carryOut_eq`, `balanced_eval`, `eval_node_false`/`eval_node_true`, `and2_eval`, `or2_eval`,
and each padded bit evaluates to `bitAt x U j` (`bitAt_eq`, `const_eval` for the padding,
`List.getD_map`). -/
theorem carryOut_eval (U W : List (TreeCircuit n)) (b : ℕ) (x : Fin n → Bool) :
    (carryOut U W b).eval x = carryBit (bitAt x U) (bitAt x W) b := by
  sorry

/-- **F7, the threshold.** For numbers of at most `b` bits the carry into position `b` is the
test `2 ^ b ≤ U + W`: `U.length ≤ b → W.length ≤ b →
(carryOut U W b).eval x = decide (2 ^ b ≤ val x U + val x W)`.  Glue (r3 §H5.7, F7).

**Proof sketch.** `carryOut_eval`, then `prefixVal_add` (`Adder.lean:397`) at `b`:
`prefixVal A b + prefixVal B b = prefixVal (sumBit A B) b + 2 ^ b · carry`.  Here
`prefixVal (bitAt x U) b = val x U` (`val_eq`, `bitsVal_eq_prefixVal`, and `prefixVal_congr`
to extend from `|U|` to `b` bits by `false`), and `prefixVal (sumBit A B) b < 2 ^ b`
(`prefixVal_lt`), so the carry is `1` exactly when `2 ^ b ≤ val x U + val x W`. -/
theorem carryOut_eval_le {U W : List (TreeCircuit n)} {b : ℕ} (hU : U.length ≤ b)
    (hW : W.length ≤ b) (x : Fin n → Bool) :
    (carryOut U W b).eval x = decide (2 ^ b ≤ val x U + val x W) := by
  sorry

/-- **F7, depth.** The carry-out lies `2⌈log₂ b⌉ + 3` levels above the bits (counted from at
least `1`, the depth of the padding constants):
`(carryOut U W b).depth ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) + 2 * Nat.clog 2 b + 3`.
Glue (r3 §H5.7, F7); r3's draft "depth `2⌈log₂(b+1)⌉ + 2`" *(fix)* is settled by this
construction at `2⌈log₂ b⌉ + 3` over the inputs.

**Proof sketch.** With `D = max 1 (maxDepth (U ++ W))`: every padded bit has depth `≤ D`
(`depth_le_maxDepth`, `depth_const`), so every `and2`/`or2` item has depth `≤ D + 1`
(`depth_and2_le`, `depth_or2_le`).  The inner list for `j < b` has `b - j ≤ b` items, so its
`balanced true` tree has depth `≤ D + 1 + ⌈log₂ b⌉ + 1` (`depth_balanced_le`,
`Nat.clog_mono_right`); the outer list has `b` items, so the outer `balanced false` tree adds
`⌈log₂ b⌉ + 1` more. -/
theorem depth_carryOut_le (U W : List (TreeCircuit n)) (b : ℕ) :
    (carryOut U W b).depth ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) + 2 * Nat.clog 2 b + 3 := by
  sorry

/-- **F7, fan-in two.**
`(carryOut U W b).maxFanin ≤ max 2 (TreeCircuit.maxFaninL (U ++ W))`.  Glue.

**Proof sketch.** `carryOut_eq`; `maxFanin_balanced_le` for both trees, `maxFanin_and2_le`,
`maxFanin_or2_le`, and each padded bit has fan-in `≤ maxFaninL (U ++ W)`
(`maxFanin_le_maxFaninL`, `maxFanin_const`); list inductions with `maxFaninL_cons`. -/
theorem maxFanin_carryOut_le (U W : List (TreeCircuit n)) (b : ℕ) :
    (carryOut U W b).maxFanin ≤ max 2 (TreeCircuit.maxFaninL (U ++ W)) := by
  sorry

/-! ### Comparison with a constant (F8) -/

/-- The low `p` bits of the constant `c` as constant formulas, little-endian:
`constBits p c = (range p).map fun j => const (c.testBit j)`, of value `c % 2 ^ p`.  Glue. -/
def constBits (p c : ℕ) : List (TreeCircuit n) :=
  (List.range p).map fun j => TreeCircuit.const (c.testBit j)

/-- The constant's bits as formulas:
`constBits p c = (List.range p).map fun j => TreeCircuit.const (c.testBit j)`. -/
theorem constBits_eq (p c : ℕ) :
    (constBits p c : List (TreeCircuit n)) =
      (List.range p).map fun j => TreeCircuit.const (c.testBit j) := rfl

/-- The comparison of `U + W` with the constant `c`: with `p = max |U| |W| + 1` (so that
`val U + val W < 2 ^ p`), `geConst U W c` is `const true` for `c = 0`, `const false` for
`2 ^ p < c`, and otherwise the carry-out at position `p` of the carry-save step of `U`, `W` and
the `p`-bit constant `2 ^ p - c`:
`carryOut (csaStep U W (constBits p (2^p - c))).1 (csaStep U W (constBits p (2^p - c))).2 p`,
since `c ≤ U + W ↔ 2 ^ p ≤ U + W + (2 ^ p - c)`.  Glue (r3 §H3.4 item 3). -/
def geConst (U W : List (TreeCircuit n)) (c : ℕ) : TreeCircuit n :=
  if c = 0 then TreeCircuit.const true
  else if 2 ^ (max U.length W.length + 1) < c then TreeCircuit.const false
  else
    carryOut
      (csaStep U W (constBits (max U.length W.length + 1)
        (2 ^ (max U.length W.length + 1) - c))).1
      (csaStep U W (constBits (max U.length W.length + 1)
        (2 ^ (max U.length W.length + 1) - c))).2
      (max U.length W.length + 1)

/-- The comparison formula written out: with `p = max U.length W.length + 1`,
`geConst U W c = if c = 0 then const true else if 2 ^ p < c then const false else
carryOut (csaStep U W (constBits p (2 ^ p - c))).1 (csaStep U W (constBits p (2 ^ p - c))).2 p`.
-/
theorem geConst_eq (U W : List (TreeCircuit n)) (c : ℕ) :
    geConst U W c =
      if c = 0 then TreeCircuit.const true
      else if 2 ^ (max U.length W.length + 1) < c then TreeCircuit.const false
      else
        carryOut
          (csaStep U W (constBits (max U.length W.length + 1)
            (2 ^ (max U.length W.length + 1) - c))).1
          (csaStep U W (constBits (max U.length W.length + 1)
            (2 ^ (max U.length W.length + 1) - c))).2
          (max U.length W.length + 1) := rfl

/-- **F8, value.** The comparison formula tests `c ≤ U + W`, for all `U`, `W` and `c`:
`(geConst U W c).eval x = decide (c ≤ val x U + val x W)`.  Glue (r3 §H5.7, F8).

**Proof sketch.** `geConst_eq`, with `p = max |U| |W| + 1`, so `val x U, val x W < 2 ^ (p - 1)`
(`val_eq`, `bitsVal_eq_prefixVal`, `prefixVal_lt`) and `val x U + val x W < 2 ^ p`.  For
`c = 0` and for `2 ^ p < c` both sides are constant (`const_eval`).  Otherwise
`T = 2 ^ p - c < 2 ^ p` and `val x (constBits p T) = T` (`constBits_eq`, `const_eval`,
`Nat.testBit` and `bitsVal`); `csaStep_val` gives `val S + val K = val U + val W + T`.  The
carry word `K` has `p + 1` bits, but its top bit is `maj3` of the padding of `U`, `W` (both
`const false`, as `|U|, |W| ≤ p - 1`) and a bit of `T`, so it is `false` (`csaStep_eq`,
`maj3_eval`); hence `carryOut_eval` and `prefixVal_add` give the carry into position `p` as
`decide (2 ^ p ≤ val S + val K)` (`carryOut_eval_le` applied to `K` without its top bit), which
is `decide (c ≤ val x U + val x W)`. -/
theorem geConst_eval (U W : List (TreeCircuit n)) (c : ℕ) (x : Fin n → Bool) :
    (geConst U W c).eval x = decide (c ≤ val x U + val x W) := by
  sorry

/-- **F8, depth.** The comparison lies `2⌈log₂(max |U| |W| + 1)⌉ + 7` levels above the inputs
(counted from at least `1`):
`(geConst U W c).depth ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) +
2 * Nat.clog 2 (max U.length W.length + 1) + 7`, independent of `c`.  Glue (r3 §H5.7, F8;
r3 names the lemma without a formula).

**Proof sketch.** `geConst_eq`.  The constant cases have depth `1` (`depth_const`).  Otherwise,
with `D = max 1 (maxDepth (U ++ W))`: the constant bits have depth `1` (`constBits_eq`,
`depth_const`), so `depth_csaStep_le` bounds both words by `D + 4`, and `depth_carryOut_le` at
`p = max |U| |W| + 1` adds `2⌈log₂ p⌉ + 3`. -/
theorem depth_geConst_le (U W : List (TreeCircuit n)) (c : ℕ) :
    (geConst U W c).depth ≤
      max 1 (TreeCircuit.maxDepth (U ++ W)) + 2 * Nat.clog 2 (max U.length W.length + 1) + 7 := by
  sorry

/-- **F8, fan-in two.**
`(geConst U W c).maxFanin ≤ max 2 (TreeCircuit.maxFaninL (U ++ W))`.  Glue.

**Proof sketch.** `geConst_eq`; `maxFanin_const` for the constant cases, otherwise
`maxFanin_carryOut_le` and `maxFaninL_csaStep_le` (the constant bits have fan-in `0`). -/
theorem maxFanin_geConst_le (U W : List (TreeCircuit n)) (c : ℕ) :
    (geConst U W c).maxFanin ≤ max 2 (TreeCircuit.maxFaninL (U ++ W)) := by
  sorry

end FormulaArith

end BoolCircuit
