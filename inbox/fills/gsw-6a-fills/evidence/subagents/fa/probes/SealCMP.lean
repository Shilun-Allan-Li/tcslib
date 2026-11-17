/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave

attribute [local irreducible] BoolCircuit.bitsVal BoolCircuit.prefixVal BoolCircuit.carryBit
  BoolCircuit.sumBit BoolCircuit.Lit.eval
  BoolCircuit.TreeCircuit.maxDepth BoolCircuit.TreeCircuit.maxFaninL
  BoolCircuit.TreeCircuit.const BoolCircuit.TreeCircuit.and2 BoolCircuit.TreeCircuit.or2
  BoolCircuit.TreeCircuit.xor2 BoolCircuit.TreeCircuit.xor3 BoolCircuit.TreeCircuit.maj3
  BoolCircuit.TreeCircuit.balanced BoolCircuit.TreeCircuit.neg
attribute [local irreducible] BoolCircuit.FormulaArith.val BoolCircuit.FormulaArith.csaStep
  BoolCircuit.FormulaArith.csaLayer BoolCircuit.FormulaArith.csaLevels BoolCircuit.FormulaArith.csaReduce


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

/-- A common depth bound of the members bounds the maximum depth of a list:
`(∀ c ∈ cs, c.depth ≤ d) → TreeCircuit.maxDepth cs ≤ d`.  Glue. -/
private theorem maxDepth_le_of_forall {cs : List (TreeCircuit n)} {d : ℕ}
    (h : ∀ c ∈ cs, c.depth ≤ d) : TreeCircuit.maxDepth cs ≤ d := by
  induction cs with
  | nil => rw [TreeCircuit.maxDepth_nil]; exact Nat.zero_le d
  | cons c cs ih =>
      rw [TreeCircuit.maxDepth_cons]
      exact max_le (h c List.mem_cons_self) (ih fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- A common fan-in bound of the members bounds the maximum fan-in of a list:
`(∀ c ∈ cs, c.maxFanin ≤ d) → TreeCircuit.maxFaninL cs ≤ d`.  Glue. -/
private theorem maxFaninL_le_of_forall {cs : List (TreeCircuit n)} {d : ℕ}
    (h : ∀ c ∈ cs, c.maxFanin ≤ d) : TreeCircuit.maxFaninL cs ≤ d := by
  induction cs with
  | nil => rw [TreeCircuit.maxFaninL_nil]; exact Nat.zero_le d
  | cons c cs ih =>
      rw [TreeCircuit.maxFaninL_cons]
      exact max_le (h c List.mem_cons_self) (ih fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- Bits that are `false` from position `i` on add nothing: for `i ≤ m`,
`(∀ j, i ≤ j → f j = false) → prefixVal f m = prefixVal f i`.  Glue. -/
private theorem prefixVal_eq_of_false {f : ℕ → Bool} {i m : ℕ} (hle : i ≤ m)
    (h : ∀ j, i ≤ j → f j = false) : prefixVal f m = prefixVal f i := by
  induction m, hle using Nat.le_induction with
  | base => rfl
  | succ m him ih =>
      rw [prefixVal_succ, ih, h m him, Bool.toNat_false, Nat.zero_mul, Nat.add_zero]

/-- A bit padded by `const false` evaluates to the bit sequence:
`(U.getD j (TreeCircuit.const false)).eval x = bitAt x U j`.  Glue. -/
private theorem eval_getD_const (x : Fin n → Bool) (U : List (TreeCircuit n)) (j : ℕ) :
    (U.getD j (TreeCircuit.const false)).eval x = bitAt x U j := by
  have h := List.getD_map U (TreeCircuit.const false) (n := j) fun c : TreeCircuit n => c.eval x
  rw [TreeCircuit.const_eval] at h
  rw [bitAt_eq, h]

/-- A formula number is the value of its bit sequence over any `m ≥ |U|` bits:
`U.length ≤ m → val x U = prefixVal (bitAt x U) m`.  Glue. -/
private theorem val_eq_prefixVal_bitAt (x : Fin n → Bool) {U : List (TreeCircuit n)} {m : ℕ}
    (hm : U.length ≤ m) : val x U = prefixVal (bitAt x U) m := by
  calc val x U = prefixVal (bitAt x U) U.length := by
        rw [val_eq, bitsVal_eq_prefixVal, List.length_map]
        exact prefixVal_congr fun j _ => (bitAt_eq x U j).symm
    _ = prefixVal (bitAt x U) m :=
        (prefixVal_eq_of_false hm fun j hj => by
          rw [bitAt_eq, List.getD_eq_default _ _ (by rw [List.length_map]; exact hj)]).symm

/-- A padded bit is no deeper than a common bound `d ≥ 1` of the members:
`(∀ c ∈ U, c.depth ≤ d) → 1 ≤ d → (U.getD i (TreeCircuit.const false)).depth ≤ d`.  Glue. -/
private theorem depth_getD_le {U : List (TreeCircuit n)} {d : ℕ} (h : ∀ c ∈ U, c.depth ≤ d)
    (hd : 1 ≤ d) (i : ℕ) : (U.getD i (TreeCircuit.const false)).depth ≤ d := by
  by_cases hi : i < U.length
  · rw [List.getD_eq_getElem U _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default U _ (Nat.le_of_not_lt hi), TreeCircuit.depth_const]
    exact hd

/-- A padded bit has fan-in at most a common bound of the members:
`(∀ c ∈ U, c.maxFanin ≤ d) → (U.getD i (TreeCircuit.const false)).maxFanin ≤ d`.  Glue. -/
private theorem maxFanin_getD_le {U : List (TreeCircuit n)} {d : ℕ}
    (h : ∀ c ∈ U, c.maxFanin ≤ d) (i : ℕ) :
    (U.getD i (TreeCircuit.const false)).maxFanin ≤ d := by
  by_cases hi : i < U.length
  · rw [List.getD_eq_getElem U _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default U _ (Nat.le_of_not_lt hi), TreeCircuit.maxFanin_const]
    exact Nat.zero_le d

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

/-- The ripple carry into position `b` is set exactly when some bit `j < b` generates a carry
and every bit strictly between `j` and `b` transmits it:
`carryBit A B b = true ↔ ∃ j < b, A j = true ∧ B j = true ∧
∀ i, j < i → i < b → (A i || B i) = true`.  Glue.

**Proof sketch.** Induction on `b` with `carryBit_zero`/`carryBit_succ`.  At `b + 1`, the carry
is `(A_b ∧ B_b) ∨ ((A_b ⊕ B_b) ∧ carry_b)`, which equals `(A_b ∧ B_b) ∨ ((A_b ∨ B_b) ∧ carry_b)`
(cases on the Booleans): the first disjunct is the witness `j = b`, the second extends a
witness `j < b` of the induction hypothesis by the transmitting bit `b`. -/
private theorem carryBit_eq_true_iff (A B : ℕ → Bool) (b : ℕ) :
    carryBit A B b = true ↔
      ∃ j < b, A j = true ∧ B j = true ∧ ∀ i, j < i → i < b → (A i || B i) = true := by
  induction b with
  | zero =>
      rw [carryBit_zero]
      exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)⟩
  | succ b ih =>
      rw [carryBit_succ]
      constructor
      · intro h
        by_cases hg : A b = true ∧ B b = true
        · exact ⟨b, Nat.lt_succ_self b, hg.1, hg.2, fun i hi hib => absurd hib (by omega)⟩
        -- Step 1: no generation at `b`, so `b` transmits and there is a carry into `b`
        have ht : (A b || B b) = true ∧ carryBit A B b = true := by
          revert h hg
          cases A b <;> cases B b <;> cases carryBit A B b <;> decide
        obtain ⟨j, hj, hAj, hBj, hm⟩ := ih.1 ht.2
        refine ⟨j, by omega, hAj, hBj, fun i hji hib => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hib with hib | rfl
        · exact hm i hji hib
        · exact ht.1
      · rintro ⟨j, hj, hAj, hBj, hm⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        -- Step 2: a witness below `b` gives a carry into `b`, which bit `b` transmits
        · have hc := ih.2 ⟨j, hj, hAj, hBj, fun i h1 h2 => hm i h1 (by omega)⟩
          have hor := hm b hj (Nat.lt_succ_self b)
          rw [hc]
          revert hor
          cases A b <;> cases B b <;> decide
        · simp only [hAj, hBj, Bool.and_self, Bool.true_or]

/-- **F7, value.** The carry-out formula computes the ripple carry into position `b`:
`(carryOut U W b).eval x = carryBit (bitAt x U) (bitAt x W) b` (`Adder.lean:377`).  Glue
(r3 §H5.7, F7).  *Statement change:* r3's sketch writes `carryOut U W` with the position `b`
free; the position is the explicit third argument.

**Proof sketch.** Induction on `b` for the unrolled carry: `carryBit A B (i + 1) =
(A_i ∧ B_i) ∨ ((A_i ⊕ B_i) ∧ carryBit A B i)` (`carryBit_zero`, `carryBit_succ`) equals
`(A_i ∧ B_i) ∨ ((A_i ∨ B_i) ∧ carryBit A B i)` by cases, and unrolling gives
`carryBit A B b = ∃ j < b, A_j ∧ B_j ∧ ∀ k, j < k < b → A_k ∨ B_k` (`carryBit_eq_true_iff`).
On the formula side `carryOut_eq`, `balanced_eval`, `eval_node_false_iff`/`eval_node_true_iff`,
`and2_eval`, `or2_eval`, and each padded bit evaluates to `bitAt x U j` (`eval_getD_const`:
`bitAt_eq`, `const_eval` for the padding, `List.getD_map`); the inner index `k` of disjunct `j`
is the bit `j + 1 + k`. -/
theorem carryOut_eval (U W : List (TreeCircuit n)) (b : ℕ) (x : Fin n → Bool) :
    (carryOut U W b).eval x = carryBit (bitAt x U) (bitAt x W) b := by
  rw [Bool.eq_iff_iff, carryOut_eq, TreeCircuit.balanced_eval, TreeCircuit.eval_node_false_iff,
    carryBit_eq_true_iff]
  constructor
  -- Step 1: a true disjunct `j` is a generate/propagate witness
  · rintro ⟨c, hc, hce⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hj
    rw [TreeCircuit.balanced_eval, TreeCircuit.eval_node_true_iff] at hce
    have h0 := hce _ List.mem_cons_self
    rw [TreeCircuit.and2_eval, eval_getD_const, eval_getD_const, Bool.and_eq_true] at h0
    refine ⟨j, hj, h0.1, h0.2, fun i hji hib => ?_⟩
    have hji : j + 1 + (i - (j + 1)) = i := by omega
    have hi := hce (TreeCircuit.or2 (U.getD i (TreeCircuit.const false))
      (W.getD i (TreeCircuit.const false))) (List.mem_cons_of_mem _ (List.mem_map.2
        ⟨i - (j + 1), List.mem_range.2 (by omega), by rw [hji]⟩))
    rwa [TreeCircuit.or2_eval, eval_getD_const, eval_getD_const] at hi
  -- Step 2: a witness `j` makes disjunct `j` true
  · rintro ⟨j, hj, hA, hB, hm⟩
    refine ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, ?_⟩
    rw [TreeCircuit.balanced_eval, TreeCircuit.eval_node_true_iff]
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rw [TreeCircuit.and2_eval, eval_getD_const, eval_getD_const, hA, hB]
      rfl
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
      rw [List.mem_range] at hk
      rw [TreeCircuit.or2_eval, eval_getD_const, eval_getD_const]
      exact hm _ (by omega) (by omega)

/-- **F7, the threshold.** For numbers of at most `b` bits the carry into position `b` is the
test `2 ^ b ≤ U + W`: `U.length ≤ b → W.length ≤ b →
(carryOut U W b).eval x = decide (2 ^ b ≤ val x U + val x W)`.  Glue (r3 §H5.7, F7).

**Proof sketch.** `carryOut_eval`, then `prefixVal_add` (`Adder.lean:397`) at `b`:
`prefixVal A b + prefixVal B b = prefixVal (sumBit A B) b + 2 ^ b · carry`.  Here
`prefixVal (bitAt x U) b = val x U` (`val_eq_prefixVal_bitAt`: `val_eq`, `bitsVal_eq_prefixVal`,
`prefixVal_congr`, and `prefixVal_eq_of_false` to extend from `|U|` to `b` bits by `false`), and
`prefixVal (sumBit A B) b < 2 ^ b` (`prefixVal_lt`), so the carry is `1` exactly when
`2 ^ b ≤ val x U + val x W`. -/
theorem carryOut_eval_le {U W : List (TreeCircuit n)} {b : ℕ} (hU : U.length ≤ b)
    (hW : W.length ≤ b) (x : Fin n → Bool) :
    (carryOut U W b).eval x = decide (2 ^ b ≤ val x U + val x W) := by
  rw [carryOut_eval]
  have hadd := prefixVal_add (bitAt x U) (bitAt x W) b
  rw [← val_eq_prefixVal_bitAt x hU, ← val_eq_prefixVal_bitAt x hW] at hadd
  have hlt := prefixVal_lt (sumBit (bitAt x U) (bitAt x W)) b
  cases hc : carryBit (bitAt x U) (bitAt x W) b
  · rw [hc, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hadd
    exact (decide_eq_false (by omega)).symm
  · rw [hc, Bool.toNat_true, Nat.mul_one] at hadd
    exact (decide_eq_true (by omega)).symm

/-- **F7, depth.** The carry-out lies `2⌈log₂ b⌉ + 3` levels above the bits (counted from at
least `1`, the depth of the padding constants):
`(carryOut U W b).depth ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) + 2 * Nat.clog 2 b + 3`.
Glue (r3 §H5.7, F7); r3's draft "depth `2⌈log₂(b+1)⌉ + 2`" *(fix)* is settled by this
construction at `2⌈log₂ b⌉ + 3` over the inputs.

**Proof sketch.** With `D = max 1 (maxDepth (U ++ W))`: every padded bit has depth `≤ D`
(`depth_getD_le`: `depth_le_maxDepth`, `depth_const`), so every `and2`/`or2` item has depth
`≤ D + 1` (`depth_and2_le`, `depth_or2_le`, `maxDepth_le_of_forall`).  The inner list for
`j < b` has `b - j ≤ b` items, so its `balanced true` tree has depth `≤ D + 1 + ⌈log₂ b⌉ + 1`
(`depth_balanced_le`, `Nat.clog_mono_right`); the outer list has `b` items, so the outer
`balanced false` tree adds `⌈log₂ b⌉ + 1` more (`depth_balanced_le`, `maxDepth_le_of_forall`). -/
theorem depth_carryOut_le (U W : List (TreeCircuit n)) (b : ℕ) :
    (carryOut U W b).depth ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) + 2 * Nat.clog 2 b + 3 := by
  -- Step 1: every padded bit lies within `D = max 1 (maxDepth (U ++ W))`
  have hpad : ∀ V : List (TreeCircuit n), (∀ c ∈ V, c ∈ U ++ W) → ∀ i,
      (V.getD i (TreeCircuit.const false)).depth ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) :=
    fun V hV => depth_getD_le
      (fun c hc => (TreeCircuit.depth_le_maxDepth (hV c hc)).trans (le_max_right _ _))
      (le_max_left _ _)
  have hU := hpad U fun c hc => List.mem_append_left _ hc
  have hW := hpad W fun c hc => List.mem_append_right _ hc
  -- Step 2: the outer balanced tree over `b` inner trees
  rw [carryOut_eq]
  refine le_trans (TreeCircuit.depth_balanced_le false _) ?_
  rw [List.length_map, List.length_range]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (maxDepth_le_of_forall
    (d := max 1 (TreeCircuit.maxDepth (U ++ W)) + Nat.clog 2 b + 2) fun c hc => ?_) _) _) ?_
  · -- Step 3: each inner balanced tree over at most `b` gates `and2`/`or2`
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hj
    refine le_trans (TreeCircuit.depth_balanced_le true _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add (maxDepth_le_of_forall
      (d := max 1 (TreeCircuit.maxDepth (U ++ W)) + 1) fun c hc => ?_)
      (Nat.clog_mono_right 2 (?_ : _ ≤ b))) _) ?_
    · rcases List.mem_cons.1 hc with rfl | hc
      · refine (TreeCircuit.depth_and2_le _ _).trans ?_
        have := hU j; have := hW j
        omega
      · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
        refine (TreeCircuit.depth_or2_le _ _).trans ?_
        have := hU (j + 1 + k); have := hW (j + 1 + k)
        omega
    · rw [List.length_cons, List.length_map, List.length_range]
      omega
    · omega
  · omega

/-- **F7, fan-in two.**
`(carryOut U W b).maxFanin ≤ max 2 (TreeCircuit.maxFaninL (U ++ W))`.  Glue.

**Proof sketch.** `carryOut_eq`; `maxFanin_balanced_le` for both trees, `maxFanin_and2_le`,
`maxFanin_or2_le`, and each padded bit has fan-in `≤ maxFaninL (U ++ W)` (`maxFanin_getD_le`:
`maxFanin_le_maxFaninL`, `maxFanin_const`); a bound on every member bounds each list's maximum
(`maxFaninL_le_of_forall`, by list induction with `maxFaninL_cons`). -/
theorem maxFanin_carryOut_le (U W : List (TreeCircuit n)) (b : ℕ) :
    (carryOut U W b).maxFanin ≤ max 2 (TreeCircuit.maxFaninL (U ++ W)) := by
  -- Step 1: every padded bit has fan-in at most `maxFaninL (U ++ W)`
  have hpad : ∀ V : List (TreeCircuit n), (∀ c ∈ V, c ∈ U ++ W) → ∀ i,
      (V.getD i (TreeCircuit.const false)).maxFanin ≤ TreeCircuit.maxFaninL (U ++ W) :=
    fun V hV => maxFanin_getD_le fun c hc => TreeCircuit.maxFanin_le_maxFaninL (hV c hc)
  have hU := hpad U fun c hc => List.mem_append_left _ hc
  have hW := hpad W fun c hc => List.mem_append_right _ hc
  -- Step 2: both balanced trees, then the `and2`/`or2` items
  rw [carryOut_eq]
  refine le_trans (TreeCircuit.maxFanin_balanced_le false _)
    (max_le (le_max_left _ _) (maxFaninL_le_of_forall fun c hc => ?_))
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  refine le_trans (TreeCircuit.maxFanin_balanced_le true _)
    (max_le (le_max_left _ _) (maxFaninL_le_of_forall fun c hc => ?_))
  rcases List.mem_cons.1 hc with rfl | hc
  · refine (TreeCircuit.maxFanin_and2_le _ _).trans ?_
    have := hU j; have := hW j
    omega
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
    refine (TreeCircuit.maxFanin_or2_le _ _).trans ?_
    have := hU (j + 1 + k); have := hW (j + 1 + k)
    omega

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

/-- The low `p` bits of `c` have the value `c mod 2 ^ p`: `prefixVal c.testBit p = c % 2 ^ p`.
Glue. -/
private theorem prefixVal_testBit (c p : ℕ) : prefixVal c.testBit p = c % 2 ^ p := by
  induction p with
  | zero => rw [prefixVal_zero, Nat.pow_zero, Nat.mod_one]
  | succ p ih => rw [prefixVal_succ, ih, Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]

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
`T = 2 ^ p - c < 2 ^ p` and `val x (constBits p T) = T` (`val_eq_prefixVal_bitAt`,
`constBits_eq`, `const_eval`, and `prefixVal c.testBit p = c % 2 ^ p` by `prefixVal_testBit`:
`prefixVal_succ`, `Nat.mod_pow_succ`, `Nat.toNat_testBit`); `csaStep_val` gives
`val S + val K = val U + val W + T`, with `|S| = p` and `|K| = p + 1` (`csaStep_eq`).  The top
bit of the carry word `K` is `maj3` of the padding of `U`, `W` (both `const false`, as
`|U|, |W| ≤ p - 1`) and a bit of `T`, so it is `false` (`csaStep_eq`, `maj3_eval`) and
`val K = prefixVal (bitAt x K) p`; hence `carryOut_eval` and `prefixVal_add` at `p`, with
`prefixVal_lt` for the sum bits, give the carry into position `p` as
`decide (2 ^ p ≤ val S + val K)`, which is `decide (c ≤ val x U + val x W)`. -/
theorem geConst_eval (U W : List (TreeCircuit n)) (c : ℕ) (x : Fin n → Bool) :
    (geConst U W c).eval x = decide (c ≤ val x U + val x W) := by
  obtain ⟨p, hp⟩ : ∃ p, max U.length W.length + 1 = p := ⟨_, rfl⟩
  -- Step 1: `val x U + val x W < 2 ^ p`
  have hpow : 2 ^ p = 2 ^ (p - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hvU : val x U < 2 ^ (p - 1) := by
    rw [val_eq_prefixVal_bitAt x (le_refl U.length)]
    exact lt_of_lt_of_le (prefixVal_lt _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hvW : val x W < 2 ^ (p - 1) := by
    rw [val_eq_prefixVal_bitAt x (le_refl W.length)]
    exact lt_of_lt_of_le (prefixVal_lt _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [geConst_eq, hp]
  split_ifs with h0 h1
  -- Step 2: the two constant cases
  · rw [TreeCircuit.const_eval, h0]
    exact (decide_eq_true (Nat.zero_le _)).symm
  · rw [TreeCircuit.const_eval]
    exact (decide_eq_false (by omega)).symm
  -- Step 3: the constant `T = 2 ^ p - c` as `p` constant bits
  obtain ⟨T, hT⟩ : ∃ T, 2 ^ p - c = T := ⟨_, rfl⟩
  rw [hT]
  have hV : (constBits p T : List (TreeCircuit n)).length = p := by
    rw [constBits_eq, List.length_map, List.length_range]
  have hvV : val x (constBits p T) = T := by
    rw [val_eq_prefixVal_bitAt x hV.le, prefixVal_congr (g := T.testBit) fun j hj => ?_,
      prefixVal_testBit, Nat.mod_eq_of_lt (by omega)]
    rw [← eval_getD_const, constBits_eq,
      List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj),
      List.getElem_map, List.getElem_range, TreeCircuit.const_eval]
  -- Step 4: one carry-save step; the sum word has `p` bits, the carry word `p + 1`
  have hcsa := csaStep_val x U W (constBits p T)
  have hS : (csaStep U W (constBits p T)).1.length = p := by
    rw [csaStep_eq]
    dsimp only
    rw [List.length_map, List.length_range, hV]
    omega
  have hK : (csaStep U W (constBits p T)).2.length = p + 1 := by
    rw [csaStep_eq]
    dsimp only
    rw [List.length_cons, List.length_map, List.length_range, hV]
    omega
  -- Step 5: the top carry bit is `maj3` of two padding bits and a bit of `T`, so `false`
  have htop : bitAt x (csaStep U W (constBits p T)).2 p = false := by
    rw [← eval_getD_const, csaStep_eq]
    dsimp only
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.getD_cons_succ,
      List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range, hV]; omega),
      List.getElem_map, List.getElem_range, TreeCircuit.maj3_eval,
      List.getD_eq_default U _ (by omega), List.getD_eq_default W _ (by omega),
      TreeCircuit.const_eval]
    cases ((constBits (q + 1) T : List (TreeCircuit n)).getD q (TreeCircuit.const false)).eval x
      <;> rfl
  -- Step 6: the carry into position `p` of `S + K` tests `2 ^ p ≤ val S + val K`
  have hvS := val_eq_prefixVal_bitAt x hS.le
  have hvK : val x (csaStep U W (constBits p T)).2 =
      prefixVal (bitAt x (csaStep U W (constBits p T)).2) p := by
    rw [val_eq_prefixVal_bitAt x hK.le, prefixVal_succ, htop, Bool.toNat_false, Nat.zero_mul,
      Nat.add_zero]
  rw [carryOut_eval]
  have hadd := prefixVal_add (bitAt x (csaStep U W (constBits p T)).1)
    (bitAt x (csaStep U W (constBits p T)).2) p
  have hlt := prefixVal_lt (sumBit (bitAt x (csaStep U W (constBits p T)).1)
    (bitAt x (csaStep U W (constBits p T)).2)) p
  cases hc : carryBit (bitAt x (csaStep U W (constBits p T)).1)
      (bitAt x (csaStep U W (constBits p T)).2) p
  · rw [hc, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hadd
    exact (decide_eq_false (by omega)).symm
  · rw [hc, Bool.toNat_true, Nat.mul_one] at hadd
    exact (decide_eq_true (by omega)).symm

/-- **F8, depth.** The comparison lies `2⌈log₂(max |U| |W| + 1)⌉ + 7` levels above the inputs
(counted from at least `1`):
`(geConst U W c).depth ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) +
2 * Nat.clog 2 (max U.length W.length + 1) + 7`, independent of `c`.  Glue (r3 §H5.7, F8;
r3 names the lemma without a formula).

**Proof sketch.** `geConst_eq`.  The constant cases have depth `1` (`depth_const`).  Otherwise,
with `D = max 1 (maxDepth (U ++ W))`: the constant bits have depth `1` (`constBits_eq`,
`depth_const`), so `maxDepth (U ++ W ++ constBits …) ≤ D` (`maxDepth_le_of_forall`),
`depth_csaStep_le` bounds both words by `D + 4`, and `depth_carryOut_le` at
`p = max |U| |W| + 1` adds `2⌈log₂ p⌉ + 3`. -/
theorem depth_geConst_le (U W : List (TreeCircuit n)) (c : ℕ) :
    (geConst U W c).depth ≤
      max 1 (TreeCircuit.maxDepth (U ++ W)) + 2 * Nat.clog 2 (max U.length W.length + 1) + 7 := by
  rw [geConst_eq]
  generalize max U.length W.length + 1 = p
  have hD : 1 ≤ max 1 (TreeCircuit.maxDepth (U ++ W)) := le_max_left _ _
  split_ifs
  · rw [TreeCircuit.depth_const]
    omega
  · rw [TreeCircuit.depth_const]
    omega
  -- Step 1: the inputs of the carry-save step, the constant bits included, lie within `D`
  have hin : TreeCircuit.maxDepth (U ++ W ++ constBits p (2 ^ p - c)) ≤
      max 1 (TreeCircuit.maxDepth (U ++ W)) := maxDepth_le_of_forall fun d hd => by
    rcases List.mem_append.1 hd with hd | hd
    · exact (TreeCircuit.depth_le_maxDepth hd).trans (le_max_right _ _)
    · rw [constBits_eq] at hd
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hd
      rw [TreeCircuit.depth_const]
      exact le_max_left _ _
  -- Step 2: `+4` for the step, `+ 2⌈log₂ p⌉ + 3` for the carry-out
  have hcsa := depth_csaStep_le U W (constBits p (2 ^ p - c))
  refine le_trans (depth_carryOut_le _ _ _) ?_
  omega

/-- **F8, fan-in two.**
`(geConst U W c).maxFanin ≤ max 2 (TreeCircuit.maxFaninL (U ++ W))`.  Glue.

**Proof sketch.** `geConst_eq`; `maxFanin_const` for the constant cases, otherwise
`maxFanin_carryOut_le` and `maxFaninL_csaStep_le` (the constant bits have fan-in `0`, so
`maxFaninL (U ++ W ++ constBits …) ≤ maxFaninL (U ++ W)` by `maxFaninL_le_of_forall`). -/
theorem maxFanin_geConst_le (U W : List (TreeCircuit n)) (c : ℕ) :
    (geConst U W c).maxFanin ≤ max 2 (TreeCircuit.maxFaninL (U ++ W)) := by
  rw [geConst_eq]
  generalize max U.length W.length + 1 = p
  split_ifs
  · rw [TreeCircuit.maxFanin_const]
    exact Nat.zero_le _
  · rw [TreeCircuit.maxFanin_const]
    exact Nat.zero_le _
  have hin : TreeCircuit.maxFaninL (U ++ W ++ constBits p (2 ^ p - c)) ≤
      TreeCircuit.maxFaninL (U ++ W) := maxFaninL_le_of_forall fun d hd => by
    rcases List.mem_append.1 hd with hd | hd
    · exact TreeCircuit.maxFanin_le_maxFaninL hd
    · rw [constBits_eq] at hd
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hd
      rw [TreeCircuit.maxFanin_const]
      exact Nat.zero_le _
  have hcsa := maxFaninL_csaStep_le U W (constBits p (2 ^ p - c))
  refine le_trans (maxFanin_carryOut_le _ _ _) ?_
  omega

end FormulaArith

end BoolCircuit
