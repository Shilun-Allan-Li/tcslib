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

/-- A formula number is the value of its bits padded by `const false`, over any `m ≥ |U|`
bits: `U.length ≤ m →
val x U = prefixVal (fun j => (U.getD j (TreeCircuit.const false)).eval x) m`.  Glue. -/
private theorem val_eq_prefixVal_getD (x : Fin n → Bool) {U : List (TreeCircuit n)} {m : ℕ}
    (hm : U.length ≤ m) :
    val x U = prefixVal (fun j => (U.getD j (TreeCircuit.const false)).eval x) m := by
  have hbit : ∀ j, (U.map fun c => c.eval x).getD j false =
      (U.getD j (TreeCircuit.const false)).eval x := by
    intro j
    have h := List.getD_map U (TreeCircuit.const false) (n := j) fun c : TreeCircuit n => c.eval x
    rwa [TreeCircuit.const_eval] at h
  calc val x U = prefixVal (fun j => (U.getD j (TreeCircuit.const false)).eval x) U.length := by
        rw [val_eq, bitsVal_eq_prefixVal, List.length_map]
        exact prefixVal_congr fun j _ => hbit j
    _ = prefixVal (fun j => (U.getD j (TreeCircuit.const false)).eval x) m := by
        refine (prefixVal_eq_of_false hm fun j hj => ?_).symm
        rw [List.getD_eq_default U _ hj, TreeCircuit.const_eval]

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

/-- The full-adder identity summed over `L` bit positions: if `s j = a j ⊕ b j ⊕ c j` and
`k (j + 1) = maj (a j, b j, c j)` for `j < L` and `k 0 = false`, then
`prefixVal a L + prefixVal b L + prefixVal c L = prefixVal s L + prefixVal k (L + 1)`.  Glue. -/
private theorem prefixVal_fullAdder {a b c s k : ℕ → Bool} {L : ℕ}
    (hs : ∀ j < L, s j = (a j ^^ b j ^^ c j)) (hk0 : k 0 = false)
    (hk : ∀ j < L, k (j + 1) = (a j && b j || c j && (a j ^^ b j))) :
    prefixVal a L + prefixVal b L + prefixVal c L = prefixVal s L + prefixVal k (L + 1) := by
  induction L with
  | zero =>
      simp only [prefixVal_zero, prefixVal_succ, hk0, Bool.toNat_false, Nat.zero_mul]
  | succ L ih =>
      have ih' := ih (fun j hj => hs j (by omega)) (fun j hj => hk j (by omega))
      rw [prefixVal_succ a, prefixVal_succ b, prefixVal_succ c, prefixVal_succ s,
        prefixVal_succ k (L + 1), hs L (by omega), hk L (by omega)]
      have hfa : (a L).toNat + (b L).toNat + (c L).toNat =
          (a L ^^ b L ^^ c L).toNat + 2 * (a L && b L || c L && (a L ^^ b L)).toNat := by
        cases a L <;> cases b L <;> cases c L <;> rfl
      have h2 := congrArg (· * 2 ^ L) hfa
      simp only at h2
      rw [pow_succ]
      nlinarith [ih', h2]

/-- **F5, value.** One carry-save step keeps the total: for every assignment `x`,
`val x A + val x B + val x C = val x (csaStep A B C).1 + val x (csaStep A B C).2`.
[BV11, Lemma 4.5 proof, p029-b002: "The summation (over the integers) can be done in depth
O(log k + log log p)"].  *Deviation:* the paper does not say how; r3 §H3.4 fixes the carry-save
(3:2) tree, of which this is one step.

**Proof sketch.** With `L = max |A| (max |B| |C|)`, `csaStep_eq` gives `S` (length `L`) and
`K` (length `L + 1`).  Every value is a `prefixVal` of its bits padded by `const false`, over
`L` bits for `A, B, C, S` and `L + 1` bits for `K` (`val_eq_prefixVal_getD`: `val_eq`,
`bitsVal_eq_prefixVal`, `prefixVal_congr`, `List.getD_map`, `const_eval`, and
`prefixVal_eq_of_false` for the padding).  Bit by bit, `S_i` is `xor3` and `K_{i+1}` is `maj3`
of the padded inputs (`xor3_eval`, `maj3_eval`) and `K_0 = false` (`const_eval`); the
full-adder identity `a + b + c = (a ⊕ b ⊕ c) + 2 · maj(a, b, c)` (cases on three Booleans),
summed with weights `2 ^ i` by induction on the number of bits (`prefixVal_succ`), gives the
equation (`prefixVal_fullAdder`). -/
theorem csaStep_val (x : Fin n → Bool) (A B C : List (TreeCircuit n)) :
    val x A + val x B + val x C = val x (csaStep A B C).1 + val x (csaStep A B C).2 := by
  obtain ⟨L, hL⟩ : ∃ L, max A.length (max B.length C.length) = L := ⟨_, rfl⟩
  -- Step 1: the two output words, with `L` the longest length
  have hS : (csaStep A B C).1 = (List.range L).map fun i =>
      TreeCircuit.xor3 (A.getD i (TreeCircuit.const false)) (B.getD i (TreeCircuit.const false))
        (C.getD i (TreeCircuit.const false)) := by
    rw [csaStep_eq, hL]
  have hK : (csaStep A B C).2 = TreeCircuit.const false :: (List.range L).map fun i =>
      TreeCircuit.maj3 (A.getD i (TreeCircuit.const false)) (B.getD i (TreeCircuit.const false))
        (C.getD i (TreeCircuit.const false)) := by
    rw [csaStep_eq, hL]
  -- Step 2: every value as a `prefixVal` of its padded bits
  rw [val_eq_prefixVal_getD x (U := A) (m := L) (by omega),
    val_eq_prefixVal_getD x (U := B) (m := L) (by omega),
    val_eq_prefixVal_getD x (U := C) (m := L) (by omega),
    val_eq_prefixVal_getD x (U := (csaStep A B C).1) (m := L)
      (by rw [hS, List.length_map, List.length_range]),
    val_eq_prefixVal_getD x (U := (csaStep A B C).2) (m := L + 1)
      (by rw [hK, List.length_cons, List.length_map, List.length_range])]
  -- Step 3: the full adder bit by bit
  refine prefixVal_fullAdder (fun j hj => ?_) ?_ (fun j hj => ?_)
  · rw [hS, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj),
      List.getElem_map, List.getElem_range, TreeCircuit.xor3_eval]
  · rw [hK, List.getD_cons_zero, TreeCircuit.const_eval]
  · rw [hK, List.getD_cons_succ,
      List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj),
      List.getElem_map, List.getElem_range, TreeCircuit.maj3_eval]

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

/-- **F5, depth `+4`.** Both output words of a carry-save step lie at most four levels above
the inputs (counted from at least `1`, the depth of the padding constants):
`TreeCircuit.maxDepth ((csaStep A B C).1 ++ (csaStep A B C).2) ≤
max 1 (TreeCircuit.maxDepth (A ++ B ++ C)) + 4`.  [BV11, Lemma 4.5 proof, p029-b002];
r3's `+4` *(fix)*, settled: `xor3` is `+4`, `maj3` is `+3`, the constant `const false` has
depth `1`.  No term depends on the bit length.

**Proof sketch.** `csaStep_eq`.  Each padded input bit `A.getD i (const false)` has depth at
most `max 1 (maxDepth (A ++ B ++ C))` (`depth_getD_le`: `depth_le_maxDepth` for a member,
`depth_const` for the padding).  Then `depth_xor3_le` bounds every `S_i` by that plus `4`,
`depth_maj3_le` every `K_{i+1}` by that plus `3`, and `depth_const` gives `K_0` depth `1`; a
bound on every member bounds the maximum (`maxDepth_le_of_forall`, by list induction with
`maxDepth_cons`/`maxDepth_nil`). -/
theorem depth_csaStep_le (A B C : List (TreeCircuit n)) :
    TreeCircuit.maxDepth ((csaStep A B C).1 ++ (csaStep A B C).2) ≤
      max 1 (TreeCircuit.maxDepth (A ++ B ++ C)) + 4 := by
  -- Step 1: every padded input bit lies within `max 1 (maxDepth (A ++ B ++ C))`
  have hd : ∀ U : List (TreeCircuit n), (∀ c ∈ U, c ∈ A ++ B ++ C) → ∀ i,
      (U.getD i (TreeCircuit.const false)).depth ≤ max 1 (TreeCircuit.maxDepth (A ++ B ++ C)) :=
    fun U hU => depth_getD_le
      (fun c hc => (TreeCircuit.depth_le_maxDepth (hU c hc)).trans (le_max_right _ _))
      (le_max_left _ _)
  have hA := hd A fun c hc => List.mem_append_left _ (List.mem_append_left _ hc)
  have hB := hd B fun c hc => List.mem_append_left _ (List.mem_append_right _ hc)
  have hC := hd C fun c hc => List.mem_append_right _ hc
  -- Step 2: every output bit (`xor3`, `const false`, `maj3`) lies within that plus `4`
  rw [csaStep_eq]
  apply maxDepth_le_of_forall
  intro c hc
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with ⟨i, -, rfl⟩ | rfl | ⟨i, -, rfl⟩
  · have := TreeCircuit.depth_xor3_le (A.getD i (TreeCircuit.const false))
      (B.getD i (TreeCircuit.const false)) (C.getD i (TreeCircuit.const false))
    have := hA i; have := hB i; have := hC i
    omega
  · rw [TreeCircuit.depth_const]
    omega
  · have := TreeCircuit.depth_maj3_le (A.getD i (TreeCircuit.const false))
      (B.getD i (TreeCircuit.const false)) (C.getD i (TreeCircuit.const false))
    have := hA i; have := hB i; have := hC i
    omega

/-- **F5, fan-in two.** A carry-save step adds only fan-in-2 gates:
`TreeCircuit.maxFaninL ((csaStep A B C).1 ++ (csaStep A B C).2) ≤
max 2 (TreeCircuit.maxFaninL (A ++ B ++ C))`.  Glue.

**Proof sketch.** `csaStep_eq`; each padded input bit has fan-in at most
`maxFaninL (A ++ B ++ C)` (`maxFanin_getD_le`: `maxFanin_le_maxFaninL`, `maxFanin_const`), and
`maxFanin_xor3_le`, `maxFanin_maj3_le`, `maxFanin_const` bound every output bit; a bound on
every member bounds the maximum (`maxFaninL_le_of_forall`, by list induction with
`maxFaninL_cons`/`maxFaninL_nil`). -/
theorem maxFaninL_csaStep_le (A B C : List (TreeCircuit n)) :
    TreeCircuit.maxFaninL ((csaStep A B C).1 ++ (csaStep A B C).2) ≤
      max 2 (TreeCircuit.maxFaninL (A ++ B ++ C)) := by
  -- Step 1: every padded input bit has fan-in at most `maxFaninL (A ++ B ++ C)`
  have hf : ∀ U : List (TreeCircuit n), (∀ c ∈ U, c ∈ A ++ B ++ C) → ∀ i,
      (U.getD i (TreeCircuit.const false)).maxFanin ≤ TreeCircuit.maxFaninL (A ++ B ++ C) :=
    fun U hU => maxFanin_getD_le fun c hc => TreeCircuit.maxFanin_le_maxFaninL (hU c hc)
  have hA := hf A fun c hc => List.mem_append_left _ (List.mem_append_left _ hc)
  have hB := hf B fun c hc => List.mem_append_left _ (List.mem_append_right _ hc)
  have hC := hf C fun c hc => List.mem_append_right _ hc
  -- Step 2: every output bit has fan-in at most `max 2 (maxFaninL (A ++ B ++ C))`
  rw [csaStep_eq]
  apply maxFaninL_le_of_forall
  intro c hc
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with ⟨i, -, rfl⟩ | rfl | ⟨i, -, rfl⟩
  · have := TreeCircuit.maxFanin_xor3_le (A.getD i (TreeCircuit.const false))
      (B.getD i (TreeCircuit.const false)) (C.getD i (TreeCircuit.const false))
    have := hA i; have := hB i; have := hC i
    omega
  · rw [TreeCircuit.maxFanin_const]
    omega
  · have := TreeCircuit.maxFanin_maj3_le (A.getD i (TreeCircuit.const false))
      (B.getD i (TreeCircuit.const false)) (C.getD i (TreeCircuit.const false))
    have := hA i; have := hB i; have := hC i
    omega

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

/-- One carry-save layer keeps the total:
`((csaLayer Us).map (val x)).sum = (Us.map (val x)).sum`.  Glue. -/
private theorem sum_csaLayer (x : Fin n → Bool) :
    ∀ Us : List (List (TreeCircuit n)), ((csaLayer Us).map (val x)).sum = (Us.map (val x)).sum
  | A :: B :: C :: Us => by
      rw [csaLayer_cons_cons_cons]
      simp only [List.map_cons, List.sum_cons]
      have h := csaStep_val x A B C
      rw [sum_csaLayer x Us]
      omega
  | [] | [_] | [_, _] => rfl

/-- One carry-save layer sends length `k` to `2 (k / 3) + k % 3`:
`(csaLayer Us).length = 2 * (Us.length / 3) + Us.length % 3`.  Glue. -/
private theorem length_csaLayer :
    ∀ Us : List (List (TreeCircuit n)),
      (csaLayer Us).length = 2 * (Us.length / 3) + Us.length % 3
  | A :: B :: C :: Us => by
      rw [csaLayer_cons_cons_cons]
      simp only [List.length_cons]
      rw [length_csaLayer Us]
      omega
  | [] | [_] | [_, _] => by
      rw [csaLayer_of_length_le_two (by simp only [List.length_cons, List.length_nil]; omega)]
      simp only [List.length_cons, List.length_nil]

/-- `j` layers send length `k` to the `j`-th iterate of `k ↦ 2 (k / 3) + k % 3`:
`(Nat.repeat csaLayer j Us).length = (fun k => 2 * (k / 3) + k % 3)^[j] Us.length`.  Glue. -/
private theorem length_repeat_csaLayer (Us : List (List (TreeCircuit n))) :
    ∀ j : ℕ, (Nat.repeat csaLayer j Us).length = (fun k => 2 * (k / 3) + k % 3)^[j] Us.length
  | 0 => rfl
  | j + 1 => by
      show (csaLayer (Nat.repeat csaLayer j Us)).length = _
      rw [length_csaLayer, length_repeat_csaLayer Us j, Function.iterate_succ_apply']

/-- After `csaLevels k` steps of `k ↦ 2 (k / 3) + k % 3` at most two numbers are left:
`(fun k => 2 * (k / 3) + k % 3)^[csaLevels k] k ≤ 2`.  Glue. -/
private theorem iterate_csaLevels_le_two (k : ℕ) :
    (fun k => 2 * (k / 3) + k % 3)^[csaLevels k] k ≤ 2 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      by_cases hk : k ≤ 2
      · rw [csaLevels_of_le_two hk, Function.iterate_zero_apply]
        exact hk
      · rw [csaLevels_of_two_lt (by omega), Function.iterate_succ_apply]
        exact ih _ (by omega)

/-- A member of a read-off number `Vs.getD i []` is a member of the flattened list:
`c ∈ Vs.getD i [] → c ∈ Vs.flatten`.  Glue. -/
private theorem mem_flatten_of_mem_getD {Vs : List (List (TreeCircuit n))} {i : ℕ}
    {c : TreeCircuit n} (h : c ∈ Vs.getD i []) : c ∈ Vs.flatten := by
  by_cases hi : i < Vs.length
  · rw [List.getD_eq_getElem Vs [] hi] at h
    exact List.mem_flatten_of_mem (List.getElem_mem hi) h
  · rw [List.getD_eq_default Vs [] (Nat.le_of_not_lt hi)] at h
    nomatch h

/-- One carry-save layer raises a common depth bound `d ≥ 1` of all formulas by at most `4`:
`1 ≤ d → (∀ c ∈ Us.flatten, c.depth ≤ d) → ∀ c ∈ (csaLayer Us).flatten, c.depth ≤ d + 4`.
Glue.

**Proof sketch.** Recursion along `csaLayer`'s cases.  For a triple `A, B, C`, the bound gives
`maxDepth (A ++ B ++ C) ≤ d` (`maxDepth_le_of_forall`), so both words of `csaStep A B C` lie
within `max 1 d + 4 = d + 4` (`depth_csaStep_le`, `depth_le_maxDepth`); the rest of the layer is
bounded by the recursive call.  A remainder of at most two numbers is kept unchanged. -/
private theorem depth_csaLayer_le {d : ℕ} (hd : 1 ≤ d) :
    ∀ Us : List (List (TreeCircuit n)), (∀ c ∈ Us.flatten, c.depth ≤ d) →
      ∀ c ∈ (csaLayer Us).flatten, c.depth ≤ d + 4
  | A :: B :: C :: Us, h => by
      have hABC : TreeCircuit.maxDepth (A ++ B ++ C) ≤ d := maxDepth_le_of_forall fun c hc => by
        refine h c ?_
        rw [List.flatten_cons, List.flatten_cons, List.flatten_cons, ← List.append_assoc,
          ← List.append_assoc]
        exact List.mem_append_left _ hc
      have hSK := depth_csaStep_le A B C
      have hUs := depth_csaLayer_le hd Us fun c hc => by
        refine h c ?_
        rw [List.flatten_cons, List.flatten_cons, List.flatten_cons]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hc))
      intro c hc
      rw [csaLayer_cons_cons_cons, List.flatten_cons, List.flatten_cons, ← List.append_assoc,
        List.mem_append] at hc
      rcases hc with hc | hc
      · have := TreeCircuit.depth_le_maxDepth hc
        omega
      · exact hUs c hc
  | [], h | [_], h | [_, _], h => fun c hc => (h c hc).trans (Nat.le_add_right d 4)

/-- One carry-save layer keeps a common fan-in bound `d ≥ 2` of all formulas:
`2 ≤ d → (∀ c ∈ Us.flatten, c.maxFanin ≤ d) → ∀ c ∈ (csaLayer Us).flatten, c.maxFanin ≤ d`.
Glue.

**Proof sketch.** As `depth_csaLayer_le`: for a triple, `maxFaninL (A ++ B ++ C) ≤ d`
(`maxFaninL_le_of_forall`) and `maxFaninL_csaStep_le` with `max 2 d = d` bound both words
(`maxFanin_le_maxFaninL`); the recursive call bounds the rest. -/
private theorem maxFanin_csaLayer_le {d : ℕ} (hd : 2 ≤ d) :
    ∀ Us : List (List (TreeCircuit n)), (∀ c ∈ Us.flatten, c.maxFanin ≤ d) →
      ∀ c ∈ (csaLayer Us).flatten, c.maxFanin ≤ d
  | A :: B :: C :: Us, h => by
      have hABC : TreeCircuit.maxFaninL (A ++ B ++ C) ≤ d := maxFaninL_le_of_forall fun c hc => by
        refine h c ?_
        rw [List.flatten_cons, List.flatten_cons, List.flatten_cons, ← List.append_assoc,
          ← List.append_assoc]
        exact List.mem_append_left _ hc
      have hSK := maxFaninL_csaStep_le A B C
      have hUs := maxFanin_csaLayer_le hd Us fun c hc => by
        refine h c ?_
        rw [List.flatten_cons, List.flatten_cons, List.flatten_cons]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hc))
      intro c hc
      rw [csaLayer_cons_cons_cons, List.flatten_cons, List.flatten_cons, ← List.append_assoc,
        List.mem_append] at hc
      rcases hc with hc | hc
      · have := TreeCircuit.maxFanin_le_maxFaninL hc
        omega
      · exact hUs c hc
  | [], h | [_], h | [_, _], h => h

/-- **F6, value.** The reduction keeps the total: for every assignment `x`,
`val x (csaReduce Us).1 + val x (csaReduce Us).2 = (Us.map (val x)).sum`.
[BV11, Lemma 4.5 proof, p029-b002]; *deviation:* the carry-save tree (r3 §H3.4).

**Proof sketch.** (1) One layer keeps the total, `((csaLayer Us).map (val x)).sum =
(Us.map (val x)).sum` (`sum_csaLayer`: recursion along `csaLayer`'s cases,
`csaLayer_cons_cons_cons`, with `csaStep_val` for each triple), hence so does every iterate
(induction on the number of layers, `Nat.repeat`).  (2) One layer sends length `k` to
`2 (k / 3) + k % 3` (`length_csaLayer`, the same recursion with `csaLayer_of_length_le_two`),
so `j` layers give the `j`-th iterate of that map (`length_repeat_csaLayer`).  (3) Induction on
`k` along `csaLevels_of_le_two`/`csaLevels_of_two_lt`: after `csaLevels k` steps of the map at
most two numbers are left (`iterate_csaLevels_le_two`).  (4) For a list of length at most two
the total is `getD 0 [] + getD 1 []`, as `val x [] = 0` (`val_eq`, `bitsVal` of `[]` is `0` by
`bitsVal_eq_prefixVal` and `prefixVal_zero`). -/
theorem csaReduce_val (x : Fin n → Bool) (Us : List (List (TreeCircuit n))) :
    val x (csaReduce Us).1 + val x (csaReduce Us).2 = (Us.map (val x)).sum := by
  -- Step 1: every iterate of the layer keeps the total
  have hsum : ∀ j, ((Nat.repeat csaLayer j Us).map (val x)).sum = (Us.map (val x)).sum := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        show ((csaLayer (Nat.repeat csaLayer j Us)).map (val x)).sum = _
        rw [sum_csaLayer, ih]
  -- Step 2: after `csaLevels |Us|` layers at most two numbers are left
  have hlen : (Nat.repeat csaLayer (csaLevels Us.length) Us).length ≤ 2 := by
    rw [length_repeat_csaLayer]
    exact iterate_csaLevels_le_two _
  -- Step 3: the empty number is `0`, and a list of at most two numbers is read off
  have hnil : val x [] = 0 := by
    rw [val_eq, List.map_nil, bitsVal_eq_prefixVal, List.length_nil, prefixVal_zero]
  rw [csaReduce_eq, ← hsum (csaLevels Us.length)]
  generalize Nat.repeat csaLayer (csaLevels Us.length) Us = Vs at hlen ⊢
  rcases Vs with _ | ⟨V₀, _ | ⟨V₁, _ | ⟨V₂, Vs⟩⟩⟩
  · simp only [List.getD_nil, List.map_nil, List.sum_nil, hnil, Nat.add_zero]
  · simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, hnil]
  · simp only [List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
  · simp only [List.length_cons] at hlen
    omega

/-- **F6, depth.** The two numbers lie at most `4 · csaLevels |Us|` levels above the inputs
(counted from at least `1`): `TreeCircuit.maxDepth ((csaReduce Us).1 ++ (csaReduce Us).2) ≤
max 1 (TreeCircuit.maxDepth Us.flatten) + 4 * csaLevels Us.length`.  r3's
"`depth ≤ 4·csaLevels k + d₀`" *(fix)*, settled with `d₀ = max 1 (input depth)`.  No term
depends on the bit length.

**Proof sketch.** With `D = max 1 (maxDepth Us.flatten)`: one layer raises a bound on the
depth of every formula by at most `4` (`depth_csaLayer_le`: `csaLayer`'s cases,
`depth_csaStep_le` for each triple, the kept remainder unchanged), so after `j` layers every
formula has depth `≤ D + 4 j` (induction on `j`, `Nat.repeat`); with `j = csaLevels |Us|` the
formulas of the two read-off numbers are formulas of the final list
(`mem_flatten_of_mem_getD`), and `maxDepth_le_of_forall` bounds the maximum. -/
theorem depth_csaReduce_le (Us : List (List (TreeCircuit n))) :
    TreeCircuit.maxDepth ((csaReduce Us).1 ++ (csaReduce Us).2) ≤
      max 1 (TreeCircuit.maxDepth Us.flatten) + 4 * csaLevels Us.length := by
  -- Step 1: `j` layers keep every formula within `D + 4 j`
  have hj : ∀ j, ∀ c ∈ (Nat.repeat csaLayer j Us).flatten,
      c.depth ≤ max 1 (TreeCircuit.maxDepth Us.flatten) + 4 * j := by
    intro j
    induction j with
    | zero =>
        intro c hc
        change c ∈ Us.flatten at hc
        exact (TreeCircuit.depth_le_maxDepth hc).trans (le_max_right _ _)
    | succ j ih =>
        intro c hc
        change c ∈ (csaLayer (Nat.repeat csaLayer j Us)).flatten at hc
        have := depth_csaLayer_le (by omega) _ ih c hc
        omega
  -- Step 2: the read-off numbers are members of the final list
  rw [csaReduce_eq]
  refine maxDepth_le_of_forall fun c hc => hj (csaLevels Us.length) c ?_
  rcases List.mem_append.1 hc with hc | hc
  · exact mem_flatten_of_mem_getD hc
  · exact mem_flatten_of_mem_getD hc

/-- **F6, fan-in two.** The reduction adds only fan-in-2 gates:
`TreeCircuit.maxFaninL ((csaReduce Us).1 ++ (csaReduce Us).2) ≤
max 2 (TreeCircuit.maxFaninL Us.flatten)`.  Glue.

**Proof sketch.** As `depth_csaReduce_le`, with `maxFaninL_csaStep_le` for each triple: the
bound `max 2 (maxFaninL Us.flatten)` on every formula is kept by every layer
(`maxFanin_csaLayer_le`), and `maxFaninL_le_of_forall` bounds the maximum. -/
theorem maxFaninL_csaReduce_le (Us : List (List (TreeCircuit n))) :
    TreeCircuit.maxFaninL ((csaReduce Us).1 ++ (csaReduce Us).2) ≤
      max 2 (TreeCircuit.maxFaninL Us.flatten) := by
  -- Step 1: every iterate keeps the bound `F = max 2 (maxFaninL Us.flatten)`
  have hj : ∀ j, ∀ c ∈ (Nat.repeat csaLayer j Us).flatten,
      c.maxFanin ≤ max 2 (TreeCircuit.maxFaninL Us.flatten) := by
    intro j
    induction j with
    | zero =>
        intro c hc
        change c ∈ Us.flatten at hc
        exact (TreeCircuit.maxFanin_le_maxFaninL hc).trans (le_max_right _ _)
    | succ j ih =>
        intro c hc
        change c ∈ (csaLayer (Nat.repeat csaLayer j Us)).flatten at hc
        exact maxFanin_csaLayer_le (le_max_left _ _) _ ih c hc
  -- Step 2: the read-off numbers are members of the final list
  rw [csaReduce_eq]
  refine maxFaninL_le_of_forall fun c hc => hj (csaLevels Us.length) c ?_
  rcases List.mem_append.1 hc with hc | hc
  · exact mem_flatten_of_mem_getD hc
  · exact mem_flatten_of_mem_getD hc

/-- **F6, the number of layers.** At most `2⌈log₂ k⌉` carry-save layers reduce `k` numbers to
two: `csaLevels k ≤ 2 * Nat.clog 2 k`.  Glue (r3 §H5.7, F6); r3's draft constant
`2⌈log₂ k⌉ + 3` *(fix)* is settled at `2⌈log₂ k⌉`, which holds (probe P10: kernel `decide`
for `k < 512` against a structural surrogate of `Nat.clog 2`, `#eval` for `k < 100000`).

**Proof sketch.** Strong induction on `k`.  For `k ≤ 2`, `csaLevels_of_le_two`.  For `k > 2`,
let `k₁ = 2 (k / 3) + k % 3`; if `k₁ ≤ 2` then `csaLevels k = 1 ≤ 2 ≤ 2⌈log₂ k⌉`.  Otherwise
`csaLevels k = csaLevels k₂ + 2` with `k₂ = 2 (k₁ / 3) + k₁ % 3` (`csaLevels_of_two_lt` twice),
and `k₂ ≤ ⌈k / 2⌉ = (k + 2 - 1) / 2` (by `omega`, for every `k > 2` with `k₁ > 2`), so
`⌈log₂ k₂⌉ + 1 ≤ ⌈log₂ k⌉` (`Nat.clog_mono_right`, `Nat.clog_of_two_le`) and the induction
hypothesis at `k₂ < k` closes it. -/
theorem csaLevels_le (k : ℕ) : csaLevels k ≤ 2 * Nat.clog 2 k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      by_cases hk : k ≤ 2
      · rw [csaLevels_of_le_two hk]
        exact Nat.zero_le _
      -- Step 1: one layer, `k₁ = 2 (k / 3) + k % 3`
      rw [csaLevels_of_two_lt (k := k) (by omega)]
      have hpos := Nat.clog_pos (b := 2) (n := k) (by norm_num) (by omega)
      by_cases hk₁ : 2 * (k / 3) + k % 3 ≤ 2
      · rw [csaLevels_of_le_two hk₁]
        omega
      -- Step 2: a second layer, `k₂ = 2 (k₁ / 3) + k₁ % 3 ≤ ⌈k / 2⌉`
      rw [csaLevels_of_two_lt (k := 2 * (k / 3) + k % 3) (by omega)]
      have h₂ : 2 * ((2 * (k / 3) + k % 3) / 3) + (2 * (k / 3) + k % 3) % 3 ≤ (k + 2 - 1) / 2 := by
        omega
      -- Step 3: `⌈log₂ k₂⌉ + 1 ≤ ⌈log₂ k⌉` and the induction hypothesis
      have hmono := Nat.clog_mono_right 2 h₂
      have hstep := Nat.clog_of_two_le (b := 2) (n := k) (by norm_num) (by omega)
      have hih := ih _ (lt_of_le_of_lt h₂ (by omega))
      omega

end FormulaArith

end BoolCircuit
