/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare

/-!
# Formula arithmetic: the modular interval sum

For public constants `a : Fin M → ℕ` with `a i < q` and an interval `[lo, hi) ⊆ [0, q)`, the
formula `FormulaArith.modSumInterval a q lo hi` on the bits `x : Fin M → Bool` tests
`(∑ i, x_i · a_i) mod q ∈ [lo, hi)`.  This is the decryption formula's core
([BV11, Lemma 4.5]; [BV14, Prop 3.4]): decryption is a binary subset sum of public constants
followed by an interval test (r3 §H3.2–H3.3).  The construction (r3 §H3.4):
1. masked constants `x_i · a_i`, each bit the literal `x_i` or the constant `false`;
2. the carry-save reduction of the `M` summands to two numbers `U, W` with `U + W = S`
   (`csaReduce`), trimmed to `⌈log₂ M⌉ + ⌈log₂ q⌉` bits (as `S < max M 1 · q`);
3. for each `j < max M 1` the two-sided test `j q + lo ≤ S < j q + hi` by two comparisons
   with constants (`geConst`), and
4. the `∨` over `j` by a balanced fan-in-2 tree.

Its depth is `O(log M + log log q)` with an explicit constant (`modSumDepth`) and no term
linear in `log q`: no Shannon, DNF or truth-table step touches a `log q`-bit value.

## Main definitions

* `BoolCircuit.FormulaArith.maskedConst` — the number `x_i · a` as a list of formulas.
* `BoolCircuit.FormulaArith.modSumInterval` — the modular interval-sum formula.
* `BoolCircuit.FormulaArith.modSumDepth` — its depth bound, in closed form over `csaLevels`.

## Main results

* `BoolCircuit.FormulaArith.modSumInterval_eval` — F9: the formula tests
  `lo ≤ (∑ i, x_i a_i) % q < hi` (target).
* `BoolCircuit.FormulaArith.depth_modSumInterval_le`, `modSumDepth_le`,
  `maxFanin_modSumInterval_le` — F10: depth at most
  `9⌈log₂ M⌉ + 2⌈log₂(⌈log₂ q⌉ + ⌈log₂ M⌉ + 3)⌉ + 21`, fan-in two (targets).

## References

* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011, pp. 97–106; full version, IACR ePrint 2011/344 (39 pages,
  2 March 2012), §4.5, Lemma 4.5 and its proof.
* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014,
  pp. 1–12; IACR ePrint 2013/541, §3.1, Proposition 3.4.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

namespace FormulaArith

variable {n : ℕ}

/-- The masked constant `x_i · a` as a `p`-bit little-endian number: bit `j` is the literal
`x_i` where `a` has a `1` and `const false` elsewhere,
`maskedConst i a p = (range p).map fun j => if a.testBit j then lit ⟨i, true⟩ else const false`,
of value `(x i).toNat * (a % 2 ^ p)`.  Glue (r3 §H3.4 item 1). -/
def maskedConst (i : Fin n) (a p : ℕ) : List (TreeCircuit n) :=
  (List.range p).map fun j =>
    if a.testBit j then TreeCircuit.lit ⟨i, true⟩ else TreeCircuit.const false

/-- The masked constant written out: `maskedConst i a p = (List.range p).map fun j =>
if a.testBit j then TreeCircuit.lit ⟨i, true⟩ else TreeCircuit.const false`. -/
theorem maskedConst_eq (i : Fin n) (a p : ℕ) :
    maskedConst i a p =
      (List.range p).map fun j =>
        if a.testBit j then TreeCircuit.lit ⟨i, true⟩ else TreeCircuit.const false := rfl

/-- The modular interval-sum formula on `M` bits `x`: with `B = ⌈log₂ q⌉` and
`w = ⌈log₂ M⌉ + ⌈log₂ q⌉`, let `(U, W) = csaReduce [maskedConst i (a i) B | i < M]` (so
`U + W = ∑ i, x_i a_i` when every `a i < q`), trimmed to `w` bits; then
`modSumInterval a q lo hi = ⋁_{j < max M 1} (geConst U W (j q + lo) ∧ ¬ geConst U W (j q + hi))`,
the `∨` a `balanced false` tree and `¬` the De Morgan `neg`.  It tests
`lo ≤ (∑ i, x_i a_i) % q < hi` (`modSumInterval_eval`).  [BV11, Lemma 4.5, p029-b001;
BV14, Prop 3.4, p011-b001]; deviations in `modSumInterval_eval`. -/
def modSumInterval {M : ℕ} (a : Fin M → ℕ) (q lo hi : ℕ) : TreeCircuit M :=
  let UW := csaReduce (List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q))
  let U := UW.1.take (Nat.clog 2 M + Nat.clog 2 q)
  let W := UW.2.take (Nat.clog 2 M + Nat.clog 2 q)
  TreeCircuit.balanced false ((List.range (max M 1)).map fun j =>
    TreeCircuit.and2 (geConst U W (j * q + lo)) (geConst U W (j * q + hi)).neg)

/-- The modular interval-sum formula written out: with
`UW = csaReduce (List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q))`,
`U = UW.1.take w`, `W = UW.2.take w` and `w = Nat.clog 2 M + Nat.clog 2 q`,
`modSumInterval a q lo hi = balanced false ((range (max M 1)).map fun j =>
and2 (geConst U W (j * q + lo)) (geConst U W (j * q + hi)).neg)`. -/
theorem modSumInterval_eq {M : ℕ} (a : Fin M → ℕ) (q lo hi : ℕ) :
    modSumInterval a q lo hi =
      TreeCircuit.balanced false ((List.range (max M 1)).map fun j =>
        TreeCircuit.and2
          (geConst
            ((csaReduce (List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q))).1.take
              (Nat.clog 2 M + Nat.clog 2 q))
            ((csaReduce (List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q))).2.take
              (Nat.clog 2 M + Nat.clog 2 q))
            (j * q + lo))
          (geConst
            ((csaReduce (List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q))).1.take
              (Nat.clog 2 M + Nat.clog 2 q))
            ((csaReduce (List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q))).2.take
              (Nat.clog 2 M + Nat.clog 2 q))
            (j * q + hi)).neg) := rfl

/-- A list of formulas has `maxDepth` at most `d` when every member has depth at most `d`:
`(∀ c ∈ cs, c.depth ≤ d) → TreeCircuit.maxDepth cs ≤ d`.  Glue. -/
private theorem maxDepth_le_of_forall {cs : List (TreeCircuit n)} {d : ℕ}
    (h : ∀ c ∈ cs, c.depth ≤ d) : TreeCircuit.maxDepth cs ≤ d := by
  induction cs with
  | nil => rw [TreeCircuit.maxDepth_nil]; exact Nat.zero_le d
  | cons c cs ih =>
      rw [TreeCircuit.maxDepth_cons]
      exact max_le (h c List.mem_cons_self) (ih fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- A list of formulas has `maxFaninL` at most `d` when every member has fan-in at most `d`:
`(∀ c ∈ cs, c.maxFanin ≤ d) → TreeCircuit.maxFaninL cs ≤ d`.  Glue. -/
private theorem maxFaninL_le_of_forall {cs : List (TreeCircuit n)} {d : ℕ}
    (h : ∀ c ∈ cs, c.maxFanin ≤ d) : TreeCircuit.maxFaninL cs ≤ d := by
  induction cs with
  | nil => rw [TreeCircuit.maxFaninL_nil]; exact Nat.zero_le d
  | cons c cs ih =>
      rw [TreeCircuit.maxFaninL_cons]
      exact max_le (h c List.mem_cons_self) (ih fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- The low `p` bits of `c` have value `c mod 2 ^ p`: `prefixVal c.testBit p = c % 2 ^ p`.
Glue. -/
private theorem prefixVal_testBit (c p : ℕ) : prefixVal c.testBit p = c % 2 ^ p := by
  induction p with
  | zero => rw [prefixVal_zero, pow_zero, Nat.mod_one]
  | succ p ih =>
      rw [prefixVal_succ, ih, Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]

/-- A masked constant has the value `x_i · a` when `a < 2 ^ p`:
`a < 2 ^ p → val x (maskedConst i a p) = (x i).toNat * a`.  Glue.

**Proof sketch.** The bits evaluate to those of `c = if x i then a else 0` (`maskedConst_eq`,
`eval_lit`, `Lit.eval_eq`, `const_eval`, `Nat.zero_testBit`); read the value through `val_eq`,
`bitsVal_eq_prefixVal`, `prefixVal_congr` and `prefixVal_testBit`, and `a % 2 ^ p = a`. -/
private theorem val_maskedConst (x : Fin n → Bool) (i : Fin n) {a p : ℕ} (ha : a < 2 ^ p) :
    val x (maskedConst i a p) = (x i).toNat * a := by
  -- Step 1: the bits are those of `c = if x i then a else 0`
  have hbits : ((maskedConst i a p).map fun c => c.eval x) =
      (List.range p).map (if x i = true then a else 0).testBit := by
    rw [maskedConst_eq, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    by_cases hj : a.testBit j
    · rw [Function.comp_apply, if_pos hj, TreeCircuit.eval_lit, Lit.eval_eq]
      by_cases hx : x i = true
      · rw [if_pos rfl, if_pos hx, hx, hj]
      · rw [if_pos rfl, if_neg hx, Nat.zero_testBit, Bool.eq_false_iff.2 hx]
    · rw [Function.comp_apply, if_neg hj, TreeCircuit.const_eval]
      by_cases hx : x i = true
      · rw [if_pos hx, Bool.eq_false_iff.2 hj]
      · rw [if_neg hx, Nat.zero_testBit]
  -- Step 2: read the value through `prefixVal`
  rw [val_eq, hbits, bitsVal_eq_prefixVal, List.length_map, List.length_range]
  rw [prefixVal_congr (g := (if x i = true then a else 0).testBit) fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some], prefixVal_testBit]
  by_cases hx : x i = true
  · rw [if_pos hx, hx, Bool.toNat_true, one_mul, Nat.mod_eq_of_lt ha]
  · rw [if_neg hx, Bool.eq_false_iff.2 hx, Bool.toNat_false, zero_mul, Nat.zero_mod]

/-- Bits above position `w` of a number below `2 ^ w` are zero:
`w ≤ m → prefixVal f m < 2 ^ w → prefixVal f m = prefixVal f w`.  Glue. -/
private theorem prefixVal_eq_of_lt_two_pow {f : ℕ → Bool} {w m : ℕ} (hwm : w ≤ m)
    (h : prefixVal f m < 2 ^ w) : prefixVal f m = prefixVal f w := by
  induction m, hwm using Nat.le_induction with
  | base => rfl
  | succ m hwm ih =>
      have h2 : 2 ^ w ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hwm
      rw [prefixVal_succ] at h ⊢
      rcases Bool.eq_false_or_eq_true (f m) with hf | hf
      · rw [hf, Bool.toNat_true, Nat.one_mul] at h
        omega
      · rw [hf, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at h ⊢
        exact ih h

/-- Trimming a formula number to `w` bits keeps its value when that value is below `2 ^ w`:
`val x U < 2 ^ w → val x (U.take w) = val x U`.  Glue. -/
private theorem val_take_of_lt (x : Fin n → Bool) {U : List (TreeCircuit n)} {w : ℕ}
    (h : val x U < 2 ^ w) : val x (U.take w) = val x U := by
  rcases le_total U.length w with hU | hU
  · rw [List.take_of_length_le hU]
  · rw [val_eq, bitsVal_eq_prefixVal] at h
    have hU' : w ≤ (U.map fun c => c.eval x).length := by rwa [List.length_map]
    rw [val_eq, val_eq, bitsVal_eq_prefixVal, bitsVal_eq_prefixVal, List.map_take,
      List.length_take, Nat.min_eq_left hU']
    refine (prefixVal_congr fun j hj => ?_).trans (prefixVal_eq_of_lt_two_pow hU' h).symm
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

/-- **F9. The modular interval sum.** For constants `a i < q` and `lo ≤ hi ≤ q`, the formula
tests whether the binary subset sum `∑ i, x_i · a_i` lies in `[lo, hi)` modulo `q`:
`(modSumInterval a q lo hi).eval x =
decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)`.
[BV11, Lemma 4.5, p029-b001; BV14, Prop 3.4, p011-b001].  *Deviations:* BV11 computes the bit
`(ŵ − ⟨v̂, ŝ⟩ mod p) mod 2` by subtracting all multiples of `p` and a selection tree; here the
output is the interval test that decryption's `decode` is (r3 §H3.2–H3.3, O2), the summands are
already the masked constants `x_i a_i` (BV11's `ŝ[i]^{(j)} · 2^j v̂[i]`), the summation is the
carry-save tree (r3 §H3.4), and the reduction mod `q` is an `∨` of two-sided comparisons with
the constants `j q + lo`, `j q + hi`.  The hypothesis `lo ≤ hi` is r3's; the probe finds the
equation true without it (`hi ≤ q` and `a i < q` are needed).

**Proof sketch.** (1) Each summand: `val x (maskedConst i (a i) B) = (x i).toNat * a i`
(`val_maskedConst`: `maskedConst_eq`, `eval_lit`, `Lit.eval_eq`, `const_eval`, `val_eq`,
`bitsVal_eq_prefixVal` and `prefixVal_testBit`, using `a i < q ≤ 2 ^ B`, `Nat.le_pow_clog`).  (2)
`csaReduce_val` and `List.sum_ofFn`: `val U + val W = S := ∑ i, (x i).toNat * a i`.  (3) `S ≤ M (q -
1) < 2 ^ w`, so both `val U, val W < 2 ^ w` and trimming to `w` bits keeps their values
(`val_take_of_lt`).  (4) `balanced_eval`, `eval_node_false`, `and2_eval`, `neg_eval`,
`geConst_eval`: the formula is `∃ j < max M 1, j q + lo ≤ S ∧ S < j q + hi`.  (5) Arithmetic: with
`j = S / q < max M 1` this is `lo ≤ S % q < hi`, and no other `j` qualifies since `hi ≤ q`
(`Nat.div_add_mod`). -/
theorem modSumInterval_eval {M : ℕ} {a : Fin M → ℕ} {q lo hi : ℕ} (ha : ∀ i, a i < q)
    (hlh : lo ≤ hi) (hhq : hi ≤ q) (x : Fin M → Bool) :
    (modSumInterval a q lo hi).eval x =
      decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi) := by
  set w := Nat.clog 2 M + Nat.clog 2 q with hw
  set Us := List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q) with hUs
  set S := ∑ i, (x i).toNat * a i with hS
  -- Step 1: each summand is a masked constant of value `x_i a_i`; `S ≤ M (q - 1)`
  have hq2 : ∀ i, a i < 2 ^ Nat.clog 2 q := fun i =>
    (ha i).trans_le (Nat.le_pow_clog (by norm_num) q)
  have hSle : S ≤ M * (q - 1) := by
    calc S ≤ ∑ _i : Fin M, (q - 1) := Finset.sum_le_sum fun i _ => by
            have := ha i
            have := Bool.toNat_le (x i)
            calc (x i).toNat * a i ≤ 1 * a i := Nat.mul_le_mul_right _ (Bool.toNat_le (x i))
              _ ≤ q - 1 := by omega
      _ = M * (q - 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- Step 2: the carry-save reduction keeps the sum
  have hsum : val x (csaReduce Us).1 + val x (csaReduce Us).2 = S := by
    rw [csaReduce_val, hUs, List.map_ofFn, List.sum_ofFn, hS]
    exact Finset.sum_congr rfl fun i _ => val_maskedConst x i (hq2 i)
  -- Step 3: `S < 2 ^ w`, so trimming to `w` bits keeps both values
  have hS2 : S < 2 ^ w := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · rw [hM, Nat.zero_mul] at hSle
      exact (Nat.le_zero.1 hSle).trans_lt (by positivity) |>.trans_le le_rfl
    · have hq : 0 < q := (Nat.zero_le _).trans_lt (ha ⟨0, hM⟩)
      calc S ≤ M * (q - 1) := hSle
        _ < M * q := Nat.mul_lt_mul_of_pos_left (by omega) hM
        _ ≤ 2 ^ Nat.clog 2 M * 2 ^ Nat.clog 2 q :=
            Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) M) (Nat.le_pow_clog (by norm_num) q)
        _ = 2 ^ w := by rw [hw, pow_add]
  have hV : val x ((csaReduce Us).1.take w) + val x ((csaReduce Us).2.take w) = S := by
    rw [val_take_of_lt x (U := (csaReduce Us).1) (w := w) (by omega),
      val_take_of_lt x (U := (csaReduce Us).2) (w := w) (by omega), hsum]
  -- Step 4: the formula is `∃ j < max M 1, j q + lo ≤ S ∧ ¬ j q + hi ≤ S`
  have hform : (modSumInterval a q lo hi).eval x = true ↔
      ∃ j < max M 1, j * q + lo ≤ S ∧ ¬ j * q + hi ≤ S := by
    rw [modSumInterval_eq, TreeCircuit.balanced_eval, TreeCircuit.eval_node_false_iff]
    constructor
    · rintro ⟨c, hc, hcx⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
      rw [TreeCircuit.and2_eval, Bool.and_eq_true, TreeCircuit.neg_eval, geConst_eval,
        geConst_eval, ← hUs, ← hw, hV, Bool.not_eq_true', decide_eq_true_iff,
        decide_eq_false_iff_not] at hcx
      exact ⟨j, List.mem_range.1 hj, hcx⟩
    · rintro ⟨j, hj, hjS⟩
      refine ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, ?_⟩
      rw [TreeCircuit.and2_eval, Bool.and_eq_true, TreeCircuit.neg_eval, geConst_eval,
        geConst_eval, ← hUs, ← hw, hV, Bool.not_eq_true', decide_eq_true_iff,
        decide_eq_false_iff_not]
      exact hjS
  -- Step 5: arithmetic, `j = S / q`
  rw [Bool.eq_iff_iff, hform, decide_eq_true_iff]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have hhi : hi = 0 := Nat.le_zero.1 hhq
    subst hhi
    constructor
    · rintro ⟨j, -, -, hj⟩
      exact absurd (by rw [Nat.mul_zero, Nat.add_zero]; exact Nat.zero_le S) hj
    · rintro ⟨-, h⟩
      exact absurd h (Nat.not_lt_zero _)
  · have hSq : S < max M 1 * q := by
      rcases Nat.eq_zero_or_pos M with hM | hM
      · rw [hM, Nat.zero_mul] at hSle
        rw [Nat.le_zero.1 hSle, hM, max_eq_right (Nat.zero_le 1), Nat.one_mul]
        exact hq
      · rw [max_eq_left hM]
        exact hSle.trans_lt (Nat.mul_lt_mul_of_pos_left (by omega) hM)
    have hdm := Nat.div_add_mod S q
    have hml := Nat.mod_lt S hq
    constructor
    · rintro ⟨j, -, hlo, hhi'⟩
      have hj : S / q = j := Nat.div_eq_of_lt_le (by omega)
        (by rw [Nat.add_mul, Nat.one_mul]; omega)
      rw [hj, Nat.mul_comm] at hdm
      constructor <;> omega
    · rintro ⟨hlo, hhi'⟩
      refine ⟨S / q, (Nat.div_lt_iff_lt_mul hq).2 hSq, ?_, ?_⟩
      · rw [Nat.mul_comm]; omega
      · rw [Nat.mul_comm]; omega

/-- The depth bound of the modular interval-sum formula on `M` summands modulo `q`:
`modSumDepth M q = 4 * csaLevels M + Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 M + Nat.clog 2 q + 1)
+ 10` (carry-save tree `1 + 4 csaLevels M`, comparison `+ 2⌈log₂(w + 1)⌉ + 7` with
`w = ⌈log₂ M⌉ + ⌈log₂ q⌉`, the `∧` `+1`, the `∨` over `max M 1` terms `+ ⌈log₂ M⌉ + 1`).
Glue. -/
def modSumDepth (M q : ℕ) : ℕ :=
  4 * csaLevels M + Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 M + Nat.clog 2 q + 1) + 10

/-- The depth bound written out: `modSumDepth M q = 4 * csaLevels M + Nat.clog 2 M +
2 * Nat.clog 2 (Nat.clog 2 M + Nat.clog 2 q + 1) + 10`. -/
theorem modSumDepth_eq (M q : ℕ) :
    modSumDepth M q =
      4 * csaLevels M + Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 M + Nat.clog 2 q + 1) + 10 :=
  rfl

/-- **F10, depth.** The modular interval-sum formula has depth at most `modSumDepth M q`, for
all constants and bounds: `(modSumInterval a q lo hi).depth ≤ modSumDepth M q`.
[BV11, Lemma 4.5, p029-b001: "fan-in 2 gates and O(log k + log log p) depth"; BV14, Prop 3.4,
p011-b001]; *deviation:* an explicit constant instead of `O(·)`.

**Proof sketch.** `modSumInterval_eq`.  The masked bits have depth `≤ 1` (`maskedConst_eq`,
`depth_lit`, `depth_const`), so `depth_csaReduce_le` bounds `U ++ W` by `1 + 4 csaLevels M` (the
summand list has length `M`, `List.length_ofFn`), and trimming does not increase it
(`List.mem_of_mem_take`, `depth_le_maxDepth`, `maxDepth_le_of_forall`).  As `|U|, |W| ≤ w`,
`depth_geConst_le` gives each comparison `≤ 4 csaLevels M + 8 + 2⌈log₂(w + 1)⌉`
(`Nat.clog_mono_right`), `depth_neg` keeps it, `depth_and2_le` adds `1`, and `depth_balanced_le`
over `max M 1` terms adds `⌈log₂ (max M 1)⌉ + 1 = ⌈log₂ M⌉ + 1`; the sum is `modSumDepth_eq`. -/
theorem depth_modSumInterval_le {M : ℕ} (a : Fin M → ℕ) (q lo hi : ℕ) :
    (modSumInterval a q lo hi).depth ≤ modSumDepth M q := by
  set w := Nat.clog 2 M + Nat.clog 2 q with hw
  set Us := List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q) with hUs
  set U := (csaReduce Us).1.take w with hU
  set W := (csaReduce Us).2.take w with hW
  -- Step 1: the masked bits have depth at most `1`, so the reduction is `≤ 1 + 4 csaLevels M`
  have hbits : TreeCircuit.maxDepth Us.flatten ≤ 1 := by
    refine maxDepth_le_of_forall fun c hc => ?_
    obtain ⟨V, hV, hcV⟩ := List.mem_flatten.1 hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hV
    rw [maskedConst_eq] at hcV
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hcV
    split
    · rw [TreeCircuit.depth_lit]; exact Nat.zero_le 1
    · rw [TreeCircuit.depth_const]
  have hred : TreeCircuit.maxDepth (U ++ W) ≤ 1 + 4 * csaLevels M := by
    have h := depth_csaReduce_le Us
    rw [hUs, List.length_ofFn, ← hUs, max_eq_left hbits] at h
    refine maxDepth_le_of_forall fun c hc => ?_
    refine le_trans (TreeCircuit.depth_le_maxDepth ?_) h
    rcases List.mem_append.1 hc with hc | hc
    · exact List.mem_append_left _ (List.mem_of_mem_take hc)
    · exact List.mem_append_right _ (List.mem_of_mem_take hc)
  -- Step 2: each comparison has depth `≤ 4 csaLevels M + 2⌈log₂ (w + 1)⌉ + 8`
  have hlen : max U.length W.length + 1 ≤ w + 1 :=
    Nat.add_le_add_right (max_le (List.length_take_le _ _) (List.length_take_le _ _)) 1
  have hcmp : ∀ c, (geConst U W c).depth ≤
      4 * csaLevels M + 2 * Nat.clog 2 (w + 1) + 8 := fun c => by
    have h1 := depth_geConst_le U W c
    have h2 := Nat.clog_mono_right 2 hlen
    have h3 : max 1 (TreeCircuit.maxDepth (U ++ W)) ≤ 1 + 4 * csaLevels M :=
      max_le (Nat.le_add_right 1 _) hred
    omega
  -- Step 3: the `∧`, then the balanced `∨` over `max M 1` terms
  rw [modSumInterval_eq, ← hUs, ← hw, ← hU, ← hW]
  refine (TreeCircuit.depth_balanced_le false _).trans ?_
  have hterms : TreeCircuit.maxDepth ((List.range (max M 1)).map fun j =>
      TreeCircuit.and2 (geConst U W (j * q + lo)) (geConst U W (j * q + hi)).neg) ≤
      4 * csaLevels M + 2 * Nat.clog 2 (w + 1) + 9 := by
    refine maxDepth_le_of_forall fun c hc => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    refine (TreeCircuit.depth_and2_le _ _).trans ?_
    rw [TreeCircuit.depth_neg]
    exact Nat.add_le_add_right (max_le (hcmp _) (hcmp _)) 1
  have hclog : Nat.clog 2 (max M 1) = Nat.clog 2 M := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · rw [hM, max_eq_right (Nat.zero_le 1), Nat.clog_one_right, Nat.clog_zero_right]
    · rw [max_eq_left hM]
  rw [List.length_map, List.length_range, hclog, modSumDepth_eq, ← hw]
  omega

/-- **F10, closed form.** The depth bound is `O(log M + log log q)` with no term linear in
`log q`: `modSumDepth M q ≤
9 * Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 3) + 21`.
[BV11, Lemma 4.5, p029-b001; BV14, Prop 3.4, p011-b001]; r3's draft closed form *(fix)*, kept:
the construction meets it with room (it gives `9⌈log₂ M⌉ + 2⌈log₂(⌈log₂ q⌉ + ⌈log₂ M⌉ + 1)⌉
+ 10`); checked numerically in probe P10.

**Proof sketch.** `modSumDepth_eq`; `csaLevels_le` gives `4 csaLevels M ≤ 8⌈log₂ M⌉`;
`Nat.clog_mono_right` gives
`⌈log₂(⌈log₂ M⌉ + ⌈log₂ q⌉ + 1)⌉ ≤ ⌈log₂(⌈log₂ q⌉ + ⌈log₂ M⌉ + 3)⌉`; then `omega`. -/
theorem modSumDepth_le (M q : ℕ) :
    modSumDepth M q ≤ 9 * Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 3) + 21 := by
  rw [modSumDepth_eq]
  have h1 := csaLevels_le M
  have h2 : Nat.clog 2 (Nat.clog 2 M + Nat.clog 2 q + 1) ≤
      Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 3) := Nat.clog_mono_right 2 (by omega)
  omega

/-- **F10, fan-in two.** The modular interval-sum formula has fan-in at most two:
`(modSumInterval a q lo hi).maxFanin ≤ 2`.  [BV11, Lemma 4.5, p029-b001: "fan-in 2 gates"].

**Proof sketch.** `modSumInterval_eq`; the masked bits have fan-in `0` (`maxFanin_lit`,
`maxFanin_const`), so `maxFaninL_csaReduce_le` gives `≤ 2` for `U ++ W` and for its
trimming; then `maxFanin_geConst_le`, `maxFanin_neg`, `maxFanin_and2_le` and
`maxFanin_balanced_le`. -/
theorem maxFanin_modSumInterval_le {M : ℕ} (a : Fin M → ℕ) (q lo hi : ℕ) :
    (modSumInterval a q lo hi).maxFanin ≤ 2 := by
  set w := Nat.clog 2 M + Nat.clog 2 q with hw
  set Us := List.ofFn fun i => maskedConst i (a i) (Nat.clog 2 q) with hUs
  set U := (csaReduce Us).1.take w
  set W := (csaReduce Us).2.take w
  -- the masked bits have fan-in `0`, so the reduction and its trimming have fan-in `≤ 2`
  have hbits : TreeCircuit.maxFaninL Us.flatten ≤ 0 := by
    refine maxFaninL_le_of_forall fun c hc => ?_
    obtain ⟨V, hV, hcV⟩ := List.mem_flatten.1 hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hV
    rw [maskedConst_eq] at hcV
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hcV
    split
    · rw [TreeCircuit.maxFanin_lit]
    · rw [TreeCircuit.maxFanin_const]
  have hred : TreeCircuit.maxFaninL (U ++ W) ≤ 2 := by
    have h := maxFaninL_csaReduce_le Us
    rw [Nat.le_zero.1 hbits, max_eq_left (Nat.zero_le 2)] at h
    refine maxFaninL_le_of_forall fun c hc => ?_
    refine le_trans (TreeCircuit.maxFanin_le_maxFaninL ?_) h
    rcases List.mem_append.1 hc with hc | hc
    · exact List.mem_append_left _ (List.mem_of_mem_take hc)
    · exact List.mem_append_right _ (List.mem_of_mem_take hc)
  have hcmp : ∀ c, (geConst U W c).maxFanin ≤ 2 := fun c =>
    (maxFanin_geConst_le U W c).trans (max_le le_rfl hred)
  rw [modSumInterval_eq, ← hUs, ← hw]
  refine (TreeCircuit.maxFanin_balanced_le false _).trans (max_le le_rfl ?_)
  refine maxFaninL_le_of_forall fun c hc => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  refine (TreeCircuit.maxFanin_and2_le _ _).trans (max_le le_rfl (max_le (hcmp _) ?_))
  rw [TreeCircuit.maxFanin_neg]
  exact hcmp _

end FormulaArith

end BoolCircuit

-- liveness control: reads `BoolCircuit.FormulaArith.val` through its body
example (x : Fin 2 → Bool) (U : List (BoolCircuit.TreeCircuit 2)) : BoolCircuit.FormulaArith.val x U = BoolCircuit.bitsVal (U.map fun c => c.eval x) :=
  rfl
