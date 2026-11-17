/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
(`maskedConst_eq`, `eval_lit`, `const_eval`, `val_eq` and `bitsVal` against `Nat.testBit`,
using `a i < q ≤ 2 ^ B`, `Nat.le_pow_clog`).  (2) `csaReduce_val` and `List.sum_ofFn`:
`val U + val W = S := ∑ i, (x i).toNat * a i`.  (3) `S < max M 1 · q ≤ 2 ^ w`, so both
`val U, val W < 2 ^ w` and trimming to `w` bits keeps their values.  (4) `balanced_eval`,
`eval_node_false`, `and2_eval`, `neg_eval`, `geConst_eval`: the formula is
`∃ j < max M 1, j q + lo ≤ S ∧ S < j q + hi`.  (5) Arithmetic: with `j = S / q < max M 1`
this is `lo ≤ S % q < hi`, and no other `j` qualifies since `hi ≤ q` (`Nat.div_add_mod`). -/
theorem modSumInterval_eval {M : ℕ} {a : Fin M → ℕ} {q lo hi : ℕ} (ha : ∀ i, a i < q)
    (hlh : lo ≤ hi) (hhq : hi ≤ q) (x : Fin M → Bool) :
    (modSumInterval a q lo hi).eval x =
      decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi) := by
  sorry

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
depth of a literal `0` (reader missing, see the census), `depth_const`), so
`depth_csaReduce_le` bounds `U ++ W` by `1 + 4 csaLevels M` (the summand list has length `M`,
`List.length_ofFn`), and trimming does not increase it (`List.take` is a sublist;
`depth_le_maxDepth`).  As `|U|, |W| ≤ w`, `depth_geConst_le` gives each comparison
`≤ 4 csaLevels M + 8 + 2⌈log₂(w + 1)⌉` (`Nat.clog_mono_right`), `depth_neg` keeps it,
`depth_and2_le` adds `1`, and `depth_balanced_le` over `max M 1` terms adds
`⌈log₂ (max M 1)⌉ + 1 = ⌈log₂ M⌉ + 1`; the sum is `modSumDepth_eq`. -/
theorem depth_modSumInterval_le {M : ℕ} (a : Fin M → ℕ) (q lo hi : ℕ) :
    (modSumInterval a q lo hi).depth ≤ modSumDepth M q := by
  sorry

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
  sorry

/-- **F10, fan-in two.** The modular interval-sum formula has fan-in at most two:
`(modSumInterval a q lo hi).maxFanin ≤ 2`.  [BV11, Lemma 4.5, p029-b001: "fan-in 2 gates"].

**Proof sketch.** `modSumInterval_eq`; the masked bits have fan-in `0` (literal, reader
missing; `maxFanin_const`), so `maxFaninL_csaReduce_le` gives `≤ 2` for `U ++ W` and for its
trimming; then `maxFanin_geConst_le`, `maxFanin_neg`, `maxFanin_and2_le` and
`maxFanin_balanced_le`. -/
theorem maxFanin_modSumInterval_le {M : ℕ} (a : Fin M → ℕ) (q lo hi : ℕ) :
    (modSumInterval a q lo hi).maxFanin ≤ 2 := by
  sorry

end FormulaArith

end BoolCircuit
