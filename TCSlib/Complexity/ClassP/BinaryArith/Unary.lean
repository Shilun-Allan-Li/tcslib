/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.TuringMachine.Build.EmitIterBody
import Mathlib.Analysis.SpecificLimits.Normed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary width bounds and conversion to unary

The width of a canonical binary word bounds powers of two and fixed polynomials in that width by linear functions of its value. A finite emitting loop converts an arbitrary binary word to unary with a bound polynomial in the raw width times two to that width.

## Main definitions

The private countdown step takes a normalized binary predecessor, and its emission is one token at a positive state.

## Main results

* `polyTimeComputable_powerOfTwo` computes two to the input width in binary.
* `two_pow_width_le` and `exists_pow_width_bound` bound canonical widths.
* `exists_binaryToUnary` gives the finite conversion machine and its running time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

open Complexity Complexity.BinArith Complexity.LogProg Turing Turing.FinTM Filter

attribute [local irreducible] PolyTimeComputable FinTM.ComputesInTime FinTM.ComputesFunInTime
attribute [local irreducible] pairEncode BinArith.sub transduce

namespace Complexity.BinArith

/-- The binary word for the power of two indexed by a word's length. -/
theorem polyTimeComputable_powerOfTwo :
    PolyTimeComputable (fun z : List Bool => Nat.bits (2 ^ z.length)) := by
  let δ := fun (_ : Unit) (_ : Bool) => ()
  let emit := fun (_ : Unit) (_ : Bool) => some false
  have hzero (z : List Bool) : transduce δ emit () z = List.replicate z.length false := by
    induction z with
    | nil => rw [transduce_nil]; rfl
    | cons b z ih => rw [transduce_cons, show δ () b = () from rfl, ih]; rfl
  simpa only [hzero, bits_two_pow_eq_replicate] using
    (polyTimeComputable_transduce δ emit ()).append (polyTimeComputable_const [true])


/-- The binary width is small enough that its power-of-two bound is at most
twice the represented number plus two. -/
theorem two_pow_width_le (m : ℕ) : 2 ^ m.bits.length ≤ 2 * (m + 1) := by
  rw [Nat.size_eq_bits_len]
  cases he : m.size with
  | zero => simp only [pow_zero]; omega
  | succ k =>
      have h : 2 ^ k ≤ m := Nat.lt_size.mp (by omega)
      rw [pow_succ]
      omega

/-- Every fixed polynomial in the binary width is bounded by a linear
function of the represented number.

**Proof sketch.** A polynomial in the width is eventually at most two
to that width. Absorb the finitely many smaller widths into the constant
and apply the binary width bound. -/
theorem exists_pow_width_bound (e : ℕ) :
    ∃ A : ℕ, ∀ m : ℕ, (m.bits.length + 1) ^ e ≤ A * (m + 1) := by
  have hlim := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) e
    (by norm_num : 1 < (2 : ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Asymptotics.isLittleO_iff.mp hlim (by norm_num : (0 : ℝ) < 1))
  refine ⟨N ^ e + 4, fun m => ?_⟩
  by_cases hm : N ≤ m.bits.length + 1
  · have h := hN _ hm
    have hnonneg : 0 ≤ ((m.bits.length + 1 : ℕ) : ℝ) ^ e :=
      pow_nonneg (Nat.cast_nonneg _) _
    have htwo : 0 ≤ (2 : ℝ) ^ (m.bits.length + 1) := by positivity
    simp only [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg htwo, one_mul] at h
    have hpow : (m.bits.length + 1) ^ e ≤ 2 ^ (m.bits.length + 1) := by exact_mod_cast h
    have hwidth := two_pow_width_le m
    rw [pow_succ] at hpow
    rw [Nat.add_mul]
    omega
  · have h := Nat.pow_le_pow_left (by omega : m.bits.length + 1 ≤ N) e
    have hmul := Nat.mul_le_mul_left (N ^ e) (by omega : 1 ≤ m + 1)
    rw [Nat.mul_one] at hmul
    rw [Nat.add_mul]
    omega

/-- The next state of the unary emission loop is the normalized predecessor. -/
private def predWord (z : List Bool) : List Bool := Nat.bits (bitsVal z - 1)

/-- The predecessor is binary subtraction by one after normalization. -/
private theorem polyTimeComputable_predWord : PolyTimeComputable predWord := by
  convert polyTimeComputable_sub.comp
    (polyTimeComputable_normBits.pairEncode (polyTimeComputable_const (Nat.bits 1))) using 1
  funext z
  simp only [predWord, Function.comp_apply, sub_pairEncode]

/-- The loop emits one token exactly when its binary state is positive. -/
private def emitToken (z : List Bool) : List Bool := if z.any id then [true] else []

/-- A scan for a set bit decides whether to emit the single token. -/
private theorem polyTimeComputable_emitToken : PolyTimeComputable emitToken := by
  simpa only [emitToken] using polyTimeComputable_ite polyTimeComputable_any
    (polyTimeComputable_const [true]) (polyTimeComputable_const [])

/-- The orbit's value is the initial value minus the number of decrements. -/
private theorem predWord_iterate_value (z : List Bool) (i : ℕ) :
    bitsVal (predWord^[i] z) = bitsVal z - i := by
  induction i with
  | zero => simp only [Function.iterate_zero_apply, Nat.sub_zero]
  | succ i ih =>
      rw [Function.iterate_succ_apply', predWord, bitsVal_bits, ih]
      omega

/-- Each orbit state has at most the original word's binary width. -/
private theorem predWord_iterate_length (z : List Bool) (i : ℕ) :
    (predWord^[i] z).length ≤ z.length := by
  cases i with
  | zero => simp only [Function.iterate_zero_apply, le_refl]
  | succ i =>
      rw [Function.iterate_succ_apply', predWord, predWord_iterate_value]
      exact length_bits_le_of_le z (by omega) le_rfl

/-- On the orbit a token is emitted during exactly the positive countdown
rounds. -/
private theorem emitToken_iterate (z : List Bool) (i : ℕ) :
    emitToken (predWord^[i] z) = if i < bitsVal z then [true] else [] := by
  by_cases hi : i < bitsVal z
  · have hzero : (predWord^[i] z).any id ≠ false := by
      intro h
      have hv := (bitsVal_eq_zero_iff _).mpr h
      rw [predWord_iterate_value] at hv
      omega
    simp only [emitToken, if_pos hi, Bool.eq_true_of_not_eq_false hzero, ↓reduceIte]
  · have hzero := (bitsVal_eq_zero_iff (predWord^[i] z)).mp (by
      rw [predWord_iterate_value]
      omega)
    simp only [emitToken, if_neg hi, hzero, Bool.false_eq_true, ↓reduceIte]

/-- The first R rounds of an initial countdown of v emit exactly
the smaller of R and v tokens. -/
private theorem unary_chunks (R v : ℕ) :
    (List.range R).flatMap (fun i => if i < v then [true] else []) =
      List.replicate (min R v) true := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton]
      by_cases h : R < v
      · rw [if_pos h, Nat.min_eq_left h.le, Nat.min_eq_left (Nat.succ_le_of_lt h)]
        change List.replicate R true ++ List.replicate 1 true = _
        rw [← List.replicate_add]
      · rw [if_neg h, List.append_nil, Nat.min_eq_right (by omega : v ≤ R),
          Nat.min_eq_right (by omega : v ≤ R + 1)]

/-- A finite emitter converts binary to unary. Its time is polynomial in the
binary width times two to that width.

**Proof sketch.** The fuel machine emits the binary representation of two to
the input width. Instantiate the existing emit-iteration body with binary
predecessor and a token on each positive orbit state. The width remains
bounded throughout the orbit, and the binary fuel covers every possible
input value. -/
theorem exists_binaryToUnary : ∃ (M : FinTM Bool) (C c : ℕ),
    M.ComputesFunInTime (fun w => List.replicate (bitsVal w) true)
      (fun n => C * (n + 1) ^ c * (2 ^ n + 2)) := by
  have hfuel := polyTimeComputable_powerOfTwo
  obtain ⟨G, A, a, hG⟩ := (polyTimeComputable_iff _).1 polyTimeComputable_predWord
  obtain ⟨E, B, b, hE⟩ := (polyTimeComputable_iff _).1 polyTimeComputable_emitToken
  obtain ⟨F, K, k, hF⟩ := (polyTimeComputable_iff _).1 hfuel
  obtain ⟨M, C, c, hM⟩ := exists_emitIterTM_withFuel G E F predWord emitToken A a B b K k
    (fun n => 2 ^ n) hG hE hF 1 1 (fun w i => by
      simpa only [one_mul, pow_one] using (predWord_iterate_length w i).trans (Nat.le_succ _))
  refine ⟨M, C, c, (computesFunInTime_iff _ _ _).2 fun w => ?_⟩
  have h := (computesFunInTime_iff _ _ _).1 hM w
  rw [List.flatMap_congr (fun i _ => emitToken_iterate w i), unary_chunks,
    Nat.min_eq_right (by have := bitsVal_lt_two_pow w; omega)] at h
  exact h


end Complexity.BinArith
