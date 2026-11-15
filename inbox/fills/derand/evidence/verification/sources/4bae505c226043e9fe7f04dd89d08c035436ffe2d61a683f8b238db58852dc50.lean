/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassP.BinaryArith.AddSub
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.ClassNP.PClosure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Word-level helpers for `BPL ⊆ P`

Polynomial-time word functions used by the dynamic program of [AB09, Exercise 7.9]
(`TCSlib.Complexity.Randomized.BPLInP`), built with the closure kit of
`TCSlib.Complexity.ClassP.BinaryArith`: the sum of an encoded list of binary numbers, the list
of the binary words of `0, …, V - 1` for a polynomial `V`, the binary window radius
`c · (|bits |x|| + 1)`, the binary word of `2^V`, and the tests of logspace languages.

## Main definitions

* `Randomized.BPLInP.sumW` — the sum of an encoded list of numbers.
* `Randomized.BPLInP.codesW` — the encoded list `bits 0, …, bits (B (|x| + 1)^e - 1)`.
* `Randomized.BPLInP.radius`, `Randomized.BPLInP.pow2W` — the radius and the word of `2^V`.

## Main results

* `Randomized.BPLInP.sumW_encWords`, `Randomized.BPLInP.polyTimeComputable_sumW`.
* `Randomized.BPLInP.codesW_eq`, `Randomized.BPLInP.polyTimeComputable_codesW`.
* `Randomized.BPLInP.polyTimeComputable_radius`, `Randomized.BPLInP.polyTimeComputable_pow2W`.
* `Randomized.BPLInP.polyTimeComputable_indicator_of_LOGSPACE` — a logspace language has a
  polynomial-time test.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.BPLInP

open Complexity Complexity.BinArith Turing
open Complexity.LogProg (bitsVal bitsVal_bits)

/-! ### Sums -/

/-- One round of the summation loop on `⟨acc, list⟩`: add the head entry to `acc`, drop it. -/
def sumStep (S : List Bool) : List Bool :=
  pairEncode (add (pairEncode (pairFstD S) (pairFstD (pairSndD S)))) (pairSndD (pairSndD S))

/-- The sum of the numbers of an encoded list: `|w| + 1` rounds of `sumStep` from `⟨0, w⟩`. -/
def sumW (w : List Bool) : List Bool :=
  pairFstD (sumStep^[1 * (w.length + 1) ^ 1] (pairEncode [] w))

/-- The rounds of the summation loop. -/
theorem iterate_sumStep (a : ℕ) (w : List Bool) (i : ℕ) :
    sumStep^[i] (pairEncode (Nat.bits a) w) = pairEncode
      (Nat.bits (a + ∑ j ∈ Finset.range i, bitsVal (pairFstD (pairSndD^[j] w))))
      (pairSndD^[i] w) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', Finset.sum_range_succ]
    simp [sumStep, add, bitsVal_bits, Nat.add_assoc]

/-- The summation loop sums an encoded list of numbers. -/
theorem iterate_sumStep_encWords (L : List ℕ) (a : ℕ) :
    sumStep^[L.length] (pairEncode (Nat.bits a) (encWords (L.map Nat.bits))) =
      pairEncode (Nat.bits (a + L.sum)) [] := by
  induction L generalizing a with
  | nil => simp
  | cons n L ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, encWords_cons]
    have : sumStep (pairEncode (Nat.bits a) (pairEncode (Nat.bits n) (encWords (L.map Nat.bits))))
        = pairEncode (Nat.bits (a + n)) (encWords (L.map Nat.bits)) := by
      simp [sumStep, add, bitsVal_bits]
    rw [this, ih, List.sum_cons, Nat.add_assoc]

/-- An encoded list of `k` words has at least `2k` letters. -/
theorem two_mul_length_le_encWords (L : List (List Bool)) : 2 * L.length ≤ (encWords L).length := by
  induction L with
  | nil => simp
  | cons w L ih => simp only [encWords_cons, length_pairEncode, List.length_cons]; omega

/-- **The sum loop sums**: on an encoded list of numbers it outputs the binary sum. -/
theorem sumW_encWords (L : List ℕ) : sumW (encWords (L.map Nat.bits)) = Nat.bits L.sum := by
  unfold sumW
  have hlen : L.length ≤ 1 * ((encWords (L.map Nat.bits)).length + 1) ^ 1 := by
    have := two_mul_length_le_encWords (L.map Nat.bits)
    rw [List.length_map] at this
    simp only [pow_one, one_mul]
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlen
  have hfix : sumStep (pairEncode (Nat.bits L.sum) []) = pairEncode (Nat.bits L.sum) [] := by
    simp [sumStep, add, bitsVal_bits, pairFstD_nil, show pairSndD ([] : List Bool) = [] from rfl,
      LogProg.bitsVal]
  rw [hd, Nat.add_comm, Function.iterate_add_apply, ← Nat.zero_bits,
    iterate_sumStep_encWords, Nat.zero_add, Function.iterate_fixed hfix, pairFstD_pairEncode]

/-- **The sum loop is polynomial-time.**

**Proof sketch.** It is `polyTimeComputable_iterate` of the round from `⟨0, w⟩`. After `i ≤ |w| + 1`
rounds the accumulator is a sum of at most `|w| + 1` numbers below `2^{|w|}`
(`iterate_sumStep`), so it has at most `2|w| + 1` digits, and the rest of the list is a
suffix of `w`. -/
theorem polyTimeComputable_sumW : PolyTimeComputable sumW := by
  have hstep : PolyTimeComputable sumStep :=
    (polyTimeComputable_add.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hinit : PolyTimeComputable (fun w : List Bool => pairEncode [] w) :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  refine polyTimeComputable_pairFstD.comp
    (polyTimeComputable_iterate hstep hinit 1 1 5 1 fun w i hi => ?_)
  rw [← Nat.zero_bits, iterate_sumStep, length_pairEncode]
  have hsum : 0 + ∑ j ∈ Finset.range i, bitsVal (pairFstD (pairSndD^[j] w)) <
      2 ^ (2 * w.length + 1) := by
    have hterm : ∀ j ∈ Finset.range i, bitsVal (pairFstD (pairSndD^[j] w)) ≤ 2 ^ w.length := by
      intro j _
      exact ((LogProg.bitsVal_lt_two_pow _).trans_le (Nat.pow_le_pow_right (by norm_num)
        ((length_pairFstD_le _).trans (length_iterate_pairSndD_le w j)))).le
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range,
      show ∀ a b : ℕ, a • b = a * b from fun _ _ => rfl] at h1
    have h2 : i ≤ 2 ^ w.length := by
      have := Nat.lt_two_pow_self (n := w.length); simp at hi; omega
    have h3 : i * 2 ^ w.length ≤ 2 ^ w.length * 2 ^ w.length := Nat.mul_le_mul_right _ h2
    have h4 : 2 ^ w.length * 2 ^ w.length < 2 ^ (2 * w.length + 1) := by
      rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hb := LogProg.length_bits_le hsum
  have hr := length_iterate_pairSndD_le w i
  simp only [pow_one] at hb hr ⊢
  omega

/-! ### The list of codes -/

/-- One round of the code-list loop on `⟨bits i, list⟩`: append `bits i`, increment `i`. -/
def codeStep (S : List Bool) : List Bool :=
  pairEncode (add (pairEncode (pairFstD S) [true])) (pairSndD S ++ pairEncode (pairFstD S) [])

/-- The rounds of the code-list loop. -/
theorem iterate_codeStep (i : ℕ) :
    codeStep^[i] (pairEncode [] []) =
      pairEncode (Nat.bits i) (encWords ((List.range i).map Nat.bits)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [codeStep, add, bitsVal_bits, List.range_succ, encWords_append_singleton,
      LogProg.bitsVal]

/-- The encoded list `bits 0, …, bits (B (|x| + 1)^e - 1)`. -/
def codesW (B e : ℕ) (x : List Bool) : List Bool :=
  pairSndD (codeStep^[B * (x.length + 1) ^ e] (pairEncode [] []))

/-- The code list lists the binary words below `B (|x| + 1)^e`. -/
theorem codesW_eq (B e : ℕ) (x : List Bool) :
    codesW B e x = encWords ((List.range (B * (x.length + 1) ^ e)).map Nat.bits) := by
  rw [codesW, iterate_codeStep, pairSndD_pairEncode]

/-- The encoded list of the binary words below `V` has length at most `V (2V + 2)`. -/
theorem length_encWords_range_le (V : ℕ) :
    (encWords ((List.range V).map Nat.bits)).length ≤ V * (2 * V + 2) := by
  have := length_encWords_le ((List.range V).map Nat.bits) V (by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
    exact (Turing.length_bits_le_self j).trans (List.mem_range.mp hj).le)
  simpa using this

/-- **The code list is polynomial-time.**

**Proof sketch.** `polyTimeComputable_iterate` of the round; after `i ≤ V` rounds the state is
`⟨bits i, bits 0, …, bits (i - 1)⟩` (`iterate_codeStep`), of length `O((V + 1)^2)`. -/
theorem polyTimeComputable_codesW (B e : ℕ) : PolyTimeComputable (codesW B e) := by
  have hstep : PolyTimeComputable codeStep :=
    (polyTimeComputable_add.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_const [true]))).pairEncode (polyTimeComputable_pairSndD.append
        (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_const [])))
  refine polyTimeComputable_pairSndD.comp (polyTimeComputable_iterate hstep
    (polyTimeComputable_const (pairEncode [] [])) B e (4 * (B + 1) ^ 2) (2 * e) fun x i hi => ?_)
  rw [iterate_codeStep, length_pairEncode]
  have h1 := Turing.length_bits_le_self i
  have h2 := length_encWords_range_le i
  have hP : i + 1 ≤ (B + 1) * (x.length + 1) ^ e := by
    have : 1 ≤ (x.length + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h3 : (i + 1) ^ 2 ≤ ((B + 1) * (x.length + 1) ^ e) ^ 2 := Nat.pow_le_pow_left hP 2
  have h4 : ((B + 1) * (x.length + 1) ^ e) ^ 2 = (B + 1) ^ 2 * (x.length + 1) ^ (2 * e) := by
    ring
  nlinarith

/-! ### The radius, powers of two, logspace tests -/

/-- The window radius `c · (|bits |x|| + 1)` in binary. -/
def radius (c : ℕ) (x : List Bool) : List Bool :=
  Nat.bits (c * ((Nat.bits x.length).length + 1))

/-- **The radius is polynomial-time.** -/
theorem polyTimeComputable_radius (c : ℕ) : PolyTimeComputable (radius c) := by
  have hlb : PolyTimeComputable (fun u : List Bool => Nat.bits u.length) :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits
  have hu : PolyTimeComputable
      (fun x : List Bool => List.replicate ((Nat.bits x.length).length + 1) true) := by
    have := (polyTimeComputable_unary.comp hlb).append (polyTimeComputable_const [true])
    simpa [Function.comp_def, List.replicate_succ'] using this
  have hc : ∀ c : ℕ, PolyTimeComputable
      (fun x : List Bool => List.replicate (c * ((Nat.bits x.length).length + 1)) true) := by
    intro c
    induction c with
    | zero => simpa using polyTimeComputable_const []
    | succ c ih => simpa [Nat.succ_mul, List.replicate_add] using ih.append hu
  have := hlb.comp (hc c)
  simpa [Function.comp_def, radius] using this

/-- The map writing a `0` for every letter. -/
def zerosW : List Bool → List Bool := transduce (fun (_ : Unit) _ => ()) (fun _ _ => some false) ()

/-- `zerosW w` is `0^{|w|}`. -/
theorem zerosW_eq (w : List Bool) : zerosW w = List.replicate w.length false := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [zerosW, transduce] at ih ⊢; simp [ih, List.replicate_succ]

/-- The binary word `0^V 1` of `2^V`, for `V = B (|x| + 1)^e`. -/
def pow2W (B e : ℕ) (x : List Bool) : List Bool :=
  zerosW (List.replicate (B * (x.length + 1) ^ e) true) ++ [true]

/-- The value of `pow2W` is `2^V`. -/
theorem bitsVal_pow2W (B e : ℕ) (x : List Bool) :
    bitsVal (pow2W B e x) = 2 ^ (B * (x.length + 1) ^ e) := by
  rw [pow2W, zerosW_eq, List.length_replicate]
  induction B * (x.length + 1) ^ e with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, LogProg.bitsVal, ih, pow_succ]; ring

/-- **The word of `2^V` is polynomial-time.** -/
theorem polyTimeComputable_pow2W (B e : ℕ) : PolyTimeComputable (pow2W B e) :=
  ((polyTimeComputable_transduce _ _ _).comp (polyTimeComputable_polyUnary B e)).append
    (polyTimeComputable_const [true])

/-- **A logspace language has a polynomial-time test** (`L ⊆ P`). -/
theorem polyTimeComputable_indicator_of_LOGSPACE {A : Language Bool} (h : A ∈ LOGSPACE) :
    PolyTimeComputable (fun z => [MultiTapeTM.indicator (A : Set (List Bool)) z]) :=
  mem_P_iff_polyTimeComputable.mp (LOGSPACE_subset_P h)

end Randomized.BPLInP
