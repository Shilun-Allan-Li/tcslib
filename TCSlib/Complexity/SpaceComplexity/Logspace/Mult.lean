/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multiplication in logarithmic space

[AB09, Example 4.7], second language: `MULT = {⟨n, m, nm⟩}` is in `L` by the
grade-school method. Deferred from phase P4.1 to P4.4
(`AroraBarakChapters3-4Plan.md`) for the number-triple encoding conventions,
which the logspace phase fixes: binary components in nested aligned pairs,
little-endian (`Nat.bits`), membership by existential witness over genuine
encodings — the same pattern as `Complexity.PATH`'s instance encoding.

## Main definitions

* `Complexity.multLang` — the triples `⟨a, b, a·b⟩`. [AB09, Example 4.7]

## Main results (proved; phase-P4.4 statement)

* `Complexity.multLang_mem_LOGSPACE` — grade-school multiplication runs in
  logarithmic space. [AB09, Example 4.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Example 4.7.)
-/

namespace Complexity

open Turing

/-- **The language `MULT`** [AB09, Example 4.7]: encodings of triples
`⟨a, b, a·b⟩`, components in little-endian binary, nested aligned pairs.
Strings encoding no such triple are not members. -/
def multLang : Language Bool :=
  {z | ∃ a b : ℕ,
    z = pairEncode (Nat.bits a) (pairEncode (Nat.bits b) (Nat.bits (a * b)))}

/-! ## Private multiplication construction (B7 target 12) -/

open LogProg
open scoped BigOperators

/-- The grade-school column sum, with absent operand bits read as zero. -/
private def multColumn (a b : List Bool) (j : ℕ) : ℕ :=
  ∑ p ∈ Finset.range a.length,
    if p ≤ j then (a.getD p false).toNat * (b.getD (j - p) false).toNat else 0

private lemma multColumn_nil (b : List Bool) (j : ℕ) : multColumn [] b j = 0 := by
  simp [multColumn]

private lemma multColumn_cons (t : Bool) (a b : List Bool) (j : ℕ) :
    multColumn (t :: a) b j = t.toNat * (b.getD j false).toNat +
      match j with
      | 0 => 0
      | k + 1 => multColumn a b k := by
  unfold multColumn
  rw [List.length_cons, Finset.sum_range_succ']
  cases j <;> simp [Nat.succ_sub_succ_eq_sub,
    Nat.add_comm]

/-- Every column has at most one contribution per bit of the first operand. -/
private lemma multColumn_le (a b : List Bool) (j : ℕ) : multColumn a b j ≤ a.length := by
  unfold multColumn
  calc
    _ ≤ ∑ _p ∈ Finset.range a.length, 1 := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · cases a.getD p false <;> cases b.getD (j-p) false <;> decide
      · omega
    _ = a.length := by simp

/-- A weighted prefix of zero-padded bits is the value of the corresponding word prefix. -/
private lemma mult_bits_prefix (w : List Bool) (n : ℕ) :
    (∑ j ∈ Finset.range n, 2 ^ j * (w.getD j false).toNat) = bitsVal (w.take n) := by
  induction n generalizing w with
  | zero => simp [bitsVal]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    cases w with
    | nil => simp [bitsVal, List.getD_eq_getElem?_getD]
    | cons t w =>
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul,
        List.take_succ_cons, bitsVal, pow_succ]
      calc
        _ = 2 * (∑ j ∈ Finset.range n, 2 ^ j * (w.getD j false).toNat) + t.toNat := by
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [ih]; omega

/-- Splitting off the low bit splits the convolution into a scalar row and a shifted product.
Proof sketch. Expand both prefixes at their first term and distribute the finite sums. -/
private lemma mult_column_prefix_cons (t : Bool) (a b : List Bool) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), 2 ^ j * multColumn (t :: a) b j) =
      t.toNat * bitsVal (b.take (n + 1)) +
        2 * (∑ j ∈ Finset.range n, 2 ^ j * multColumn a b j) := by
  rw [← mult_bits_prefix b (n + 1)]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [multColumn_cons, pow_zero, one_mul, Nat.add_zero]
  simp_rw [pow_succ, Nat.mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have h₁ : (∑ j ∈ Finset.range n, 2 ^ j * 2 *
      (t.toNat * (b.getD (j + 1) false).toNat)) =
      ∑ j ∈ Finset.range n, t.toNat * (2 ^ j * 2 * (b.getD (j + 1) false).toNat) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h₂ : (∑ j ∈ Finset.range n, 2 ^ j * 2 * multColumn a b j) =
      ∑ j ∈ Finset.range n, 2 * (2 ^ j * multColumn a b j) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [h₁, h₂]
  ring

/-- Once all possible columns are included, their weighted sum is the product.
Proof sketch. Induct on the first operand, using the preceding convolution decomposition
and the received definition of `bitsVal`; the length bound removes the second-word take. -/
private lemma mult_columns_value (a b : List Bool) (n : ℕ)
    (hn : a.length + b.length ≤ n) :
    (∑ j ∈ Finset.range n, 2 ^ j * multColumn a b j) = bitsVal a * bitsVal b := by
  induction a generalizing n with
  | nil => simp [multColumn_nil, bitsVal]
  | cons t a ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [mult_column_prefix_cons, List.take_of_length_le (by simp only [List.length_cons] at hn; omega),
        ih n (by simp only [List.length_cons] at hn; omega)]
      simp only [bitsVal]
      ring

/-- Carry entering a column; it starts at zero and is halved after the column is added. -/
private def multCarry (a b : List Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (multCarry a b j + multColumn a b j) / 2

/-- The carry never exceeds the first operand's bit length. -/
private lemma multCarry_le (a b : List Bool) (j : ℕ) : multCarry a b j ≤ a.length := by
  induction j with
  | zero => simp [multCarry]
  | succ j ih =>
    have hc := multColumn_le a b j
    simp only [multCarry]
    omega

/-- The exact column/carry invariant of [AB09, Example 4.7] (P4.4 audit, Q8).
Proof sketch. Add the next weighted column to the induction hypothesis. Euclidean
division splits the new accumulator into its parity and twice the next carry. -/
private lemma mult_carry_invariant (a b : List Bool) (n : ℕ) :
    (∑ j ∈ Finset.range n, 2 ^ j * multColumn a b j) =
      (∑ j ∈ Finset.range n,
        2 ^ j * ((multCarry a b j + multColumn a b j) % 2)) +
      2 ^ n * multCarry a b n := by
  induction n with
  | zero => simp [multCarry]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ, multCarry]
    have hd := Nat.mod_add_div (multCarry a b n + multColumn a b n) 2
    have he := congrArg (fun k => 2 ^ n * k) hd
    simp only [Nat.mul_add] at he
    simp only [Nat.mul_assoc]
    omega

/-- Binary digits and the carry beyond the last digit are uniquely determined by the
weighted sum, even for words with high zero padding.
Proof sketch. Compare both sums modulo two, cancel their equal low digits, divide by
two, and apply the induction hypothesis to the shifted digit functions. -/
private lemma mult_digits_unique (n k : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ j < n, f j < 2) (hg : ∀ j < n, g j < 2)
    (he : (∑ j ∈ Finset.range n, 2 ^ j * f j) + 2 ^ n * k =
      ∑ j ∈ Finset.range n, 2 ^ j * g j) :
    k = 0 ∧ ∀ j < n, f j = g j := by
  induction n generalizing f g with
  | zero => simpa using he
  | succ n ih =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at he
    simp only [pow_zero, one_mul, pow_succ] at he
    have shift (h : ℕ → ℕ) :
        (∑ j ∈ Finset.range n, 2 ^ j * 2 * h (j + 1)) =
        2 * ∑ j ∈ Finset.range n, 2 ^ j * h (j + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [shift f, shift g] at he
    have hpow : 2 ^ n * 2 * k = 2 * (2 ^ n * k) := by ring
    rw [hpow] at he
    have h₀ : f 0 = g 0 := by have := hf 0 (by omega); have := hg 0 (by omega); omega
    have htail : (∑ j ∈ Finset.range n, 2 ^ j * f (j + 1)) + 2 ^ n * k =
        ∑ j ∈ Finset.range n, 2 ^ j * g (j + 1) := by omega
    obtain ⟨hk, hs⟩ := ih (fun j => f (j + 1)) (fun j => g (j + 1))
      (fun j hj => hf (j + 1) (by omega)) (fun j hj => hg (j + 1) (by omega)) htail
    refine ⟨hk, ?_⟩
    intro j hj
    cases j with
    | zero => exact h₀
    | succ j => exact hs j (by omega)

/-- The finite column checks and final zero carry are exactly the product equation.
The result is zero-padded; its length need only be at most the sum of operand lengths.
Proof sketch. Apply digit uniqueness to the carry invariant and the product expansion.
In the other direction substitute the checked digits and zero carry in that invariant. -/
private lemma mult_columns_correct (a b c : List Bool)
    (hlen : c.length ≤ a.length + b.length) :
    bitsVal c = bitsVal a * bitsVal b ↔
      multCarry a b (a.length + b.length) = 0 ∧
      ∀ j < a.length + b.length,
        (c.getD j false).toNat = (multCarry a b j + multColumn a b j) % 2 := by
  have hv := mult_columns_value a b (a.length + b.length) le_rfl
  have hi := mult_carry_invariant a b (a.length + b.length)
  have hc := mult_bits_prefix c (a.length + b.length)
  rw [List.take_of_length_le hlen] at hc
  constructor
  · intro he
    have heq : (∑ j ∈ Finset.range (a.length + b.length),
        2 ^ j * ((multCarry a b j + multColumn a b j) % 2)) +
        2 ^ (a.length + b.length) * multCarry a b (a.length + b.length) =
        ∑ j ∈ Finset.range (a.length + b.length), 2 ^ j * (c.getD j false).toNat := by
      rw [← hi, hv, hc, he]
    obtain ⟨hzero, hd⟩ := mult_digits_unique _ _ _ _
      (fun j _ => Nat.mod_lt _ (by omega))
      (fun j _ => by cases c.getD j false <;> decide) heq
    exact ⟨hzero, fun j hj => (hd j hj).symm⟩
  · rintro ⟨hzero, hd⟩
    have hs : (∑ j ∈ Finset.range (a.length + b.length),
        2 ^ j * ((multCarry a b j + multColumn a b j) % 2)) = bitsVal c := by
      rw [← hc]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hd j (Finset.mem_range.mp hj)]
    rw [hv, hzero, Nat.mul_zero, Nat.add_zero, hs] at hi
    exact hi.symm

/-- A canonical product needs no more bits than the two operands combined, including zero. -/
private lemma mult_product_length (a b : ℕ) :
    (Nat.bits (a * b)).length ≤ (Nat.bits a).length + (Nat.bits b).length := by
  apply length_bits_le
  rw [pow_add]
  have ha : a < 2 ^ (Nat.bits a).length := by simpa [Nat.size_eq_bits_len] using Nat.lt_size_self a
  have hb : b < 2 ^ (Nat.bits b).length := by simpa [Nat.size_eq_bits_len] using Nat.lt_size_self b
  exact lt_of_le_of_lt (Nat.mul_le_mul_right b ha.le)
    (Nat.mul_lt_mul_of_pos_left hb (Nat.pow_pos (by omega)))

/-- The inner double loop has one possible nonzero summand, at the complementary index.
Proof sketch. If that index is in range, the single-term finite sum rule applies. Otherwise
every equality test fails and the zero-padded lookup is zero as well. -/
private lemma mult_column_row (t : Bool) (b : List Bool) (j p : ℕ) :
    (∑ q ∈ Finset.range b.length,
      if p + q = j then t.toNat * (b.getD q false).toNat else 0) =
    if p ≤ j then t.toNat * (b.getD (j - p) false).toNat else 0 := by
  by_cases hp : p ≤ j
  · rw [if_pos hp]
    by_cases hq : j - p < b.length
    · rw [Finset.sum_eq_single (j - p)]
      · simp [show p + (j-p) = j by omega]
      · intro q hq hne
        rw [if_neg (by omega)]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr hq))
    · have hzero : b.getD (j-p) false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : b.length ≤ j-p)]
      rw [hzero]
      simp only [Bool.toNat_false, Nat.mul_zero]
      apply Finset.sum_eq_zero
      intro q hmem
      rw [if_neg (by have := Finset.mem_range.mp hmem; omega)]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg (by omega)]

/-- The literal double loop computes the column used in the carry invariant. -/
private lemma mult_column_double (a b : List Bool) (j : ℕ) :
    (∑ p ∈ Finset.range a.length, ∑ q ∈ Finset.range b.length,
      if p + q = j then (a.getD p false).toNat * (b.getD q false).toNat else 0) =
      multColumn a b j := by
  unfold multColumn
  apply Finset.sum_congr rfl
  intro p hp
  exact mult_column_row (a.getD p false) b j p

/-- Contributions remaining in one inner loop, with an arbitrary starting diagonal index. -/
private def multRow (t : Bool) (b : List Bool) (j k : ℕ) : ℕ :=
  ∑ q ∈ Finset.range b.length,
    if k + q = j then t.toNat * (b.getD q false).toNat else 0

/-- Removing the next second-operand bit exposes one tested contribution. -/
private lemma multRow_cons (t u : Bool) (b : List Bool) (j k : ℕ) :
    multRow t (u :: b) j k =
      (if k = j then t.toNat * u.toNat else 0) + multRow t b j (k + 1) := by
  simp only [multRow, List.length_cons, Finset.sum_range_succ']
  simp [Nat.add_left_comm, Nat.add_comm]

/-- Only one second-operand index can contribute to a fixed row and column. -/
private lemma multRow_le_one (t : Bool) (b : List Bool) (j k : ℕ) : multRow t b j k ≤ 1 := by
  rw [multRow, mult_column_row]
  split_ifs
  · cases t <;> cases b.getD (j-k) false <;> decide
  · omega

/-- Remaining first-operand rows in a column, with an arbitrary starting first index. -/
private def multRows (a b : List Bool) (j p : ℕ) : ℕ :=
  ∑ q ∈ Finset.range a.length, multRow (a.getD q false) b j (p + q)

/-- The first row separates from the remaining outer loop. -/
private lemma multRows_cons (t : Bool) (a b : List Bool) (j p : ℕ) :
    multRows (t :: a) b j p = multRow t b j p + multRows a b j (p + 1) := by
  simp only [multRows, List.length_cons, Finset.sum_range_succ']
  simp [Nat.add_left_comm, Nat.add_comm]

/-- A remaining outer loop contributes at most one per remaining first-operand bit. -/
private lemma multRows_bound (a b : List Bool) (j p : ℕ) : multRows a b j p ≤ a.length := by
  calc
    _ ≤ ∑ _q ∈ Finset.range a.length, 1 := Finset.sum_le_sum (fun q _ => multRow_le_one _ _ _ _)
    _ = a.length := by simp

/-- Starting both loops at their first indices produces the convolution column. -/
private lemma multRows_column (a b : List Bool) (j : ℕ) : multRows a b j 0 = multColumn a b j := by
  simpa only [multRows, multRow, Nat.zero_add] using mult_column_double a b j

/-- Canonicality is decided from emptiness and the last bit, without storing the value. -/
private lemma mult_canonical_last (w : List Bool) :
    Canon w ↔ w.length = 0 ∨ w.getD (w.length - 1) false = true := by
  by_cases hw : w = []
  · subst w; simp [Canon]
  · have hn : 0 < w.length := List.length_pos_iff.mpr hw
    simp only [Canon, Nat.ne_of_gt hn, false_or]
    have hget : w.getD (w.length - 1) false = w.getLast hw := by
      simp [List.getLast_eq_getElem, List.getD_eq_getElem?_getD, show w.length - 1 < w.length by omega]
    rw [hget]
    exact ⟨fun h => h hw, fun h _ => h⟩

/-- Pair injectivity and canonical binary uniqueness identify the existential language
with the arithmetic predicate on the three parsed words. -/
private lemma mult_membership (a b c : List Bool) :
    pairEncode a (pairEncode b c) ∈ multLang ↔
      Canon a ∧ Canon b ∧ Canon c ∧ bitsVal c = bitsVal a * bitsVal b := by
  constructor
  · rintro ⟨u, v, he⟩
    obtain ⟨ha, hbc⟩ := Prod.mk.inj (pairEncode_injective he)
    obtain ⟨hb, hc⟩ := Prod.mk.inj (pairEncode_injective hbc)
    subst a; subst b; subst c
    exact ⟨canon_bits u, canon_bits v, canon_bits (u * v), by
      change bitsVal (Nat.bits (u * v)) = bitsVal (Nat.bits u) * bitsVal (Nat.bits v)
      simp only [bitsVal_bits]⟩
  · rintro ⟨ha, hb, hc, he⟩
    refine ⟨bitsVal a, bitsVal b, ?_⟩
    rw [← he, ← canon_eq_bits a ha, ← canon_eq_bits b hb, ← canon_eq_bits c hc]

/-- The complete arithmetic acceptance condition, including canonicality and excessive
result-length rejection, is equivalent to membership in `MULT`.
Proof sketch. Canonicality fixes each field to the binary representation of its value.
The product-length bound supplies the legal column count; `mult_columns_correct` supplies
exactly the parity comparisons and final carry test. -/
private lemma mult_acceptance (a b c : List Bool) :
    pairEncode a (pairEncode b c) ∈ multLang ↔
      Canon a ∧ Canon b ∧ Canon c ∧ c.length ≤ a.length + b.length ∧
      multCarry a b (a.length + b.length) = 0 ∧
      ∀ j < a.length + b.length,
        (c.getD j false).toNat = (multCarry a b j + multColumn a b j) % 2 := by
  rw [mult_membership]
  constructor
  · rintro ⟨ha, hb, hc, he⟩
    have hlen : c.length ≤ a.length + b.length := by
      rw [canon_eq_bits c hc, canon_eq_bits a ha, canon_eq_bits b hb, he]
      exact mult_product_length _ _
    exact ⟨ha, hb, hc, hlen, (mult_columns_correct a b c hlen).mp he⟩
  · rintro ⟨ha, hb, hc, hlen, hcheck⟩
    exact ⟨ha, hb, hc, (mult_columns_correct a b c hlen).mpr hcheck⟩

open LogProg Turing Classical

/-- Finite control for the multiplication verifier. The two shape scans have stride one.
Registers 0–12 hold: the first pointer, host length, second and third starts, first and
second ends, column count, current column, first index, second pointer, index sum,
carry/accumulator and result pointer. -/
private inductive MultState
  | lengthTest | lengthInc
  | pairTest (inner : Bool) | pairFirst (inner : Bool)
  | pairSecond (inner bit : Bool) | pairRead (inner bit : Bool)
  | pairAdvance (inner : Bool) (choice : Fin 4)
  | copy (stage : Fin 11) (bump : Bool)
  | endDown (inner second : Bool)
  | countHalf | countDown (second : Bool)
  | canonTest (field : Fin 3) | canonClear (field : Fin 3)
  | canonDown (field : Fin 3) (second : Bool) | canonRead (field : Fin 3)
  | column | clearA | clearP | outer | clearB | clearDiagonal | inner
  | diagonal | firstBit | secondBit | add
  | nextB (second : Bool) | nextDiagonal
  | nextA (second : Bool) | nextP
  | resultTest | resultRead | parity (bit : Bool)
  | carryHalf | nextColumn | nextResultTest | nextResult
  | finalPosition | finalCarry | answer (bit : Bool)
  deriving DecidableEq, Fintype

/-- Continuations of the two received shape scans. -/
private def multPairNext (inner : Bool) (choice : Fin 4) : MultState :=
  ![.pairSecond inner false, .pairSecond inner true, .pairTest inner,
    .copy (if inner then 1 else 0) false] choice

/-- Copy destinations, sources, and successful continuations. Every copy is the received
bounded counting fragment; the caller clears a reused destination before entering. -/
private def multCopy : Fin 11 → Fin 13 × Fin 13 × MultState :=
  ![(2, 0, .pairTest true), (3, 0, .copy 2 false),
    (4, 2, .endDown false false), (5, 3, .endDown true false),
    (6, 3, .countHalf),
    (0, 4, .canonDown 0 false), (0, 5, .canonDown 1 false),
    (0, 1, .canonDown 2 false), (12, 3, .column),
    (9, 2, .clearDiagonal), (10, 8, .inner)]

/-- The complete finite table for [AB09, Example 4.7]. All input reads are whole-mode
calls to the two proved input-access languages. No field value is stored. Two nested
loops enumerate operand positions in each column. The result pointer stops at its end,
so missing bits compare with zero; the final position test rejects an overlong result. -/
private def multARM : ARM 13 2 MultState
  | .lengthTest => .call 1 .whole [1] .lengthInc (.pairTest false)
  | .lengthInc => .inc 1 .lengthTest
  | .pairTest inner => .jeq 0 1 (.answer false) (.pairFirst inner)
  | .pairFirst inner => .call 0 .whole [0] (.pairAdvance inner 1) (.pairAdvance inner 0)
  | .pairSecond inner bit => .jeq 0 1 (.answer false) (.pairRead inner bit)
  | .pairRead inner bit => .call 0 .whole [0]
      (if bit then .pairAdvance inner 2 else .pairAdvance inner 3)
      (if bit then .answer false else .pairAdvance inner 2)
  | .pairAdvance inner choice => .inc 0 (multPairNext inner choice)
  | .copy stage false => .jeq (multCopy stage).1 (multCopy stage).2.1
      (multCopy stage).2.2 (.copy stage true)
  | .copy stage true => .inc (multCopy stage).1 (.copy stage false)
  | .endDown inner false => .dec (if inner then 5 else 4) (.endDown inner true)
  | .endDown inner true => .dec (if inner then 5 else 4) (.copy (if inner then 4 else 3) false)
  | .countHalf => .half 6 (.countDown false)
  | .countDown false => .dec 6 (.countDown true)
  | .countDown true => .dec 6 (.canonTest 0)
  | .canonTest f =>
      if f = 0 then .jz 4 (.canonTest 1) (.canonClear 0)
      else if f = 1 then .jeq 5 2 (.canonTest 2) (.canonClear 1)
      else .jeq 3 1 (.copy 8 false) (.canonClear 2)
  | .canonClear f => .clr 0 (.copy (if f = 0 then 5 else if f = 1 then 6 else 7) false)
  | .canonDown f second => .dec 0
      (if f = 2 ∨ second = true then .canonRead f else .canonDown f true)
  | .canonRead f => .call 0 .whole [0]
      (if f = 0 then .canonTest 1 else if f = 1 then .canonTest 2 else .copy 8 false)
      (.answer false)
  | .column => .jeq 7 6 .finalPosition .clearA
  | .clearA => .clr 0 .clearP
  | .clearP => .clr 8 .outer
  | .outer => .jeq 0 4 .resultTest .clearB
  | .clearB => .clr 9 (.copy 9 false)
  | .clearDiagonal => .clr 10 (.copy 10 false)
  | .inner => .jeq 9 5 (.nextA false) .diagonal
  | .diagonal => .jeq 10 7 .firstBit (.nextB false)
  | .firstBit => .call 0 .whole [0] .secondBit (.nextB false)
  | .secondBit => .call 0 .whole [9] .add (.nextB false)
  | .add => .inc 11 (.nextB false)
  | .nextB false => .inc 9 (.nextB true)
  | .nextB true => .inc 9 .nextDiagonal
  | .nextDiagonal => .inc 10 .inner
  | .nextA false => .inc 0 (.nextA true)
  | .nextA true => .inc 0 .nextP
  | .nextP => .inc 8 .outer
  | .resultTest => .jeq 12 1 (.parity false) .resultRead
  | .resultRead => .call 0 .whole [12] (.parity true) (.parity false)
  | .parity bit => .jodd 11 (if bit then .carryHalf else .answer false)
      (if bit then .answer false else .carryHalf)
  | .carryHalf => .half 11 .nextColumn
  | .nextColumn => .inc 7 .nextResultTest
  | .nextResultTest => .jeq 12 1 .column .nextResult
  | .nextResult => .inc 12 .column
  | .finalPosition => .jeq 12 1 .finalCarry (.answer false)
  | .finalCarry => .jz 11 (.answer true) (.answer false)
  | .answer bit => .ret bit

/-- The three physical addresses in the nested-pair layout, from the frozen common
pair lookup law. The result-field equation includes its zero padding. -/
private lemma mult_addresses (a b c : List Bool) :
    (∀ i < a.length, (pairEncode a (pairEncode b c)).getD (2 * i) false = a.getD i false) ∧
    (∀ i < b.length, (pairEncode a (pairEncode b c)).getD (2 * a.length + 2 + 2 * i) false =
      b.getD i false) ∧
    (∀ i, (pairEncode a (pairEncode b c)).getD (2 * a.length + 2 + 2 * b.length + 2 + i) false =
      c.getD i false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  · intro i hi
    rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 2 * a.length + 2 + 2 * i - 2 * a.length - 2 = 2 * i by omega]
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  · intro i
    rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 2 * a.length + 2 + 2 * b.length + 2 + i - 2 * a.length - 2 =
      2 * b.length + 2 + i by omega]
    rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1
    omega

/-- Conditions not yet checked at the start of column `j`. -/
private def MultRemaining (a b c : List Bool) (j : ℕ) : Prop :=
  c.length ≤ a.length + b.length ∧ multCarry a b (a.length + b.length) = 0 ∧
    ∀ i, j ≤ i → i < a.length + b.length →
      (c.getD i false).toNat = (multCarry a b i + multColumn a b i) % 2

/-- The residual acceptance condition separates into the next bit and the later columns. -/
private lemma mult_remaining_step (a b c : List Bool) (j : ℕ) (hj : j < a.length + b.length) :
    MultRemaining a b c j ↔
      (c.getD j false).toNat = (multCarry a b j + multColumn a b j) % 2 ∧
      MultRemaining a b c (j + 1) := by
  constructor
  · rintro ⟨hlen, hzero, hbits⟩
    exact ⟨hbits j le_rfl hj, hlen, hzero, fun i hi hin => hbits i (by omega) hin⟩
  · rintro ⟨hbit, hlen, hzero, hbits⟩
    refine ⟨hlen, hzero, ?_⟩
    intro i hi hin
    by_cases he : i = j
    · simpa only [he] using hbit
    · exact hbits i (by omega) hin

/-- Truthful access-bank oracle used throughout the run proof. -/
private noncomputable def multOracle : Fin 2 → List Bool → Bool :=
  fun k => MultiTapeTM.indicator ((![inputBitLang, inputLenLang] k : Language Bool) : Set (List Bool))

/-- Both genuine-query equations follow from the frozen index-language indicator law. -/
private lemma mult_queries (x : List Bool) (i : ℕ) :
    multOracle 0 (pairEncode x (Nat.bits i)) = x.getD i false ∧
    multOracle 1 (pairEncode x (Nat.bits i)) = decide (i < x.length) := by
  simp [multOracle, inputBitLang, inputLenLang, indicator_indexLang_pairEncode]

/-- All table instructions meet their syntactic side conditions for every input and
register assignment: comparisons use distinct registers and calls use one register. -/
private lemma mult_preconditions (x : List Bool) (s : MultState) (v : Fin 13 → ℕ)
    (o : Option Bool) : PreS multARM x (some s, v, o) := by
  cases s <;> simp only [PreS, multARM] <;> try decide
  case copy stage bump =>
    cases bump
    · exact (by decide : ∀ k, (multCopy k).1 ≠ (multCopy k).2.1) stage
    · trivial
  case canonTest field => split_ifs <;> simp
  case endDown inner second => cases second <;> trivial
  case countDown second => cases second <;> trivial
  case nextB second => cases second <;> trivial
  case nextA second => cases second <;> trivial

/-- The syntactic and numerical guard shared by all bounded multiplication paths. -/
private abbrev MultGood (x : List Bool) (a : AConf 13 MultState) :=
  PreS multARM x a ∧ ∀ r, a.2.1 r ≤ 4 * (x.length + 1)

/-- The received bounded path relation at the required linear register bound. -/
private abbrev MultReach (x : List Bool) :=
  AReach multARM multOracle x (MultGood x)

/-- The received bounded halting relation at the same bound. -/
private abbrev MultHalt (x : List Bool) :=
  AHalt multARM multOracle x (MultGood x)

/-- Every copy stage invokes the public bounded copy fragment. -/
private lemma mult_copy (x : List Bool) (k : Fin 11) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (ordered : v (multCopy k).1 ≤ v (multCopy k).2.1) :
    MultReach x (some (.copy k false), v, none)
      (some (multCopy k).2.2, Function.update v (multCopy k).1 (v (multCopy k).2.1), none) :=
  registerCopy_loop multARM multOracle x (multCopy k).1 (multCopy k).2.1
    ((by decide : ∀ k, (multCopy k).1 ≠ (multCopy k).2.1) k)
    (.copy k false) (.copy k true) (multCopy k).2.2 rfl rfl _ v bound ordered

/-- Both shape scans instantiate the same public aligned-pair validator. -/
private lemma mult_scan (x w : List Bool) (inner : Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) (endpos : v 1 = v 0 + w.length)
    (reads : ∀ j < w.length, x.getD (v 0 + j) false = w.getD j false) :
    match pairDecode w with
    | none => ∃ t ≤ w.length, MultReach x (some (.pairTest inner), v, none)
        (some (.answer false), Function.update v 0 (v 0 + t), none)
    | some (a, _) => MultReach x (some (.pairTest inner), v, none)
        (some (.copy (if inner then 1 else 0) false),
          Function.update v 0 (v 0 + (2 * a.length + 2)), none) := by
  let advance : Fin 4 → ℕ → MultState := fun k t =>
    if t = 0 then .pairAdvance inner k else multPairNext inner k
  have paths := alignedPair_loop multARM multOracle x 0 1 0
    (.pairTest inner) (.pairFirst inner) (.pairSecond inner) (.pairRead inner)
    (.answer false) (.copy (if inner then 1 else 0) false) advance 1
    (4 * (x.length + 1)) (by omega) (by decide) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun k i hi => by
      have hi0 : i = 0 := by omega
      subst i
      rfl)
    (by simp [advance, multPairNext]) w v bound (by simpa using endpos)
    (fun j hj => by simpa only [one_mul, (mult_queries x _).1] using reads j hj)
  simpa only [one_mul] using paths

/-- A tested pair contributes its product exactly when its two indices name the current
column. This path stops immediately after the possible increment, before the next loop step. -/
private lemma mult_contribution (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultReach x (some .diagonal, v, none)
      (some (.nextB false), Function.update v 11
        (v 11 + if v 10 = v 7 then
          (x.getD (v 0) false).toNat * (x.getD (v 9) false).toNat else 0), none) := by
  have good (s : MultState) : PreS multARM x (some s, v, none) ∧
      ∀ r, v r ≤ 4 * (x.length + 1) := ⟨mult_preconditions x s v none, bound⟩
  apply AReach.step (good .diagonal)
  simp only [astep, multARM]
  by_cases eq : v 10 = v 7
  · rw [if_pos eq, if_pos eq]
    apply AReach.step (good .firstBit)
    simp only [astep, multARM, vword_whole₁, (mult_queries x _).1]
    cases first : x.getD (v 0) false with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false,
        Nat.zero_mul, Nat.add_zero, Function.update_eq_self]
      exact AReach.refl _
    | true =>
      simp only [↓reduceIte, Bool.toNat_true, Nat.one_mul]
      apply AReach.step (good .secondBit)
      simp only [astep, multARM, vword_whole₁, (mult_queries x _).1]
      cases second : x.getD (v 9) false with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false,
          Nat.add_zero, Function.update_eq_self]
        exact AReach.refl _
      | true =>
        simp only [↓reduceIte, Bool.toNat_true]
        exact AReach.single (good .add)
  · simp only [if_neg eq, Nat.add_zero, Function.update_eq_self]
    exact AReach.refl _

/-- The inner operand loop terminates and adds exactly its row contribution, preserving
all other registers. The hypotheses bound the final accumulator and index; monotonicity
then bounds every intermediate increment.
Proof sketch. Induct on the remaining second-operand word. The diagonal and two oracle
reads give one contribution, then two pointer increments and one index increment expose
the tail. The empty word exits by the end-address comparison. -/
private lemma mult_inner_loop (x : List Bool) (bit : Bool) (w : List Bool)
    (v : Fin 13 → ℕ) (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (endpos : v 5 = v 9 + 2 * w.length)
    (first : x.getD (v 0) false = bit)
    (reads : ∀ q < w.length, x.getD (v 9 + 2 * q) false = w.getD q false)
    (indexBound : v 10 + w.length ≤ 4 * (x.length + 1))
    (sumBound : v 11 + multRow bit w (v 7) (v 10) ≤ 4 * (x.length + 1)) :
    MultReach x (some .inner, v, none)
      (some (.nextA false),
        Function.update (Function.update (Function.update v 9 (v 9 + 2 * w.length))
          10 (v 10 + w.length)) 11 (v 11 + multRow bit w (v 7) (v 10)), none) := by
  induction w generalizing v with
  | nil =>
    have ends : v 9 = v 5 := by simpa using endpos.symm
    simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero, multRow,
      Finset.range_zero, Finset.sum_empty, Function.update_eq_self, astep, multARM,
      if_pos ends] using (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some .inner, v, none)) ⟨mult_preconditions x .inner v none, bound⟩)
  | cons u w ih =>
    let delta := if v 10 = v 7 then bit.toNat * u.toNat else 0
    let va := Function.update v 11 (v 11 + delta)
    let v₁ := Function.update va 9 (v 9 + 1)
    let v₂ := Function.update va 9 (v 9 + 2)
    let vn := Function.update v₂ 10 (v 10 + 1)
    have cap : v 11 + delta + multRow bit w (v 7) (v 10 + 1) ≤ 4 * (x.length + 1) := by
      rw [multRow_cons] at sumBound
      dsimp [delta]
      omega
    have ba : ∀ r, va r ≤ 4 * (x.length + 1) := register_update_le v 11 _ _ bound (by omega)
    have b₁ : ∀ r, v₁ r ≤ 4 * (x.length + 1) := by
      apply register_update_le va 9 _ _ ba
      have := bound 5
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at endpos
      omega
    have b₂ : ∀ r, v₂ r ≤ 4 * (x.length + 1) := by
      apply register_update_le va 9 _ _ ba
      have := bound 5
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at endpos
      omega
    have bn : ∀ r, vn r ≤ 4 * (x.length + 1) := by
      apply register_update_le v₂ 10 _ _ b₂
      simp only [List.length_cons] at indexBound
      omega
    have headRead : x.getD (v 9) false = u := by simpa using reads 0 (by simp)
    have pairStep : MultReach x (some .diagonal, v, none) (some (.nextB false), va, none) := by
      simpa only [first, headRead] using mult_contribution x v bound
    have adv₁ : MultReach x (some (.nextB false), va, none) (some (.nextB true), v₁, none) :=
      AReach.single ⟨mult_preconditions x _ va none, ba⟩
    have adv₂ : MultReach x (some (.nextB true), v₁, none) (some .nextDiagonal, v₂, none) := by
      simpa [astep, multARM, v₁, v₂, Function.update_idem, Nat.add_assoc] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some (.nextB true), v₁, none)) ⟨mult_preconditions x _ v₁ none, b₁⟩)
    have adv₃ : MultReach x (some .nextDiagonal, v₂, none) (some .inner, vn, none) :=
      AReach.single ⟨mult_preconditions x _ v₂ none, b₂⟩
    have hnend : vn 5 = vn 9 + 2 * w.length := by
      simp [vn, v₂, va]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at endpos
      omega
    have hnfirst : x.getD (vn 0) false = bit := by simpa [vn, v₂, va] using first
    have hnreads : ∀ q < w.length, x.getD (vn 9 + 2 * q) false = w.getD q false := by
      intro q hq
      have hq' := reads (q + 1) (by simp; omega)
      simpa [vn, v₂, va, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hq'
    have hnindex : vn 10 + w.length ≤ 4 * (x.length + 1) := by
      simpa [vn, Nat.add_assoc, Nat.add_comm] using indexBound
    have hnsum : vn 11 + multRow bit w (vn 7) (vn 10) ≤ 4 * (x.length + 1) := by
      simpa [vn, v₂, va] using cap
    have rest := ih vn bn hnend hnfirst hnreads hnindex hnsum
    have endpoints : Function.update (Function.update (Function.update vn 9
        (vn 9 + 2 * w.length)) 10 (vn 10 + w.length))
        11 (vn 11 + multRow bit w (vn 7) (vn 10)) =
        Function.update (Function.update (Function.update v 9 (v 9 + 2 * (u :: w).length))
          10 (v 10 + (u :: w).length)) 11 (v 11 + multRow bit (u :: w) (v 7) (v 10)) := by
      simp [funext_iff, Fin.forall_fin_succ, Function.update_apply, vn, v₂, va,
        multRow_cons, delta, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [endpoints] at rest
    apply AReach.step ⟨mult_preconditions x .inner v none, bound⟩
    have hne : v 9 ≠ v 5 := by simp only [List.length_cons] at endpos; omega
    simpa only [astep, multARM, if_neg hne] using
      pairStep.trans (adv₁.trans (adv₂.trans (adv₃.trans rest)))

/-- Clear and restore the second pointer and diagonal index before an inner loop.
Both restorations invoke the single shared counting-copy proof. -/
private lemma mult_row_start (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultReach x (some .clearB, v, none)
      (some .inner, Function.update (Function.update v 9 (v 2)) 10 (v 8), none) := by
  let va := Function.update v 9 0
  let vb := Function.update v 9 (v 2)
  let vc := Function.update vb 10 0
  have ba : ∀ r, va r ≤ 4 * (x.length + 1) := register_update_le v 9 _ _ bound (Nat.zero_le _)
  have bb : ∀ r, vb r ≤ 4 * (x.length + 1) := register_update_le v 9 _ _ bound (bound 2)
  have bc : ∀ r, vc r ≤ 4 * (x.length + 1) := register_update_le vb 10 _ _ bb (Nat.zero_le _)
  have cp₁ : MultReach x (some (.copy 9 false), va, none) (some .clearDiagonal, vb, none) := by
    simpa [multCopy, va, vb] using mult_copy x 9 va ba (by simp [multCopy, va])
  have cp₂ : MultReach x (some (.copy 10 false), vc, none)
      (some .inner, Function.update vb 10 (v 8), none) := by
    simpa [multCopy, vc, vb] using mult_copy x 10 vc bc (by simp [multCopy, vc])
  apply AReach.step ⟨mult_preconditions x .clearB v none, bound⟩
  change MultReach x (some (.copy 9 false), va, none) _
  apply cp₁.trans
  apply AReach.step ⟨mult_preconditions x .clearDiagonal vb none, bb⟩
  exact cp₂

/-- The complete outer operand loop computes all remaining rows of one column.
Proof sketch. Reset the inner counters through the public copy fragment, apply the proved
inner loop to the next first-operand bit, and advance that bit's pointer and index. Induct
on the remaining first-operand word. The total remaining row sum bounds the accumulator
through each nested loop; the sum of remaining lengths bounds the index additions. -/
private lemma mult_outer_loop (x a b : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (enda : v 4 = v 0 + 2 * a.length) (endb : v 5 = v 2 + 2 * b.length)
    (readsa : ∀ p < a.length, x.getD (v 0 + 2 * p) false = a.getD p false)
    (readsb : ∀ q < b.length, x.getD (v 2 + 2 * q) false = b.getD q false)
    (indexBound : v 8 + a.length + b.length ≤ 4 * (x.length + 1))
    (sumBound : v 11 + multRows a b (v 7) (v 8) ≤ 4 * (x.length + 1)) :
    ∃ final : Fin 13 → ℕ,
      (∀ r, final r ≤ 4 * (x.length + 1)) ∧
      final 0 = v 0 + 2 * a.length ∧ final 8 = v 8 + a.length ∧
      final 11 = v 11 + multRows a b (v 7) (v 8) ∧
      (∀ r, r ≠ 0 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → final r = v r) ∧
      MultReach x (some .outer, v, none) (some .resultTest, final, none) := by
  induction a generalizing v with
  | nil =>
    refine ⟨v, bound, by simp, by simp, by simp [multRows], ?_, ?_⟩
    · intros; rfl
    · have he : v 0 = v 4 := by simpa using enda.symm
      simpa only [astep, multARM, if_pos he] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some .outer, v, none)) ⟨mult_preconditions x .outer v none, bound⟩)
  | cons t a ih =>
    let vs := Function.update (Function.update v 9 (v 2)) 10 (v 8)
    let ve := Function.update (Function.update (Function.update v 9 (v 2 + 2 * b.length))
      10 (v 8 + b.length)) 11 (v 11 + multRow t b (v 7) (v 8))
    let v₁ := Function.update ve 0 (v 0 + 1)
    let v₂ := Function.update ve 0 (v 0 + 2)
    let vn := Function.update v₂ 8 (v 8 + 1)
    have cap : v 11 + multRow t b (v 7) (v 8) + multRows a b (v 7) (v 8 + 1) ≤
        4 * (x.length + 1) := by rw [multRows_cons] at sumBound; omega
    have bs : ∀ r, vs r ≤ 4 * (x.length + 1) :=
      register_update_le _ 10 _ _ (register_update_le v 9 _ _ bound (bound 2)) (bound 8)
    have be : ∀ r, ve r ≤ 4 * (x.length + 1) := by
      apply register_update_le _ 11 _ _
      · apply register_update_le _ 10 _ _
        · apply register_update_le v 9 _ _ bound
          rw [← endb]; exact bound 5
        · simp only [List.length_cons] at indexBound; omega
      · omega
    have b₁ : ∀ r, v₁ r ≤ 4 * (x.length + 1) := by
      apply register_update_le ve 0 _ _ be
      have := bound 4
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at enda
      omega
    have b₂ : ∀ r, v₂ r ≤ 4 * (x.length + 1) := by
      apply register_update_le ve 0 _ _ be
      have := bound 4
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at enda
      omega
    have bn : ∀ r, vn r ≤ 4 * (x.length + 1) := by
      apply register_update_le v₂ 8 _ _ b₂
      simp only [List.length_cons] at indexBound; omega
    have starts := mult_row_start x v bound
    have inner := mult_inner_loop x t b vs bs
      (by simpa [vs] using endb)
      (by simpa [vs] using readsa 0 (by simp))
      (by simpa [vs] using readsb)
      (by simp [vs]; simp only [List.length_cons] at indexBound; omega)
      (by simp [vs]; omega)
    have innerEnd : Function.update (Function.update (Function.update vs 9
        (vs 9 + 2 * b.length)) 10 (vs 10 + b.length))
        11 (vs 11 + multRow t b (vs 7) (vs 10)) = ve := by
      simp [funext_iff, Fin.forall_fin_succ, Function.update_apply, vs, ve]
    rw [innerEnd] at inner
    have adv₁ : MultReach x (some (.nextA false), ve, none) (some (.nextA true), v₁, none) :=
      AReach.single ⟨mult_preconditions x _ ve none, be⟩
    have adv₂ : MultReach x (some (.nextA true), v₁, none) (some .nextP, v₂, none) := by
      simpa [astep, multARM, v₁, v₂, Function.update_idem, Nat.add_assoc] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some (.nextA true), v₁, none)) ⟨mult_preconditions x _ v₁ none, b₁⟩)
    have adv₃ : MultReach x (some .nextP, v₂, none) (some .outer, vn, none) :=
      AReach.single ⟨mult_preconditions x _ v₂ none, b₂⟩
    have hna : vn 4 = vn 0 + 2 * a.length := by
      simp [vn, v₂, ve]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at enda
      omega
    have hnb : vn 5 = vn 2 + 2 * b.length := by simpa [vn, v₂, ve] using endb
    have hnread : ∀ p < a.length, x.getD (vn 0 + 2 * p) false = a.getD p false := by
      intro p hp
      have h := readsa (p + 1) (by simp; omega)
      simpa [vn, v₂, ve, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have hnreadb : ∀ q < b.length, x.getD (vn 2 + 2 * q) false = b.getD q false := by
      simpa [vn, v₂, ve] using readsb
    have hni : vn 8 + a.length + b.length ≤ 4 * (x.length + 1) := by
      simpa [vn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using indexBound
    have hnc : vn 11 + multRows a b (vn 7) (vn 8) ≤ 4 * (x.length + 1) := by
      simpa [vn, v₂, ve] using cap
    obtain ⟨last, bl, la, lp, lc, frame, rest⟩ := ih vn bn hna hnb hnread hnreadb hni hnc
    refine ⟨last, bl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [vn, v₂, ve, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using la
    · simpa [vn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lp
    · simpa [vn, v₂, ve, multRows_cons, Nat.add_assoc] using lc
    · intro r r0 r8 r9 r10 r11
      rw [frame r r0 r8 r9 r10 r11]
      simp [vn, v₂, ve, Function.update_of_ne, r0, r8, r9, r10, r11]
    · apply AReach.step ⟨mult_preconditions x .outer v none, bound⟩
      have ne : v 0 ≠ v 4 := by simp only [List.length_cons] at enda; omega
      simpa only [astep, multARM, if_neg ne] using
        starts.trans (inner.trans (adv₁.trans (adv₂.trans (adv₃.trans rest))))

/-- Returning from a Boolean exit uses the received one-step halting rule. -/
private lemma mult_return (x : List Bool) (bit : Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultHalt x (some (.answer bit), v, none) bit :=
  AHalt.ret rfl ⟨mult_preconditions x (.answer bit) v none, bound⟩

/-- The final two tests accept exactly exhausted result input and zero carry. -/
private lemma mult_finish (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultHalt x (some .finalPosition, v, none) (decide (v 12 = v 1 ∧ v 11 = 0)) := by
  apply AHalt.step ⟨mult_preconditions x .finalPosition v none, bound⟩
  simp only [astep, multARM]
  by_cases hp : v 12 = v 1
  · rw [if_pos hp]
    apply AHalt.step ⟨mult_preconditions x .finalCarry v none, bound⟩
    simp only [astep, multARM]
    by_cases hc : v 11 = 0 <;> simpa [hp, hc] using mult_return x (decide (v 11 = 0)) v bound
  · simpa [hp] using mult_return x false v bound

/-- A parity test either reaches carry propagation or rejects the supplied result bit. -/
private lemma mult_parity (x : List Bool) (v : Fin 13 → ℕ) (bit : Bool)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    if bit.toNat = v 11 % 2 then
      MultReach x (some (.parity bit), v, none) (some .carryHalf, v, none)
    else MultHalt x (some (.parity bit), v, none) false := by
  have hmod := Nat.mod_lt (v 11) (by omega : 0 < 2)
  cases bit <;> by_cases odd : v 11 % 2 = 1
  all_goals simp only [Bool.toNat_false, Bool.toNat_true]
  · rw [if_neg (by omega)]
    apply AHalt.step ⟨mult_preconditions x _ v none, bound⟩
    simpa [astep, multARM, odd] using mult_return x false v bound
  · rw [if_pos (by omega)]
    simpa [astep, multARM, odd] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some (.parity false), v, none)) ⟨mult_preconditions x _ v none, bound⟩)
  · rw [if_pos odd.symm]
    simpa [astep, multARM, odd] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some (.parity true), v, none)) ⟨mult_preconditions x _ v none, bound⟩)
  · rw [if_neg (by omega)]
    apply AHalt.step ⟨mult_preconditions x _ v none, bound⟩
    simpa [astep, multARM, odd] using mult_return x false v bound

/-- At the result end the next bit is zero; otherwise the access bank reads it. -/
private lemma mult_result_read (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) (length : v 1 = x.length) :
    MultReach x (some .resultTest, v, none)
      (some (.parity (x.getD (v 12) false)), v, none) := by
  apply AReach.step ⟨mult_preconditions x .resultTest v none, bound⟩
  simp only [astep, multARM]
  by_cases hp : v 12 = v 1
  · have hzero : x.getD (v 12) false = false := by
      simp [hp, length, List.getD_eq_getElem?_getD]
    rw [if_pos hp, hzero]
    exact AReach.refl _
  · rw [if_neg hp]
    cases hb : x.getD (v 12) false <;>
      simpa only [astep, multARM, vword_whole₁, (mult_queries x _).1,
        hb, Bool.false_eq_true, ↓reduceIte] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (G := fun a => PreS multARM x a ∧ ∀ r, a.2.1 r ≤ 4 * (x.length + 1))
        (a := (some .resultRead, v, none)) ⟨mult_preconditions x _ v none, bound⟩)

/-- Carry halving and bounded cursor advancement prepare the next column. The result
pointer saturates at the input end rather than requiring equal operand/product lengths. -/
private lemma mult_next_column (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) (position : v 12 ≤ v 1)
    (columnBound : v 7 + 1 ≤ 4 * (x.length + 1)) :
    MultReach x (some .carryHalf, v, none)
      (some .column, Function.update (Function.update (Function.update v 11 (v 11 / 2))
        7 (v 7 + 1)) 12 (min (v 12 + 1) (v 1)), none) := by
  let vh := Function.update v 11 (v 11 / 2)
  let vi := Function.update vh 7 (v 7 + 1)
  have bh : ∀ r, vh r ≤ 4 * (x.length + 1) :=
    register_update_le v 11 _ _ bound ((Nat.div_le_self _ _).trans (bound 11))
  have bi : ∀ r, vi r ≤ 4 * (x.length + 1) := register_update_le vh 7 _ _ bh columnBound
  apply AReach.step ⟨mult_preconditions x .carryHalf v none, bound⟩
  change MultReach x (some .nextColumn, vh, none) _
  apply AReach.step ⟨mult_preconditions x .nextColumn vh none, bh⟩
  change MultReach x (some .nextResultTest, vi, none) _
  apply AReach.step ⟨mult_preconditions x .nextResultTest vi none, bi⟩
  simp only [astep, multARM]
  have vp : vi 12 = v 12 := by simp [vi, vh]
  have vl : vi 1 = v 1 := by simp [vi, vh]
  rw [vp, vl]
  by_cases hp : v 12 = v 1
  · rw [if_pos hp, min_eq_right (by omega)]
    have he : Function.update vi 12 (v 1) = vi := by rw [← hp, ← vp, Function.update_eq_self]
    rw [show Function.update (Function.update v 11 (v 11 / 2)) 7 (v 7 + 1) = vi by rfl, he]
    exact AReach.refl _
  · rw [if_neg hp, min_eq_left (by omega)]
    simpa only [astep, multARM, vp] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some .nextResult, vi, none)) ⟨mult_preconditions x _ vi none, bi⟩)

/-- All remaining multiplication columns halt with exactly their residual arithmetic
acceptance condition, within the required linear register bound.
Proof sketch. Induct on the number of remaining columns. The nested operand loops compute
one column, the zero-padded result read supplies its comparison bit, and parity success
halves the accumulator and advances the cursors. At the last column the saturated result
pointer tests excessive length and the accumulator tests final carry. -/
private lemma mult_columns_run (x a b c : List Bool)
    (encoded : x = pairEncode a (pairEncode b c)) (j : ℕ)
    (hj : j ≤ a.length + b.length) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (layout : v 1 = x.length ∧ v 2 = 2 * a.length + 2 ∧ v 4 = 2 * a.length ∧
      v 5 = 2 * a.length + 2 + 2 * b.length ∧ v 6 = a.length + b.length)
    (column : v 7 = j) (carry : v 11 = multCarry a b j)
    (result : v 12 = 2 * a.length + 2 + 2 * b.length + 2 + min j c.length) :
    MultHalt x (some .column, v, none) (decide (MultRemaining a b c j)) := by
  have size : x.length = 2 * a.length + 2 + 2 * b.length + 2 + c.length := by
    rw [encoded, length_pairEncode, length_pairEncode]; omega
  generalize hrem : a.length + b.length - j = remaining
  induction remaining using Nat.strong_induction_on generalizing j v with
  | h remaining ih =>
    by_cases done : j = a.length + b.length
    · apply AHalt.step ⟨mult_preconditions x .column v none, bound⟩
      simp only [astep, multARM, column, layout.2.2.2.2, if_pos done]
      have finish := mult_finish x v bound
      have exactTest : (v 12 = v 1 ∧ v 11 = 0) ↔ MultRemaining a b c j := by
        rw [result, layout.1, size, carry, done]
        simp only [MultRemaining]
        constructor
        · rintro ⟨hpos, hz⟩
          exact ⟨by omega, hz, fun i hi hn => by omega⟩
        · rintro ⟨hlen, hz, _⟩
          exact ⟨by omega, hz⟩
      simpa only [exactTest] using finish
    · have before : j < a.length + b.length := by omega
      let vs := Function.update (Function.update v 0 0) 8 0
      have bs : ∀ r, vs r ≤ 4 * (x.length + 1) :=
        register_update_le _ 8 _ 0 (register_update_le v 0 _ 0 bound (Nat.zero_le _)) (Nat.zero_le _)
      have reset : MultReach x (some .clearA, v, none) (some .outer, vs, none) := by
        apply AReach.step ⟨mult_preconditions x .clearA v none, bound⟩
        apply AReach.single
        exact ⟨mult_preconditions x .clearP _ none,
          register_update_le v 0 _ 0 bound (Nat.zero_le _)⟩
      have outer := mult_outer_loop x a b vs bs
        (by simp [vs, layout.2.2.1])
        (by simp [vs, layout.2.1, layout.2.2.2.1])
        (by simpa [vs, encoded] using (mult_addresses a b c).1)
        (by simpa [vs, layout.2.1, encoded] using (mult_addresses a b c).2.1)
        (by simp [vs]; omega)
        (by
          simp only [vs, Function.update_of_ne (by decide : (11 : Fin 13) ≠ 8),
            Function.update_of_ne (by decide : (11 : Fin 13) ≠ 0),
            Function.update_of_ne (by decide : (7 : Fin 13) ≠ 8),
            Function.update_of_ne (by decide : (7 : Fin 13) ≠ 0), Function.update_self,
            multRows_column, column, carry]
          have := multCarry_le a b j
          have := multColumn_le a b j
          omega)
      obtain ⟨ve, be, _, _, accum, frame, operands⟩ := outer
      have fixed (r : Fin 13) (safe : r ≠ 0 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 11) : ve r = v r := by
        rw [frame r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2]
        simp [vs, safe.1, safe.2.1]
      have e1 := fixed 1 (by decide)
      have e2 := fixed 2 (by decide)
      have e4 := fixed 4 (by decide)
      have e5 := fixed 5 (by decide)
      have e6 := fixed 6 (by decide)
      have e7 := fixed 7 (by decide)
      have e12 := fixed 12 (by decide)
      have esum : ve 11 = multCarry a b j + multColumn a b j := by
        simpa [vs, column, carry, multRows_column] using accum
      have elen : ve 1 = x.length := e1.trans layout.1
      have epos : ve 12 ≤ ve 1 := by rw [e12, result, elen, size]; omega
      have ebit : x.getD (ve 12) false = c.getD j false := by
        rw [e12, result, encoded, (mult_addresses a b c).2.2]
        by_cases hc : j ≤ c.length
        · rw [min_eq_left hc]
        · rw [min_eq_right (by omega)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : c.length ≤ j)]
      have reader := mult_result_read x ve be elen
      rw [ebit] at reader
      have parity := mult_parity x ve (c.getD j false) be
      by_cases agree : (c.getD j false).toNat = (multCarry a b j + multColumn a b j) % 2
      · rw [if_pos (by rwa [esum])] at parity
        have next := mult_next_column x ve be epos (by rw [e7, column]; omega)
        let vn := Function.update (Function.update (Function.update ve 11 (ve 11 / 2))
          7 (ve 7 + 1)) 12 (min (ve 12 + 1) (ve 1))
        have bn : ∀ r, vn r ≤ 4 * (x.length + 1) := by
          apply register_update_le _ 12 _ _
          · apply register_update_le _ 7 _ _
            · exact register_update_le ve 11 _ _ be ((Nat.div_le_self _ _).trans (be 11))
            · rw [e7, column]; omega
          · exact (Nat.min_le_right _ _).trans (be 1)
        have ln : vn 1 = x.length ∧ vn 2 = 2 * a.length + 2 ∧ vn 4 = 2 * a.length ∧
            vn 5 = 2 * a.length + 2 + 2 * b.length ∧ vn 6 = a.length + b.length := by
          simpa [vn, e1, e2, e4, e5, e6] using layout
        have jn : vn 7 = j + 1 := by simp [vn, e7, column]
        have cn : vn 11 = multCarry a b (j + 1) := by simp [vn, esum, multCarry]
        have rn : vn 12 = 2 * a.length + 2 + 2 * b.length + 2 + min (j + 1) c.length := by
          simp only [vn, Function.update_self]
          rw [e12, result, elen, size]
          omega
        have rest := ih (a.length + b.length - (j + 1)) (by omega)
          (j + 1) (by omega) vn bn ln jn cn rn rfl
        have exactNext : MultRemaining a b c j ↔ MultRemaining a b c (j + 1) := by
          rw [mult_remaining_step a b c j before]
          simp only [agree, true_and]
        rw [← exactNext] at rest
        apply AHalt.step ⟨mult_preconditions x .column v none, bound⟩
        simpa only [astep, multARM, column, layout.2.2.2.2, if_neg done] using
          reset.halt (operands.halt (reader.halt (parity.halt (next.halt rest))))
      · rw [if_neg (by rwa [esum])] at parity
        have reject : decide (MultRemaining a b c j) = false := by
          apply decide_eq_false
          rw [mult_remaining_step a b c j before]
          exact fun h => agree h.1
        rw [reject]
        apply AHalt.step ⟨mult_preconditions x .column v none, bound⟩
        simpa only [astep, multARM, column, layout.2.2.2.2, if_neg done] using
          reset.halt (operands.halt (reader.halt parity))

/-- Source register, shared-copy stage, and successful exit for each last-bit check. -/
private def multCanonSource (f : Fin 3) : Fin 13 := ![4, 5, 1] f

/-- Shared counting-copy stage selected by the canonical field. -/
private def multCanonCopy (f : Fin 3) : Fin 11 := if f = 0 then 5 else if f = 1 then 6 else 7

/-- Successful continuation selected by the canonical field. -/
private def multCanonNext (f : Fin 3) : MultState :=
  if f = 0 then .canonTest 1 else if f = 1 then .canonTest 2 else .copy 8 false

/-- The shared nonempty-field path reads its last physical bit. The first two fields are
strided by two and the third by one. The proof never decodes any field numerically.
Proof sketch. Clear the scratch pointer, invoke the received counting-copy loop, decrement
by the field stride, and make one input-bit query. All scratch values are at most the
source boundary, so the original register bound is preserved. -/
private lemma mult_last_bit (x : List Bool) (f : Fin 3) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultReach x (some (.canonClear f), v, none)
      (some (if x.getD (v (multCanonSource f) - (if f = 2 then 1 else 2)) false
        then multCanonNext f else .answer false),
        Function.update v 0 (v (multCanonSource f) - (if f = 2 then 1 else 2)), none) := by
  have srcne : multCanonSource f ≠ 0 := (by decide : ∀ f, multCanonSource f ≠ 0) f
  have spec : multCopy (multCanonCopy f) = (0, multCanonSource f, .canonDown f false) :=
    (by decide : ∀ f, multCopy (multCanonCopy f) = (0, multCanonSource f, .canonDown f false)) f
  let va := Function.update v 0 0
  let vs := Function.update v 0 (v (multCanonSource f))
  let vd := Function.update v 0 (v (multCanonSource f) - (if f = 2 then 1 else 2))
  have ba : ∀ r, va r ≤ 4 * (x.length + 1) := register_update_le v 0 _ _ bound (Nat.zero_le _)
  have bs : ∀ r, vs r ≤ 4 * (x.length + 1) := register_update_le v 0 _ _ bound (bound _)
  have bd : ∀ r, vd r ≤ 4 * (x.length + 1) :=
    register_update_le v 0 _ _ bound ((Nat.sub_le _ _).trans (bound _))
  have copies : MultReach x (some (.copy (multCanonCopy f) false), va, none)
      (some (.canonDown f false), vs, none) := by
    simpa [spec, va, vs, srcne] using
      mult_copy x (multCanonCopy f) va ba (by simp [spec, va, srcne])
  have down : MultReach x (some (.canonDown f false), vs, none) (some (.canonRead f), vd, none) := by
    by_cases last : f = 2
    · simpa [astep, multARM, last, vs, vd] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some (.canonDown f false), vs, none)) ⟨mult_preconditions x _ vs none, bs⟩)
    · let vm := Function.update v 0 (v (multCanonSource f) - 1)
      have bm : ∀ r, vm r ≤ 4 * (x.length + 1) :=
        register_update_le v 0 _ _ bound ((Nat.sub_le _ _).trans (bound _))
      have first : MultReach x (some (.canonDown f false), vs, none)
          (some (.canonDown f true), vm, none) := by
        simpa [astep, multARM, last, vs, vm] using
          (AReach.single (A := multARM) (oracle := multOracle) (x := x)
            (a := (some (.canonDown f false), vs, none)) ⟨mult_preconditions x _ vs none, bs⟩)
      apply first.trans
      simpa [astep, multARM, last, vm, vd, Nat.sub_sub] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some (.canonDown f true), vm, none)) ⟨mult_preconditions x _ vm none, bm⟩)
  have read : MultReach x (some (.canonRead f), vd, none)
      (some (if x.getD (v (multCanonSource f) - (if f = 2 then 1 else 2)) false
        then multCanonNext f else .answer false), vd, none) := by
    simpa only [astep, multARM, vword_whole₁, (mult_queries x _).1,
      vd, Function.update_self, multCanonNext] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some (.canonRead f), vd, none)) ⟨mult_preconditions x _ vd none, bd⟩)
  apply AReach.step ⟨mult_preconditions x (.canonClear f) v none, bound⟩
  exact copies.trans (down.trans read)

/-- Canonical-field validation in continuation form. The only changed register is the
scratch pointer. Empty fields represent zero; nonempty fields are accepted exactly when
the physical last bit is true. The caller supplies the field-specific address equations. -/
private lemma mult_validate_field (x w : List Bool) (f : Fin 3) (v : Fin 13 → ℕ)
    (answer : Bool) (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (emptyStep : astep multARM multOracle x (some (.canonTest f), v, none) =
      (some (if w = [] then multCanonNext f else .canonClear f), v, none))
    (lastRead : w ≠ [] →
      x.getD (v (multCanonSource f) - (if f = 2 then 1 else 2)) false =
        w.getD (w.length - 1) false)
    (failure : ¬ Canon w → answer = false)
    (success : Canon w → ∀ u : Fin 13 → ℕ,
      (∀ r, u r ≤ 4 * (x.length + 1)) → (∀ r, r ≠ 0 → u r = v r) →
      MultHalt x (some (multCanonNext f), u, none) answer) :
    MultHalt x (some (.canonTest f), v, none) answer := by
  apply AHalt.step ⟨mult_preconditions x (.canonTest f) v none, bound⟩
  rw [emptyStep]
  by_cases empty : w = []
  · rw [if_pos empty]
    exact success (by simp [empty, Canon]) v bound (fun _ _ => rfl)
  · rw [if_neg empty]
    let u := Function.update v 0 (v (multCanonSource f) - (if f = 2 then 1 else 2))
    have bu : ∀ r, u r ≤ 4 * (x.length + 1) :=
      register_update_le v 0 _ _ bound ((Nat.sub_le _ _).trans (bound _))
    have frame : ∀ r, r ≠ 0 → u r = v r := fun r hr => Function.update_of_ne hr _ _
    have last := mult_last_bit x f v bound
    rw [lastRead empty] at last
    have canon : Canon w ↔ w.getD (w.length - 1) false = true := by
      rw [mult_canonical_last]
      simp only [List.length_eq_zero_iff, empty, false_or]
    by_cases valid : Canon w
    · rw [canon.mp valid, if_pos rfl] at last
      exact last.halt (success valid u bu frame)
    · have bit : w.getD (w.length - 1) false = false := by
        cases hb : w.getD (w.length - 1) false
        · rfl
        · exact False.elim (valid (canon.mpr hb))
      rw [bit, if_neg Bool.false_ne_true] at last
      rw [failure valid]
      exact last.halt (mult_return x false u bu)

/-- Phase-boundary metadata after shape parsing and before the three canonicality checks. -/
private structure MultReady (x a b c : List Bool) (v : Fin 13 → ℕ) : Prop where
  length : v 1 = x.length
  startB : v 2 = 2 * a.length + 2
  startC : v 3 = 2 * a.length + 2 + 2 * b.length + 2
  endA : v 4 = 2 * a.length
  endB : v 5 = 2 * a.length + 2 + 2 * b.length
  rounds : v 6 = a.length + b.length
  column : v 7 = 0
  carry : v 11 = 0
  result : v 12 = 0

/-- Canonicality checks preserve all metadata because they change only the scratch pointer. -/
private lemma mult_ready_frame {x a b c : List Bool} {v u : Fin 13 → ℕ}
    (ready : MultReady x a b c v) (frame : ∀ r, r ≠ 0 → u r = v r) :
    MultReady x a b c u :=
  ⟨(frame 1 (by decide)).trans ready.length, (frame 2 (by decide)).trans ready.startB,
    (frame 3 (by decide)).trans ready.startC, (frame 4 (by decide)).trans ready.endA,
    (frame 5 (by decide)).trans ready.endB, (frame 6 (by decide)).trans ready.rounds,
    (frame 7 (by decide)).trans ready.column, (frame 11 (by decide)).trans ready.carry,
    (frame 12 (by decide)).trans ready.result⟩

/-- The three canonicality checks followed by the proved column loop decide a parsed triple.
Proof sketch. Each field check calls the common last-bit path, accepting the empty word.
Failure excludes the existential language by pair injectivity. On success copy the result
start, run all columns from zero carry, and use the pure acceptance equivalence. -/
private lemma mult_canonical_run (x a b c : List Bool)
    (encoded : x = pairEncode a (pairEncode b c)) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) (ready : MultReady x a b c v) :
    MultHalt x (some (.canonTest 0), v, none) (decide (x ∈ multLang)) := by
  have size : x.length = 2 * a.length + 2 + 2 * b.length + 2 + c.length := by
    rw [encoded, length_pairEncode, length_pairEncode]; omega
  have member : x ∈ multLang ↔ Canon a ∧ Canon b ∧ Canon c ∧ MultRemaining a b c 0 := by
    simpa [encoded, MultRemaining] using mult_acceptance a b c
  apply mult_validate_field x a 0 v _ bound
  · simp [astep, multARM, multCanonNext, ready.endA, List.length_eq_zero_iff]
  · intro nonempty
    have pos : 0 < a.length := List.length_pos_iff.mpr nonempty
    change x.getD (v 4 - 2) false = _
    rw [ready.endA, show 2 * a.length - 2 = 2 * (a.length - 1) by omega, encoded]
    exact (mult_addresses a b c).1 _ (by omega)
  · intro invalid
    apply decide_eq_false
    intro h
    exact invalid (member.mp h).1
  · intro ha va ba fa
    have ra := mult_ready_frame ready fa
    change MultHalt x (some (.canonTest 1), va, none) _
    apply mult_validate_field x b 1 va _ ba
    · simp [astep, multARM, multCanonNext, ra.endB, ra.startB, List.length_eq_zero_iff]
    · intro nonempty
      have pos : 0 < b.length := List.length_pos_iff.mpr nonempty
      change x.getD (va 5 - 2) false = _
      rw [ra.endB, show 2 * a.length + 2 + 2 * b.length - 2 =
        2 * a.length + 2 + 2 * (b.length - 1) by omega, encoded]
      exact (mult_addresses a b c).2.1 _ (by omega)
    · intro invalid
      apply decide_eq_false
      intro h
      exact invalid (member.mp h).2.1
    · intro hb vb bb fb
      have rb := mult_ready_frame ra fb
      change MultHalt x (some (.canonTest 2), vb, none) _
      apply mult_validate_field x c 2 vb _ bb
      · have test : (vb 3 = vb 1) ↔ c = [] := by
          rw [rb.startC, rb.length, size]
          simp
        simp only [astep, multARM, multCanonNext]
        simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
          ↓reduceIte, test]
      · intro nonempty
        have pos : 0 < c.length := List.length_pos_iff.mpr nonempty
        change x.getD (vb 1 - 1) false = _
        rw [rb.length, size, show 2 * a.length + 2 + 2 * b.length + 2 + c.length - 1 =
          2 * a.length + 2 + 2 * b.length + 2 + (c.length - 1) by omega, encoded]
        exact (mult_addresses a b c).2.2 _
      · intro invalid
        apply decide_eq_false
        intro h
        exact invalid (member.mp h).2.2.1
      · intro hc vc bc fc
        have rc := mult_ready_frame rb fc
        change MultHalt x (some (.copy 8 false), vc, none) _
        have start := mult_copy x 8 vc bc (by simp [multCopy, rc.result])
        let vd := Function.update vc 12 (vc 3)
        have bd : ∀ r, vd r ≤ 4 * (x.length + 1) := register_update_le vc 12 _ _ bc (bc 3)
        have layout : vd 1 = x.length ∧ vd 2 = 2 * a.length + 2 ∧ vd 4 = 2 * a.length ∧
            vd 5 = 2 * a.length + 2 + 2 * b.length ∧ vd 6 = a.length + b.length := by
          simpa [vd] using ⟨rc.length, rc.startB, rc.endA, rc.endB, rc.rounds⟩
        have columns := mult_columns_run x a b c encoded 0 (Nat.zero_le _) vd bd layout
          (by simpa [vd] using rc.column) (by simpa [vd, multCarry] using rc.carry)
          (by simpa [vd] using rc.startC)
        have acceptance : (x ∈ multLang) ↔ MultRemaining a b c 0 := by
          rw [member]
          simp only [ha, hb, hc, true_and]
        rw [← acceptance] at columns
        apply start.halt
        exact columns

/-- Two consecutive decrements share one bounded path argument. This private arithmetic
fragment is a promotion candidate for the shared input-access layer. -/
private lemma mult_sub_two (x : List Bool) (v : Fin 13 → ℕ) (r : Fin 13)
    (labels : Bool → MultState) (done : MultState)
    (code₀ : multARM (labels false) = .dec r (labels true))
    (code₁ : multARM (labels true) = .dec r done)
    (bound : ∀ s, v s ≤ 4 * (x.length + 1)) :
    MultReach x (some (labels false), v, none)
      (some done, Function.update v r (v r - 2), none) := by
  apply AReach.step ⟨mult_preconditions x _ v none, bound⟩
  simp only [astep, code₀]
  have nextBound := register_update_le v r (4 * (x.length + 1)) (v r - 1) bound
    ((Nat.sub_le _ _).trans (bound r))
  simpa only [astep, code₁, Function.update_self, Function.update_idem, Nat.sub_sub,
    show (1 : ℕ) + 1 = 2 by rfl] using
    (AReach.single (A := multARM) (oracle := multOracle) (x := x)
      (a := (some (labels true), Function.update v r (v r - 1), none))
      ⟨mult_preconditions x _ _ none, nextBound⟩)

/-- Parsed boundaries are converted to operand ends and the number of product columns.
Proof sketch. Shared copies preserve the two starts. Two decrements remove each separator;
halving the second start and subtracting two gives the sum of operand lengths. Every
arithmetic operation decreases a copied boundary. The canonicality/column proof then applies. -/
private lemma mult_prepare_run (x a b c : List Bool)
    (encoded : x = pairEncode a (pairEncode b c)) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (len : v 1 = x.length) (startB : v 2 = 2 * a.length + 2)
    (startC : v 3 = 2 * a.length + 2 + 2 * b.length + 2)
    (a0 : v 4 = 0) (b0 : v 5 = 0) (n0 : v 6 = 0)
    (j0 : v 7 = 0) (carry0 : v 11 = 0) (result0 : v 12 = 0) :
    MultHalt x (some (.copy 2 false), v, none) (decide (x ∈ multLang)) := by
  let va := Function.update v 4 (2 * a.length)
  let vb := Function.update va 5 (2 * a.length + 2 + 2 * b.length)
  let vn := Function.update vb 6 (a.length + b.length)
  have ba : ∀ r, va r ≤ 4 * (x.length + 1) := by
    apply register_update_le v 4 _ _ bound
    have := bound 2; rw [startB] at this; omega
  have bb : ∀ r, vb r ≤ 4 * (x.length + 1) := by
    apply register_update_le va 5 _ _ ba
    have := bound 3; rw [startC] at this; omega
  have bn : ∀ r, vn r ≤ 4 * (x.length + 1) := by
    apply register_update_le vb 6 _ _ bb
    have := bound 3; rw [startC] at this; omega
  have cpA := mult_copy x 2 v bound (by simp [multCopy, a0])
  have bca : ∀ r, Function.update v 4 (v 2) r ≤ 4 * (x.length + 1) :=
    register_update_le v 4 _ _ bound (bound 2)
  have subA : MultReach x (some (.endDown false false), Function.update v 4 (v 2), none)
      (some (.copy 3 false), va, none) := by
    simpa [va, startB] using mult_sub_two x (Function.update v 4 (v 2)) 4
      (.endDown false) (.copy 3 false) rfl rfl bca
  have cpB := mult_copy x 3 va ba (by simp [multCopy, va, b0])
  have bcb : ∀ r, Function.update va 5 (va 3) r ≤ 4 * (x.length + 1) :=
    register_update_le va 5 _ _ ba (ba 3)
  have subB : MultReach x (some (.endDown true false), Function.update va 5 (va 3), none)
      (some (.copy 4 false), vb, none) := by
    simpa [vb, va, startC] using mult_sub_two x (Function.update va 5 (va 3)) 5
      (.endDown true) (.copy 4 false) rfl rfl bcb
  have cpN := mult_copy x 4 vb bb (by simp [multCopy, vb, va, n0])
  let vc := Function.update vb 6 (vb 3)
  let vh := Function.update vb 6 (vb 3 / 2)
  have bc : ∀ r, vc r ≤ 4 * (x.length + 1) := register_update_le vb 6 _ _ bb (bb 3)
  have bh : ∀ r, vh r ≤ 4 * (x.length + 1) :=
    register_update_le vb 6 _ _ bb ((Nat.div_le_self _ _).trans (bb 3))
  have half : MultReach x (some .countHalf, vc, none) (some (.countDown false), vh, none) := by
    simpa [astep, multARM, vc, vh] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some .countHalf, vc, none)) ⟨mult_preconditions x _ vc none, bc⟩)
  have arithmetic : vb 3 / 2 - 2 = a.length + b.length := by simp [vb, va, startC]; omega
  have subN : MultReach x (some (.countDown false), vh, none) (some (.canonTest 0), vn, none) := by
    simpa only [vh, Function.update_self, Function.update_idem, arithmetic, vn] using
      mult_sub_two x vh 6 .countDown (.canonTest 0) rfl rfl bh
  have ready : MultReady x a b c vn := by
    constructor <;> simp [vn, vb, va, len, startB, startC, j0, carry0, result0]
  have finish := mult_canonical_run x a b c encoded vn bn ready
  exact cpA.halt (subA.halt (cpB.halt (subB.halt (cpN.halt (half.halt (subN.halt finish))))))

/-- A failed outer or inner pair decode excludes every genuine multiplication triple. -/
private lemma mult_bad_decode (x : List Bool)
    (bad : (pairDecode x).bind (fun p => pairDecode p.2) = none) : x ∉ multLang := by
  rintro ⟨u, v, rfl⟩
  simp only [pairDecode_pairEncode, Option.bind_some, reduceCtorEq] at bad

/-- The complete all-input bounded halting theorem for the multiplication ARM.
Proof sketch. Count the physical input with the public length fragment and validate both
aligned pairs with the public shape fragment. Either failure rejects a malformed triple.
On success, shared copies retain the two suffix starts; separator arithmetic prepares the
metadata and the proved canonicality/column construction supplies the answer. -/
private lemma mult_run (x : List Bool) :
    MultHalt x (some .lengthTest, fun _ => 0, none) (decide (x ∈ multLang)) := by
  let vl : Fin 13 → ℕ := Function.update (fun _ => 0) 1 x.length
  have bl : ∀ r, vl r ≤ 4 * (x.length + 1) :=
    register_update_le (fun _ => 0) 1 _ _ (fun _ => Nat.zero_le _) (by omega)
  have length : MultReach x (some .lengthTest, fun _ => 0, none)
      (some (.pairTest false), vl, none) :=
    inputLength_loop multARM multOracle x 1 1 .lengthTest .lengthInc (.pairTest false)
      rfl rfl (fun i _ => (mult_queries x i).2) _ (by omega) (fun _ => 0)
      (fun _ => Nat.zero_le _) (Nat.zero_le _)
  have outer := mult_scan x x false vl bl (by simp [vl]) (by simp [vl])
  cases parsed : pairDecode x with
  | none =>
    rw [parsed] at outer
    obtain ⟨t, ht, path⟩ := outer
    have lastBound : ∀ r, Function.update vl 0 (vl 0 + t) r ≤ 4 * (x.length + 1) := by
      apply register_update_le vl 0 _ _ bl
      simp [vl]; omega
    have reject := mult_bad_decode x (by simp [parsed])
    simpa only [reject, decide_false] using length.halt (path.halt (mult_return x false _ lastBound))
  | some fields =>
    rcases fields with ⟨a, tail⟩
    have eqx := eq_pairEncode_of_pairDecode x a tail parsed
    have outerSize : x.length = 2 * a.length + 2 + tail.length := by rw [eqx, length_pairEncode]
    let vs := Function.update vl 0 (2 * a.length + 2)
    let vb := Function.update vs 2 (2 * a.length + 2)
    have bs : ∀ r, vs r ≤ 4 * (x.length + 1) := register_update_le vl 0 _ _ bl (by omega)
    have bb : ∀ r, vb r ≤ 4 * (x.length + 1) := register_update_le vs 2 _ _ bs (by omega)
    have outerPath : MultReach x (some (.pairTest false), vl, none)
        (some (.copy 0 false), vs, none) := by simpa [parsed, vl, vs] using outer
    have saveB : MultReach x (some (.copy 0 false), vs, none)
        (some (.pairTest true), vb, none) := by
      simpa [multCopy, vs, vb, vl] using mult_copy x 0 vs bs (by simp [multCopy, vs, vl])
    have inner := mult_scan x tail true vb bb (by simp [vb, vs, vl]; omega) (by
      intro i hi
      change x.getD (2 * a.length + 2 + i) false = tail.getD i false
      rw [eqx, pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      congr 1
      omega)
    cases nested : pairDecode tail with
    | none =>
      rw [nested] at inner
      obtain ⟨t, ht, path⟩ := inner
      have lastBound : ∀ r, Function.update vb 0 (vb 0 + t) r ≤ 4 * (x.length + 1) := by
        apply register_update_le vb 0 _ _ bb
        simp [vb, vs, vl]; omega
      have reject := mult_bad_decode x (by simp [parsed, nested])
      simpa only [reject, decide_false] using
        length.halt (outerPath.halt (saveB.halt (path.halt (mult_return x false _ lastBound))))
    | some fields =>
      rcases fields with ⟨b, c⟩
      have eqtail := eq_pairEncode_of_pairDecode tail b c nested
      have encoded : x = pairEncode a (pairEncode b c) := by rw [eqx, eqtail]
      have size : x.length = 2 * a.length + 2 + 2 * b.length + 2 + c.length := by
        rw [encoded, length_pairEncode, length_pairEncode]; omega
      let vc := Function.update vb 0 (2 * a.length + 2 + 2 * b.length + 2)
      let vd := Function.update vc 3 (2 * a.length + 2 + 2 * b.length + 2)
      have bc : ∀ r, vc r ≤ 4 * (x.length + 1) := register_update_le vb 0 _ _ bb (by omega)
      have bd : ∀ r, vd r ≤ 4 * (x.length + 1) := register_update_le vc 3 _ _ bc (by omega)
      have innerPath : MultReach x (some (.pairTest true), vb, none)
          (some (.copy 1 false), vc, none) := by
        simpa [nested, vc, vb, vs, vl, Nat.add_assoc] using inner
      have saveC : MultReach x (some (.copy 1 false), vc, none)
          (some (.copy 2 false), vd, none) := by
        simpa [multCopy, vc, vd] using mult_copy x 1 vc bc (by simp [multCopy, vc, vb, vs, vl])
      have prepared : MultHalt x (some (.copy 2 false), vd, none) (decide (x ∈ multLang)) := by
        apply mult_prepare_run x a b c encoded vd bd <;> simp [vd, vc, vb, vs, vl]
      exact length.halt (outerPath.halt (saveB.halt (innerPath.halt (saveC.halt prepared))))

/-- **Multiplication verifies in logarithmic space** ([AB09, Example 4.7];
proved — phase P4.4): the grade-school method checks the third
component bit by bit with carry and index counters only.

**Proof sketch.** The verifier computes each bit of `a · b` on demand:
bit `j` of the product is determined by the column sums
`∑_{p+q=j'} a_p · b_q` for `j' ≤ j` propagated through the carry — maintain
the carry (of `O(logSpace n)` bits, since a column sum is at most the input
length) and two index counters, re-reading `a`'s and `b`'s bits from the
input by position arithmetic on the nested pair layout (through `whole`-mode
calls to the input-access languages `Complexity.inputBitLang` and
`Complexity.inputLenLang` of phase P4.4b; the received
`Machines/Parse2`/`ParseCmp` toolkit reads only unary-first inputs
`⟨1ⁿ, ⟨u, w⟩⟩` and does not apply); compare each computed bit against the
third component's bit and reject on mismatch or malformed shape; accept when
every column through `|a| + |b|` matches (missing result bits read as `0`, a
longer result field rejected) and no carry remains. Registers: carry, two
indices, a column cursor — `O(logSpace n)` cells; assembled by the received
`arm_decides_poly`. Fill obligations, named: the column-sum/carry invariant;
the position arithmetic into the nested pairs; the shape validator; the
`DecidesInSpace` packaging. (Sketch prose corrected at phase P4.4b; the
statement is unchanged.) -/
theorem multLang_mem_LOGSPACE : multLang ∈ LOGSPACE := by
  refine arm_decides_poly multARM .lengthTest ![inputBitLang, inputLenLang] ?_ 4 1 ?_
  · intro i
    rcases i with ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    · exact inputBitLang_mem
    · exact inputLenLang_mem
  · intro x
    simpa only [pow_one, multOracle, indicator_eq_decide] using mult_run x

end Complexity
