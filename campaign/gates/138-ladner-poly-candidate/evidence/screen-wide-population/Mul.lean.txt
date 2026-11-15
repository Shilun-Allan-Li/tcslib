/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.AddSub

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary multiplication and word reversal in polynomial time

Infrastructure for [AB09 §7.2]; not itself a result of the book. Multiplication is the
shift-and-add loop, run through `Complexity.BinArith.polyTimeComputable_iterate`; reversal
(used by long division, which reads the dividend from its top bit) is the same kind of loop.

## Main definitions

* `Complexity.BinArith.mul` — the product of the two components of a pair.
* `Complexity.BinArith.mulStep` — one round of shift-and-add on `⟨A, ⟨B, acc⟩⟩`.
* `Complexity.BinArith.revStep` — one round of reversal on `⟨src, acc⟩`.
* `Complexity.BinArith.sqStep` — one round of binary repeated squaring on `⟨p, ⟨E, ⟨b, acc⟩⟩⟩`
  for a given product, shared by modular exponentiation and `powCap`.
* `Complexity.BinArith.powCap` — the power of the first value to the second, capped at one plus
  the third.

## Main results

* `Complexity.BinArith.polyTimeComputable_mul` — binary multiplication is polynomial-time.
* `Complexity.BinArith.polyTimeComputable_reverse` — word reversal is polynomial-time.
* `Complexity.BinArith.polyTimeComputable_powCap` — the saturated power is polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2; Exercise 7.3.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### Reversal -/

/-- One round of reversal on `⟨src, acc⟩`: move the head of `src` onto `acc`. -/
def revStep (S : List Bool) : List Bool :=
  if isNilB (pairFstD S) then S
  else pairEncode ((pairFstD S).drop 1) ((pairFstD S).headD false :: pairSndD S)

/-- A reversal round is polynomial-time. -/
theorem polyTimeComputable_revStep : PolyTimeComputable revStep := by
  unfold revStep
  refine polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
    polyTimeComputable_id ?_
  exact (polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_cons (polyTimeComputable_headD.comp polyTimeComputable_pairFstD)
      polyTimeComputable_pairSndD)

/-- Reversal rounds keep `reverse src ++ acc` and the total length. -/
theorem revStep_pairEncode (u v : List Bool) :
    ∃ u' v', revStep (pairEncode u v) = pairEncode u' v' ∧ u'.reverse ++ v' = u.reverse ++ v ∧
      u'.length + v'.length = u.length + v.length ∧ (u ≠ [] → u'.length < u.length) ∧
      (u = [] → u' = []) := by
  cases u with
  | nil => exact ⟨[], v, by simp [revStep, isNilB], rfl, rfl, by simp, fun _ => rfl⟩
  | cons b u =>
    refine ⟨u, b :: v, by simp [revStep, isNilB], by simp, by simp; omega, by simp, by simp⟩

/-- **Word reversal is polynomial-time**: `|w| + 1` reversal rounds from `⟨w, []⟩`.

**Proof sketch.** Each round moves the head of `src` onto `acc`, keeping
`reverse src ++ acc = reverse w` and the total length; `|src|` reaches `0` within `|w|`
rounds, after which the state is fixed and `acc = reverse w`. -/
theorem polyTimeComputable_reverse : PolyTimeComputable (fun w : List Bool => w.reverse) := by
  let I : List Bool → List Bool → Prop := fun w S => ∃ u v, S = pairEncode u v ∧
    u.reverse ++ v = w.reverse ∧ u.length + v.length = w.length
  have hI : ∀ w S, I w S → I w (revStep S) := by
    rintro w S ⟨u, v, rfl, h1, h2⟩
    obtain ⟨u', v', he, h1', h2', -, -⟩ := revStep_pairEncode u v
    exact ⟨u', v', he, h1'.trans h1, h2'.trans h2⟩
  have h0 : ∀ w, I w (pairEncode w []) := fun w => ⟨w, [], rfl, by simp, by simp⟩
  have hinit : PolyTimeComputable (fun w : List Bool => pairEncode w []) :=
    polyTimeComputable_id.pairEncode (polyTimeComputable_const [])
  have hloop := polyTimeComputable_iterate polyTimeComputable_revStep hinit 1 1 3 1
    (fun w i _ => by
      obtain ⟨u, v, he, -, h2⟩ := iterate_invariant (I w) (hI w) i (h0 w)
      rw [he, length_pairEncode]; simp; omega)
  convert polyTimeComputable_pairSndD.comp hloop using 1
  funext w
  obtain ⟨u, v, he, h1, -⟩ := iterate_invariant (I w) (hI w) (1 * (w.length + 1) ^ 1) (h0 w)
  have hμ := iterate_measure_eq_zero (g := revStep) (I w) (fun S => (pairFstD S).length) (hI w)
    (by
      rintro S ⟨u, v, rfl, -, -⟩ hpos
      obtain ⟨u', v', he', -, -, hlt, -⟩ := revStep_pairEncode u v
      rw [he']; simp only [pairFstD_pairEncode] at hpos ⊢
      exact hlt (List.ne_nil_of_length_pos hpos))
    (by
      rintro S ⟨u, v, rfl, -, -⟩ h0
      simp only [pairFstD_pairEncode, List.length_eq_zero_iff] at h0
      subst h0; simp [revStep, isNilB])
    (1 * (w.length + 1) ^ 1) (pairEncode w []) (h0 w) (by simp)
  rw [he] at hμ
  simp only [pairFstD_pairEncode, List.length_eq_zero_iff] at hμ
  subst hμ
  simp only [Function.comp_apply, he, pairSndD_pairEncode]
  simpa using h1.symm

/-! ### Multiplication -/

/-- The product of the values of the two components of `z`, as a binary word. -/
def mul (z : List Bool) : List Bool := Nat.bits (bitsVal (pairFstD z) * bitsVal (pairSndD z))

/-- `mul` on encoded numbers is multiplication. -/
@[simp] theorem mul_pairEncode (a b : ℕ) :
    mul (pairEncode (Nat.bits a) (Nat.bits b)) = Nat.bits (a * b) := by
  simp [mul, bitsVal_bits]

/-- One round of shift-and-add on `⟨A, ⟨B, acc⟩⟩`: if the low bit of `B` is set add `A` to
`acc`; then double `A` and halve `B`. A state with `B = []` is fixed. -/
def mulStep (S : List Bool) : List Bool :=
  if isNilB (pairFstD (pairSndD S)) then S
  else pairEncode (false :: pairFstD S)
    (pairEncode ((pairFstD (pairSndD S)).drop 1)
      (if (pairFstD (pairSndD S)).headD false then
        add (pairEncode (pairSndD (pairSndD S)) (pairFstD S))
      else pairSndD (pairSndD S)))

/-- A shift-and-add round is polynomial-time. -/
theorem polyTimeComputable_mulStep : PolyTimeComputable mulStep := by
  unfold mulStep
  refine polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_slot2)
    polyTimeComputable_id ?_
  refine (polyTimeComputable_cons (polyTimeComputable_const [false])
    polyTimeComputable_pairFstD).pairEncode
    ((polyTimeComputable_tail.comp polyTimeComputable_slot2).pairEncode ?_)
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp polyTimeComputable_slot2)
    (polyTimeComputable_add.comp (polyTimeComputable_slot3.pairEncode polyTimeComputable_pairFstD))
    polyTimeComputable_slot3

/-- The invariant of the multiplication loop on input `z`: `acc + A·B = a·b`, `acc` is
normalized, and `|A| + |B|` does not grow. -/
def MulInv (z S : List Bool) : Prop :=
  ∃ A B C, S = pairEncode A (pairEncode B C) ∧
    bitsVal C + bitsVal A * bitsVal B = bitsVal (pairFstD z) * bitsVal (pairSndD z) ∧
    C = Nat.bits (bitsVal C) ∧ A.length + B.length ≤ (pairFstD z).length + (pairSndD z).length

/-- The shift-and-add round preserves the invariant, and shortens a nonempty `B`.

**Proof sketch.** With `B = b₀ + 2B'`, the round maps `acc + A·B` to `(acc + b₀A) + 2A·B'`,
the same value; `|A|` grows by one while `|B|` drops by one. -/
theorem mulInv_step {z S : List Bool} (h : MulInv z S) :
    MulInv z (mulStep S) ∧
      ((pairFstD (pairSndD S)) ≠ [] →
        (pairFstD (pairSndD (mulStep S))).length < (pairFstD (pairSndD S)).length) ∧
      ((pairFstD (pairSndD S)) = [] → mulStep S = S) := by
  obtain ⟨A, B, C, rfl, hv, hC, hl⟩ := h
  have hB := bitsVal_eq_headD B
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨?_, fun hne => ?_, fun he => by simp [mulStep, isNilB, he]⟩
  · unfold mulStep
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    split_ifs with h1 h2
    · exact ⟨A, B, C, rfl, hv, hC, hl⟩
    · have hne : B ≠ [] := by simpa [isNilB] using h1
      refine ⟨false :: A, B.drop 1, _, rfl, ?_, by simp [add, bitsVal_bits], ?_⟩
      · simp only [add, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_bits, bitsVal,
          Bool.toNat_false, zero_add]
        rw [h2, Bool.toNat_true] at hB
        rw [← hv, hB]; ring
      · have := List.length_pos_iff.mpr hne
        simp; omega
    · have hne : B ≠ [] := by simpa [isNilB] using h1
      refine ⟨false :: A, B.drop 1, C, rfl, ?_, hC, ?_⟩
      · simp only [bitsVal, Bool.toNat_false, zero_add]
        simp only [Bool.not_eq_true] at h2
        rw [h2, Bool.toNat_false, zero_add] at hB
        rw [← hv, hB]; ring
      · have := List.length_pos_iff.mpr hne
        simp; omega
  · have hne' : isNilB B = false := by simpa [isNilB] using hne
    simp only [mulStep, pairFstD_pairEncode, pairSndD_pairEncode, hne', Bool.false_eq_true,
      if_false, List.length_drop]
    have := List.length_pos_iff.mpr hne
    omega

/-- A state satisfying the multiplication invariant has length at most `4(|z| + 1)`
(`acc ≤ a·b < 2^{|a|+|b|}` bounds the normalized `acc`). -/
theorem length_le_of_mulInv {z S : List Bool} (h : MulInv z S) : S.length ≤ 4 * (z.length + 1) := by
  obtain ⟨A, B, C, rfl, hv, hC, hl⟩ := h
  have hCl : C.length ≤ (pairFstD z).length + (pairSndD z).length := by
    rw [hC]
    apply length_bits_le
    calc bitsVal C ≤ bitsVal (pairFstD z) * bitsVal (pairSndD z) := by omega
      _ < 2 ^ (pairFstD z).length * 2 ^ (pairSndD z).length := by
          rcases Nat.eq_zero_or_pos (bitsVal (pairSndD z)) with h0 | h0
          · rw [h0, mul_zero]; positivity
          · exact Nat.mul_lt_mul_of_lt_of_le (bitsVal_lt_two_pow _)
              (bitsVal_lt_two_pow _).le (by positivity)
      _ = 2 ^ ((pairFstD z).length + (pairSndD z).length) := by rw [pow_add]
  have hz := length_pair_components_le z
  simp only [length_pairEncode]
  omega

/-- The input state `⟨a, ⟨b, []⟩⟩` of the multiplication loop. -/
def mulInit (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairEncode (pairSndD z) [])

/-- The input state satisfies the multiplication invariant. -/
theorem mulInv_init (z : List Bool) : MulInv z (mulInit z) :=
  ⟨_, _, [], rfl, by simp [bitsVal], by simp [bitsVal, Nat.zero_bits], le_rfl⟩

/-- **Binary multiplication is polynomial-time** (infrastructure for [AB09 §7.2]; not
itself a result of the book).

**Proof sketch.** Run `|z| + 1` shift-and-add rounds from `⟨a, ⟨b, []⟩⟩`
(`polyTimeComputable_iterate`). The invariant `acc + A·B = a·b` (`MulInv`) holds throughout
and bounds the state length linearly; `|B|` drops each round until `B = []`, which is then
fixed (`iterate_measure_eq_zero`), so the final `acc` is `Nat.bits (a·b)`. -/
theorem polyTimeComputable_mul : PolyTimeComputable mul := by
  have hinit : PolyTimeComputable mulInit :=
    polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))
  have hloop := polyTimeComputable_iterate polyTimeComputable_mulStep hinit 1 1 4 1
    (fun z i _ => by
      simpa using length_le_of_mulInv
        (iterate_invariant (MulInv z) (fun _ h => (mulInv_step h).1) i (mulInv_init z)))
  convert polyTimeComputable_slot3.comp hloop using 1
  funext z
  have hμ := iterate_measure_eq_zero (g := mulStep) (MulInv z)
    (fun S => (pairFstD (pairSndD S)).length) (fun _ h => (mulInv_step h).1)
    (fun S h hpos => (mulInv_step h).2.1 (List.ne_nil_of_length_pos hpos))
    (fun S h h0 => (mulInv_step h).2.2 (List.length_eq_zero_iff.mp h0))
    (1 * (z.length + 1) ^ 1) (mulInit z) (mulInv_init z)
    (by simp [mulInit]; have := length_pairSndD_le z; omega)
  obtain ⟨A, B, C, he, hv, hC, -⟩ :=
    iterate_invariant (MulInv z) (fun _ h => (mulInv_step h).1) (1 * (z.length + 1) ^ 1)
      (mulInv_init z)
  rw [he] at hμ
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_eq_zero_iff] at hμ
  subst hμ
  simp only [Function.comp_apply, he, pairSndD_pairEncode, mul]
  rw [hC]
  simp only [bitsVal, mul_zero, add_zero] at hv
  rw [hv]

/-! ### Repeated-squaring rounds -/

/-- One round of binary repeated squaring [AB09, Exercise 7.3] on `⟨p, ⟨E, ⟨b, acc⟩⟩⟩`, for
a product `op` that reads its parameter from the first component of `⟨p, ⟨x, y⟩⟩` and its
factors from the second: if the low bit of `E` is set, `acc := op ⟨p, ⟨acc, b⟩⟩`; then
`b := op ⟨p, ⟨b, b⟩⟩` and `E` loses its low bit. States with `E = []`, or on which `stop`
holds, are fixed. -/
def sqStep (op : List Bool → List Bool) (stop : List Bool → Bool) (S : List Bool) :
    List Bool :=
  if decide (pairFstD (pairSndD S) = []) || stop S then S
  else pairEncode (pairFstD S) (pairEncode ((pairFstD (pairSndD S)).drop 1)
    (pairEncode (op (pairEncode (pairFstD S) (pairEncode (pairFstD (pairSndD (pairSndD S)))
        (pairFstD (pairSndD (pairSndD S))))))
      (if (pairFstD (pairSndD S)).headD false then
        op (pairEncode (pairFstD S) (pairEncode (pairSndD (pairSndD (pairSndD S)))
          (pairFstD (pairSndD (pairSndD S)))))
      else pairSndD (pairSndD (pairSndD S)))))

/-- A repeated-squaring round fixes a state with an empty exponent or a stopped state. -/
theorem sqStep_of_stop {op : List Bool → List Bool} {stop : List Bool → Bool}
    {S : List Bool} (h : pairFstD (pairSndD S) = [] ∨ stop S = true) :
    sqStep op stop S = S := by
  unfold sqStep
  rw [if_pos]
  rcases h with h | h
  · rw [h]
    rfl
  · rw [h, Bool.or_true]

/-- A repeated-squaring round on a live state consumes the low exponent bit `c`. -/
theorem sqStep_cons (op : List Bool → List Bool) (stop : List Bool → Bool)
    (p : List Bool) (c : Bool) (E' b acc : List Bool)
    (h : stop (pairEncode p (pairEncode (c :: E') (pairEncode b acc))) = false) :
    sqStep op stop (pairEncode p (pairEncode (c :: E') (pairEncode b acc))) =
      pairEncode p (pairEncode E' (pairEncode (op (pairEncode p (pairEncode b b)))
        (if c then op (pairEncode p (pairEncode acc b)) else acc))) := by
  unfold sqStep
  rw [if_neg (by simp only [pairFstD_pairEncode, pairSndD_pairEncode, h, reduceCtorEq,
    decide_false, Bool.or_false, Bool.false_eq_true, not_false_eq_true])]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.drop_succ_cons, List.drop_zero,
    List.headD_cons]

/-- A repeated-squaring round is polynomial-time when its product and stop test are. -/
theorem polyTimeComputable_sqStep {op : List Bool → List Bool} {stop : List Bool → Bool}
    (hop : PolyTimeComputable op) (hstop : PolyTimeComputable (fun S => [stop S])) :
    PolyTimeComputable (sqStep op stop) := by
  have hb := polyTimeComputable_pairFstD.comp polyTimeComputable_slot3
  have hm : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
      PolyTimeComputable (fun S => op (pairEncode (pairFstD S) (pairEncode (f S) (g S)))) :=
    fun hf hg => hop.comp (polyTimeComputable_pairFstD.pairEncode (hf.pairEncode hg))
  unfold sqStep
  exact polyTimeComputable_ite
    (polyTimeComputable_or (polyTimeComputable_isNil.comp polyTimeComputable_slot2) hstop)
    polyTimeComputable_id
    (polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_tail.comp polyTimeComputable_slot2).pairEncode
        ((hm hb hb).pairEncode (polyTimeComputable_ite
          (polyTimeComputable_headD.comp polyTimeComputable_slot2)
          (hm polyTimeComputable_slot4 hb) polyTimeComputable_slot4))))

/-! ### Saturated powers -/

/-- The power of the first value to the second, capped at one plus the third value.
Computed by repeated squaring with saturation, including `0 ^ 0 = 1`. -/
def powCap (z : List Bool) : List Bool :=
  Nat.bits (min
    ((LogProg.bitsVal (pairFstD z)) ^ (LogProg.bitsVal (pairFstD (pairSndD z))))
    (LogProg.bitsVal (pairSndD (pairSndD z)) + 1))

/-- On every word, `powCap` is the binary encoding of the specified capped power. -/
theorem powCap_eq (z : List Bool) :
    powCap z = Nat.bits (min
      ((LogProg.bitsVal (pairFstD z)) ^ (LogProg.bitsVal (pairFstD (pairSndD z))))
      (LogProg.bitsVal (pairSndD (pairSndD z)) + 1)) := rfl

/-- On three encoded naturals, `powCap` computes `min (m ^ e) (c + 1)`.
This is the canonical input equation for saturated repeated squaring. -/
theorem powCap_pairEncode (m e c : ℕ) :
    powCap (pairEncode (Nat.bits m) (pairEncode (Nat.bits e) (Nat.bits c))) =
      Nat.bits (min (m ^ e) (c + 1)) := by
  rw [powCap_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_bits]

/-- Saturating one factor before multiplication preserves the saturated product. -/
private theorem powCap_min_mul (a b C : ℕ) :
    min (min a C * b) C = min (a * b) C := by
  by_cases hb : b = 0
  · simp only [hb, mul_zero]
  by_cases ha : a ≤ C
  · rw [min_eq_left ha]
  have hb' : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
  have h1 : C ≤ C * b := by nlinarith
  have h2 : C ≤ a * b := by nlinarith
  rw [min_eq_right (by omega : C ≤ a), min_eq_right h1, min_eq_right h2]

/-- The same saturation law for the right factor. -/
private theorem powCap_mul_min (a b C : ℕ) :
    min (a * min b C) C = min (a * b) C := by
  simpa only [mul_comm] using powCap_min_mul b a C

/-- Saturating a base preserves every saturated natural power.

**Proof sketch.** Induct on the exponent; at each multiplication the saturation law
removes the inner cap. The zero exponent is one on both sides. -/
private theorem powCap_min_pow (a C n : ℕ) :
    min ((min a C) ^ n) C = min (a ^ n) C := by
  induction n with
  | zero => simp only [pow_zero]
  | succ n ih =>
    rw [pow_succ, powCap_mul_min]
    calc
      min ((min a C) ^ n * a) C = min (min ((min a C) ^ n) C * a) C :=
        (powCap_min_mul _ _ _).symm
      _ = min (min (a ^ n) C * a) C := by rw [ih]
      _ = min (a ^ (n + 1)) C := by rw [powCap_min_mul, pow_succ]

/-- Saturation of a powered right factor can also be removed. -/
private theorem powCap_mul_min_pow (a b C n : ℕ) :
    min (a * (min b C) ^ n) C = min (a * b ^ n) C := by
  calc
    min (a * (min b C) ^ n) C = min (a * min ((min b C) ^ n) C) C :=
      (powCap_mul_min _ _ _).symm
    _ = min (a * min (b ^ n) C) C := by rw [powCap_min_pow]
    _ = min (a * b ^ n) C := powCap_mul_min _ _ _

/-- Normalize the two arguments and select the smaller binary value. -/
private def powCapMin (z : List Bool) : List Bool :=
  let a := Nat.bits (bitsVal (pairFstD z))
  let C := Nat.bits (bitsVal (pairSndD z))
  if le (pairEncode a C) then a else C

/-- The normalized minimum reads every input through the public comparison equation. -/
private theorem powCapMin_eq (z : List Bool) :
    powCapMin z = Nat.bits (min (bitsVal (pairFstD z)) (bitsVal (pairSndD z))) := by
  unfold powCapMin
  dsimp only
  rw [le_pairEncode]
  split_ifs with h
  · rw [min_eq_left (of_decide_eq_true h)]
  · have hlt : bitsVal (pairSndD z) < bitsVal (pairFstD z) := by
      simpa only [decide_eq_true_eq, not_le] using h
    rw [min_eq_right hlt.le]

/-- The normalized minimum is polynomial-time. -/
private theorem powCapMin_FP : PolyTimeComputable powCapMin := by
  have ha := polyTimeComputable_normBits.comp polyTimeComputable_pairFstD
  have hc := polyTimeComputable_normBits.comp polyTimeComputable_pairSndD
  exact polyTimeComputable_ite (polyTimeComputable_le.comp (ha.pairEncode hc)) ha hc

/-- Multiply the last two slots and saturate at the first slot. -/
private def powCapMul (z : List Bool) : List Bool :=
  powCapMin (pairEncode (mul (pairSndD z)) (pairFstD z))

/-- Saturated multiplication is polynomial-time. -/
private theorem powCapMul_FP : PolyTimeComputable powCapMul :=
  powCapMin_FP.comp ((polyTimeComputable_mul.comp polyTimeComputable_pairSndD).pairEncode
    polyTimeComputable_pairFstD)

/-- The canonical saturated multiplication equation. -/
private theorem powCapMul_pair (C a b : ℕ) :
    powCapMul (pairEncode (Nat.bits C) (pairEncode (Nat.bits a) (Nat.bits b))) =
      Nat.bits (min (a * b) C) := by
  unfold powCapMul
  rw [powCapMin_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, mul_pairEncode, bitsVal_bits]

/-- One saturated repeated-squaring round on `⟨C, ⟨E, ⟨b, acc⟩⟩⟩`: the shared round `sqStep`
with multiplication saturated at `C`. An empty exponent word fixes the state. -/
private def powCapStep : List Bool → List Bool := sqStep powCapMul (fun _ => false)

/-- A saturated squaring round is polynomial-time. -/
private theorem powCapStep_FP : PolyTimeComputable powCapStep :=
  polyTimeComputable_sqStep powCapMul_FP (polyTimeComputable_const [false])

/-- The initial saturated squaring state has cap `c+1` and accumulator one. -/
private def powCapInit (z : List Bool) : List Bool :=
  let C := add (pairEncode (Nat.bits (bitsVal (pairSndD (pairSndD z)))) (Nat.bits 1))
  pairEncode C (pairEncode (pairFstD (pairSndD z))
    (pairEncode (powCapMin (pairEncode (pairFstD z) C)) (Nat.bits 1)))

/-- The initial state is polynomial-time computable. -/
private theorem powCapInit_FP : PolyTimeComputable powCapInit := by
  have hc := polyTimeComputable_add.comp
    ((polyTimeComputable_normBits.comp polyTimeComputable_slot3).pairEncode
      (polyTimeComputable_const (Nat.bits 1)))
  exact hc.pairEncode (polyTimeComputable_slot2.pairEncode
    ((powCapMin_FP.comp (polyTimeComputable_pairFstD.pairEncode hc)).pairEncode
      (polyTimeComputable_const (Nat.bits 1))))

/-- The loop invariant bounds all registers and preserves the saturated remaining power. -/
private def PowCapInv (z S : List Bool) : Prop :=
  let C := bitsVal (pairSndD (pairSndD z)) + 1
  ∃ E b acc, S = pairEncode (Nat.bits C)
      (pairEncode E (pairEncode (Nat.bits b) (Nat.bits acc))) ∧
    E.length ≤ (pairFstD (pairSndD z)).length ∧ b ≤ C ∧ acc ≤ C ∧
    min (acc * b ^ bitsVal E) C =
      min (bitsVal (pairFstD z) ^ bitsVal (pairFstD (pairSndD z))) C

/-- The initial state satisfies the invariant, also for exponent zero and base zero. -/
private theorem powCapInv_init (z : List Bool) : PowCapInv z (powCapInit z) := by
  refine ⟨pairFstD (pairSndD z), min (bitsVal (pairFstD z))
    (bitsVal (pairSndD (pairSndD z)) + 1), 1, ?_, le_rfl, min_le_right _ _, by omega, ?_⟩
  · simp only [powCapInit, add_pairEncode, bitsVal_bits, powCapMin_eq,
      pairFstD_pairEncode, pairSndD_pairEncode]
  · simp only [one_mul]
    exact powCap_min_pow _ _ _

/-- The round preserves the invariant and drops one exponent bit until fixed.

**Proof sketch.** Write the exponent value as its low bit plus twice its tail value.
Square the base and multiply the accumulator when that bit is one. The saturation laws
remove the inner caps, so the saturated remaining power stays unchanged. -/
private theorem powCapInv_step {z S : List Bool} (h : PowCapInv z S) :
    PowCapInv z (powCapStep S) ∧
      (pairFstD (pairSndD S) ≠ [] →
        (pairFstD (pairSndD (powCapStep S))).length < (pairFstD (pairSndD S)).length) ∧
      (pairFstD (pairSndD S) = [] → powCapStep S = S) := by
  obtain ⟨E, b, acc, rfl, hE, hb, ha, hv⟩ := h
  let C := bitsVal (pairSndD (pairSndD z)) + 1
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  by_cases he : E = []
  · subst E
    unfold powCapStep
    rw [sqStep_of_stop (Or.inl (by simp only [pairFstD_pairEncode, pairSndD_pairEncode]))]
    exact ⟨⟨[], b, acc, rfl, hE, hb, ha, hv⟩, fun h => (h rfl).elim, fun _ => rfl⟩
  have hs : powCapStep (pairEncode (Nat.bits C)
      (pairEncode E (pairEncode (Nat.bits b) (Nat.bits acc)))) =
      pairEncode (Nat.bits C) (pairEncode (E.drop 1)
        (pairEncode (Nat.bits (min (b * b) C))
          (Nat.bits (if E.headD false then min (acc * b) C else acc)))) := by
    obtain ⟨c, E', rfl⟩ := List.exists_cons_of_ne_nil he
    unfold powCapStep
    rw [sqStep_cons _ _ _ _ _ _ _ rfl, powCapMul_pair, powCapMul_pair]
    cases c <;> rfl
  rw [hs]
  refine ⟨⟨E.drop 1, min (b * b) C, if E.headD false then min (acc * b) C else acc,
    rfl, ?_, min_le_right _ _, ?_, ?_⟩, ?_, fun h => (he h).elim⟩
  · simp only [List.length_drop]; omega
  · split <;> first | exact min_le_right _ _ | exact ha
  · have heval := bitsVal_eq_headD E
    cases hh : E.headD false
    · simp only [hh, Bool.false_eq_true, if_false, Bool.toNat_false, zero_add] at heval ⊢
      rw [powCap_mul_min_pow]
      rw [heval] at hv
      simpa only [pow_mul, pow_two] using hv
    · simp only [hh, if_true, Bool.toNat_true] at heval ⊢
      rw [powCap_min_mul, powCap_mul_min_pow]
      rw [heval, pow_add, pow_mul, pow_one, pow_two] at hv
      simpa only [mul_assoc] using hv
  · simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_drop]
    have := List.length_pos_iff.mpr he
    omega

/-- All saturated states have linear length.

**Proof sketch.** The cap's word is at most one bit longer than the input cap word.
Both numerical registers are below the cap, and the exponent is a suffix of its original
word. The three pair encodings add only a fixed linear overhead. -/
private theorem powCapInv_length {z S : List Bool} (h : PowCapInv z S) :
    S.length ≤ 16 * (z.length + 1) := by
  obtain ⟨E, b, acc, rfl, hE, hb, ha, -⟩ := h
  let w := pairSndD (pairSndD z)
  have hc : (Nat.bits (bitsVal w + 1)).length ≤ w.length + 1 := by
    apply length_bits_le
    have hv := bitsVal_lt_two_pow w
    have hp : 0 < 2 ^ w.length := by positivity
    rw [pow_succ]
    omega
  have hbl := (length_bits_mono hb).trans hc
  have hal := (length_bits_mono ha).trans hc
  have hw : w.length ≤ z.length :=
    (length_pairSndD_le _).trans (length_pairSndD_le z)
  have he : (pairFstD (pairSndD z)).length ≤ z.length :=
    (length_pairFstD_le _).trans (length_pairSndD_le z)
  dsimp only [w] at hc hbl hal hw
  simp only [length_pairEncode]
  omega

/-- Saturated binary exponentiation is polynomial-time by repeated squaring.

**Proof sketch.** Iterate the saturated squaring round for `|z|+1` rounds with the
existing polynomial iterator. Every intermediate state has linear length by the cap
invariant. Each live round consumes one exponent bit, so the remaining exponent is
empty at the end; the invariant then identifies the accumulator with the required
capped power. In particular a large binary exponent never expands the output. -/
theorem polyTimeComputable_powCap : PolyTimeComputable powCap := by
  have hloop := polyTimeComputable_iterate powCapStep_FP powCapInit_FP 1 1 16 1
    (fun z i _ => by
      simpa only [pow_one] using powCapInv_length
        (iterate_invariant (PowCapInv z) (fun _ h => (powCapInv_step h).1) i (powCapInv_init z)))
  convert polyTimeComputable_slot4.comp hloop using 1
  funext z
  have hzero := iterate_measure_eq_zero (g := powCapStep) (PowCapInv z)
    (fun S => (pairFstD (pairSndD S)).length) (fun _ h => (powCapInv_step h).1)
    (fun S h hp => (powCapInv_step h).2.1 (List.ne_nil_of_length_pos hp))
    (fun S h h0 => (powCapInv_step h).2.2 (List.length_eq_zero_iff.mp h0))
    (1 * (z.length + 1) ^ 1) (powCapInit z) (powCapInv_init z) (by
      simp only [powCapInit, pairFstD_pairEncode, pairSndD_pairEncode, one_mul, pow_one]
      have := (length_pairFstD_le (pairSndD z)).trans (length_pairSndD_le z)
      omega)
  obtain ⟨E, b, acc, hs, -, -, ha, hv⟩ :=
    iterate_invariant (PowCapInv z) (fun _ h => (powCapInv_step h).1)
      (1 * (z.length + 1) ^ 1) (powCapInv_init z)
  rw [hs] at hzero
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_eq_zero_iff] at hzero
  subst E
  have hnil : bitsVal ([] : List Bool) = 0 := by
    simpa only [Nat.zero_bits] using bitsVal_bits 0
  simp only [hnil, pow_zero, mul_one, min_eq_left ha] at hv
  simp only [Function.comp_apply, hs, pairSndD_pairEncode, powCap_eq]
  rw [hv]


end BinArith

end Complexity
