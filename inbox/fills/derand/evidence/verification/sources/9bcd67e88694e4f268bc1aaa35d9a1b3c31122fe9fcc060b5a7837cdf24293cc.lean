/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Mul

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary division with remainder in polynomial time

Infrastructure for [AB09 §7.2]; not itself a result of the book. Schoolbook long division:
the dividend is reversed (top bit first) and consumed one bit per round of
`Complexity.BinArith.polyTimeComputable_iterate`, shifting it into a running remainder from
which the divisor is subtracted whenever it fits. Division by `0` follows Lean's convention
(`a / 0 = 0`, `a % 0 = a`).

## Main definitions

* `Complexity.BinArith.div`, `Complexity.BinArith.mod` — quotient and remainder of the two
  components of a pair.
* `Complexity.BinArith.divStep` — one round of long division on `⟨b, ⟨R, ⟨r, q⟩⟩⟩`.

## Main results

* `Complexity.BinArith.polyTimeComputable_isZero` — the zero test.
* `Complexity.BinArith.polyTimeComputable_div`, `Complexity.BinArith.polyTimeComputable_mod`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-- The zero test `bitsVal w = 0` is polynomial-time (no `1` in `w`). -/
theorem polyTimeComputable_isZero :
    PolyTimeComputable (fun w : List Bool => [decide (bitsVal w = 0)]) := by
  convert polyTimeComputable_not polyTimeComputable_any using 1
  funext w
  cases h : w.any id <;> simp [bitsVal_eq_zero_iff, h]

/-- The quotient of the values of the two components of `z`, as a binary word. -/
def div (z : List Bool) : List Bool := Nat.bits (bitsVal (pairFstD z) / bitsVal (pairSndD z))

/-- The remainder of the values of the two components of `z`, as a binary word. -/
def mod (z : List Bool) : List Bool := Nat.bits (bitsVal (pairFstD z) % bitsVal (pairSndD z))

/-- `div` on encoded numbers is `/`. -/
@[simp] theorem div_pairEncode (a b : ℕ) :
    div (pairEncode (Nat.bits a) (Nat.bits b)) = Nat.bits (a / b) := by simp [div, bitsVal_bits]

/-- `mod` on encoded numbers is `%`. -/
@[simp] theorem mod_pairEncode (a b : ℕ) :
    mod (pairEncode (Nat.bits a) (Nat.bits b)) = Nat.bits (a % b) := by simp [mod, bitsVal_bits]

/-- One round of long division on `⟨b, ⟨R, ⟨r, q⟩⟩⟩` (`R` the unread dividend, top bit
first): shift the next bit `c` into `r' = 2r + c`; if `b ≤ r'` subtract `b` and append a
quotient bit `1`, else append `0`. A state with `R = []` is fixed. -/
def divStep (S : List Bool) : List Bool :=
  if isNilB (pairFstD (pairSndD S)) then S
  else if le (pairEncode (pairFstD S)
      ((pairFstD (pairSndD S)).headD false :: pairFstD (pairSndD (pairSndD S)))) then
    pairEncode (pairFstD S) (pairEncode ((pairFstD (pairSndD S)).drop 1)
      (pairEncode (sub (pairEncode ((pairFstD (pairSndD S)).headD false ::
        pairFstD (pairSndD (pairSndD S))) (pairFstD S)))
        (true :: pairSndD (pairSndD (pairSndD S)))))
  else
    pairEncode (pairFstD S) (pairEncode ((pairFstD (pairSndD S)).drop 1)
      (pairEncode ((pairFstD (pairSndD S)).headD false :: pairFstD (pairSndD (pairSndD S)))
        (false :: pairSndD (pairSndD (pairSndD S)))))

/-- A long-division round is polynomial-time. -/
theorem polyTimeComputable_divStep : PolyTimeComputable divStep := by
  have hs3 : PolyTimeComputable (fun S => pairFstD (pairSndD (pairSndD S))) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_slot3
  have hr' := polyTimeComputable_cons (polyTimeComputable_headD.comp polyTimeComputable_slot2) hs3
  have hR := polyTimeComputable_tail.comp polyTimeComputable_slot2
  unfold divStep
  refine polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_slot2)
    polyTimeComputable_id ?_
  refine polyTimeComputable_ite (polyTimeComputable_le.comp
    (polyTimeComputable_pairFstD.pairEncode hr')) ?_ ?_
  · exact polyTimeComputable_pairFstD.pairEncode (hR.pairEncode
      ((polyTimeComputable_sub.comp (hr'.pairEncode polyTimeComputable_pairFstD)).pairEncode
        (polyTimeComputable_cons (polyTimeComputable_const [true]) polyTimeComputable_slot4)))
  · exact polyTimeComputable_pairFstD.pairEncode (hR.pairEncode (hr'.pairEncode
      (polyTimeComputable_cons (polyTimeComputable_const [false]) polyTimeComputable_slot4)))

/-- The input state `⟨b, ⟨reverse a, ⟨[], []⟩⟩⟩` of the division loop. -/
def divInit (z : List Bool) : List Bool :=
  pairEncode (pairSndD z) (pairEncode (pairFstD z).reverse (pairEncode [] []))

/-- The invariant of the division loop on input `z = ⟨a, b⟩`: the slots `r` and `q` grow by
at most one bit per consumed bit of `R`, and, when `b ≠ 0`, `(q·b + r)·2^|R| + R̄ = a` with
`r < b` (`R̄` the value of the unread bits). -/
def DivInv (z S : List Bool) : Prop :=
  ∃ R r q, S = pairEncode (pairSndD z) (pairEncode R (pairEncode r q)) ∧
    r.length + R.length ≤ (pairFstD z).length ∧ q.length + R.length ≤ (pairFstD z).length ∧
    (0 < bitsVal (pairSndD z) →
      (bitsVal q * bitsVal (pairSndD z) + bitsVal r) * 2 ^ R.length + bitsVal R.reverse =
        bitsVal (pairFstD z) ∧ bitsVal r < bitsVal (pairSndD z))

/-- The input state satisfies the division invariant. -/
theorem divInv_init (z : List Bool) : DivInv z (divInit z) :=
  ⟨_, [], [], rfl, by simp, by simp, fun _ => ⟨by simp [bitsVal], by simpa [bitsVal]⟩⟩

/-- The value step of a long-division round: from `(q·b + r)·2^(|R|+1) + R̄ c = a`, both the
subtracting and the non-subtracting round give the invariant for the shorter `R`. -/
private theorem div_value_step {Q ρ v c P T a : ℕ} (hc : c ≤ 1)
    (h : (Q * v + ρ) * (2 * P) + (T + c * P) = a) (hρ : ρ < v) :
    (v ≤ c + 2 * ρ → ((1 + 2 * Q) * v + (c + 2 * ρ - v)) * P + T = a ∧ c + 2 * ρ - v < v) ∧
    (¬ v ≤ c + 2 * ρ → ((2 * Q) * v + (c + 2 * ρ)) * P + T = a ∧ c + 2 * ρ < v) := by
  refine ⟨fun hle => ⟨?_, by omega⟩, fun hlt => ⟨?_, by omega⟩⟩
  · have : (1 + 2 * Q) * v + (c + 2 * ρ - v) = 2 * (Q * v + ρ) + c := by
      have := Nat.sub_add_cancel hle; nlinarith
    rw [this, ← h]; ring
  · rw [← h]; ring

/-- The long-division round preserves the invariant, and shortens a nonempty `R`.

**Proof sketch.** Consuming the next bit `c` of `R` turns `v = q·b + r` into `2v + c`; with
`r' = 2r + c < 2b`, subtracting `b` when it fits keeps `r < b` and sets the new quotient bit
(`div_value_step`). Each round removes one bit of `R` and adds at most one to `r` and `q`. -/
theorem divInv_step {z S : List Bool} (h : DivInv z S) :
    DivInv z (divStep S) ∧
      ((pairFstD (pairSndD S)) ≠ [] →
        (pairFstD (pairSndD (divStep S))).length < (pairFstD (pairSndD S)).length) ∧
      ((pairFstD (pairSndD S)) = [] → divStep S = S) := by
  obtain ⟨R, r, q, rfl, hl1, hl2, hv⟩ := h
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  cases R with
  | nil => exact ⟨by simpa [divStep, isNilB] using ⟨[], r, q, rfl, hl1, hl2, hv⟩,
      by simp, fun _ => by simp [divStep, isNilB]⟩
  | cons c R =>
    refine ⟨?_, fun _ => ?_, by simp⟩
    swap
    · unfold divStep; split_ifs <;> simp_all [isNilB]
    have hc : c.toNat ≤ 1 := by cases c <;> simp
    have hrev : bitsVal (c :: R).reverse = bitsVal R.reverse + c.toNat * 2 ^ R.length := by
      rw [List.reverse_cons, bitsVal_append_singleton, List.length_reverse]
    have hr' : bitsVal (c :: r) = c.toNat + 2 * bitsVal r := rfl
    unfold divStep
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, isNilB, List.cons_ne_nil,
      decide_false, Bool.false_eq_true, if_false, List.headD_cons, List.drop_succ_cons,
      List.drop_zero, le, sub]
    split_ifs with hle
    · refine ⟨R, _, true :: q, rfl, ?_, by simp at hl2 ⊢; omega, fun hb => ?_⟩
      · have := length_bits_le_of_le (c :: r) (n := bitsVal (c :: r) - bitsVal (pairSndD z))
          (Nat.sub_le _ _) le_rfl
        simp at hl1 this ⊢; omega
      · obtain ⟨hv1, hv2⟩ := hv hb
        rw [List.length_cons, pow_succ, hrev] at hv1
        have := (div_value_step (Q := bitsVal q) (ρ := bitsVal r)
          (P := 2 ^ R.length) (T := bitsVal R.reverse) (a := bitsVal (pairFstD z)) hc
          (by rw [← hv1]; ring) hv2).1 (by simpa [hr'] using hle)
        simp only [bitsVal_bits, bitsVal, Bool.toNat_true]
        exact this
    · refine ⟨R, _, false :: q, rfl, by simp at hl1 ⊢; omega, by simp at hl2 ⊢; omega,
        fun hb => ?_⟩
      obtain ⟨hv1, hv2⟩ := hv hb
      rw [List.length_cons, pow_succ, hrev] at hv1
      have := (div_value_step (Q := bitsVal q) (ρ := bitsVal r)
        (P := 2 ^ R.length) (T := bitsVal R.reverse) (a := bitsVal (pairFstD z)) hc
        (by rw [← hv1]; ring) hv2).2 (by simpa [hr'] using hle)
      simp only [bitsVal, Bool.toNat_false, zero_add]
      exact this

/-- A state satisfying the division invariant has length at most `7(|z| + 1)`. -/
theorem length_le_of_divInv {z S : List Bool} (h : DivInv z S) :
    S.length ≤ 7 * (z.length + 1) := by
  obtain ⟨R, r, q, rfl, hl1, hl2, -⟩ := h
  have hz := length_pair_components_le z
  simp only [length_pairEncode]
  omega

/-- The division loop: `|z| + 1` long-division rounds from `divInit z`. -/
def divLoop (z : List Bool) : List Bool := divStep^[1 * (z.length + 1) ^ 1] (divInit z)

/-- The division loop is polynomial-time. -/
theorem polyTimeComputable_divLoop : PolyTimeComputable divLoop := by
  have hinit : PolyTimeComputable divInit :=
    polyTimeComputable_pairSndD.pairEncode
      ((polyTimeComputable_reverse.comp polyTimeComputable_pairFstD).pairEncode
        (polyTimeComputable_const _))
  exact polyTimeComputable_iterate polyTimeComputable_divStep hinit 1 1 7 1 (fun z i _ => by
    simpa using length_le_of_divInv
      (iterate_invariant (DivInv z) (fun _ h => (divInv_step h).1) i (divInv_init z)))

/-- For a nonzero divisor the division loop ends with quotient slot `a / b` and remainder
slot `a % b` (by value).

**Proof sketch.** `|R|` drops each round (`iterate_measure_eq_zero`), so the final state has
`R = []`, where the invariant reads `q·b + r = a`, `r < b`; conclude by
`Nat.div_mod_unique`. -/
theorem divLoop_spec (z : List Bool) (hb : 0 < bitsVal (pairSndD z)) :
    bitsVal (pairSndD (pairSndD (pairSndD (divLoop z)))) =
        bitsVal (pairFstD z) / bitsVal (pairSndD z) ∧
      bitsVal (pairFstD (pairSndD (pairSndD (divLoop z)))) =
        bitsVal (pairFstD z) % bitsVal (pairSndD z) := by
  have hμ := iterate_measure_eq_zero (g := divStep) (DivInv z)
    (fun S => (pairFstD (pairSndD S)).length) (fun _ h => (divInv_step h).1)
    (fun S h hpos => (divInv_step h).2.1 (List.ne_nil_of_length_pos hpos))
    (fun S h h0 => (divInv_step h).2.2 (List.length_eq_zero_iff.mp h0))
    (1 * (z.length + 1) ^ 1) (divInit z) (divInv_init z)
    (by simp [divInit]; have := length_pairFstD_le z; omega)
  obtain ⟨R, r, q, he, -, -, hv⟩ :=
    iterate_invariant (DivInv z) (fun _ h => (divInv_step h).1) (1 * (z.length + 1) ^ 1)
      (divInv_init z)
  rw [he] at hμ
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_eq_zero_iff] at hμ
  subst hμ
  obtain ⟨hv1, hv2⟩ := hv hb
  simp only [List.length_nil, pow_zero, mul_one, List.reverse_nil, bitsVal, add_zero] at hv1
  rw [divLoop, he]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  exact ((Nat.div_mod_unique hb).mpr ⟨by rw [← hv1]; ring, hv2⟩).imp Eq.symm Eq.symm

/-- **Binary division is polynomial-time** (infrastructure for [AB09 §7.2]; not itself a
result of the book): `0` for a zero divisor, else the normalized quotient slot of the
division loop. -/
theorem polyTimeComputable_div : PolyTimeComputable div := by
  convert polyTimeComputable_ite (polyTimeComputable_isZero.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_const [])
    (polyTimeComputable_normBits.comp (polyTimeComputable_slot4.comp polyTimeComputable_divLoop))
    using 1
  funext z
  simp only [Function.comp_apply, div]
  by_cases hb : bitsVal (pairSndD z) = 0
  · simp [hb, Nat.zero_bits]
  · simp only [hb, decide_false, Bool.false_eq_true, if_false]
    rw [(divLoop_spec z (Nat.pos_of_ne_zero hb)).1]

/-- **Binary remainder is polynomial-time** (infrastructure for [AB09 §7.2]; not itself a
result of the book): `a` for a zero divisor, else the normalized remainder slot of the
division loop. -/
theorem polyTimeComputable_mod : PolyTimeComputable mod := by
  have hs3 : PolyTimeComputable (fun S => pairFstD (pairSndD (pairSndD S))) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_slot3
  convert polyTimeComputable_ite (polyTimeComputable_isZero.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_normBits.comp polyTimeComputable_pairFstD)
    (polyTimeComputable_normBits.comp (hs3.comp polyTimeComputable_divLoop))
    using 1
  funext z
  simp only [Function.comp_apply, mod]
  by_cases hb : bitsVal (pairSndD z) = 0
  · simp [hb]
  · simp only [hb, decide_false, Bool.false_eq_true, if_false]
    rw [(divLoop_spec z (Nat.pos_of_ne_zero hb)).2]

end BinArith

end Complexity
