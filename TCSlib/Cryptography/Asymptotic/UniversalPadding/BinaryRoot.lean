/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Unary
import TCSlib.Cryptography.Asymptotic.UniversalPadding.Parameter

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The binary floor-root computation for Levin padding

A guarded word iteration bisects an interval containing the recovered parameter. Its state has linear binary width, and every round uses the shared binary arithmetic interface.

## Main definitions

The private search state retains the normalized argument, a word whose length counts the remaining rounds, and the lower endpoint.

## Main results

* `TCSlib.Cryptography.PadQuad.polyTimeComputable_shifted_root` computes the canonical binary word of the recovered parameter minus one.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010. (§2.13, Lemma 64.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

open Turing Complexity Complexity.BinArith TCSlib.Cryptography Complexity.LogProg

attribute [local irreducible] PadQuad.nu pairEncode pairFstD pairSndD
attribute [local irreducible] BinArith.add BinArith.sub BinArith.mul BinArith.le
attribute [local irreducible] transduce PolyTimeComputable

namespace TCSlib.Cryptography.PadQuad

/-- Any fixed power of a binary input is computable in polynomial time by repeated
binary multiplication, with both factors normalized at every call. -/
private theorem polyTimeComputable_fixedPower (d : ℕ) :
    PolyTimeComputable (fun z => Nat.bits (bitsVal z ^ d)) := by
  induction d with
  | zero => simpa only [pow_zero] using polyTimeComputable_const (Nat.bits 1)
  | succ d ih =>
      convert polyTimeComputable_mul.comp (ih.pairEncode polyTimeComputable_normBits) using 1
      funext z
      simp only [Function.comp_apply, mul_pairEncode, pow_succ]

/-- The initialization retains the normalized input, its original length as
remaining rounds, and the lower endpoint zero. -/
private def init (z : List Bool) : List Bool :=
  pairEncode (Nat.bits (bitsVal z)) (pairEncode z (Nat.bits 0))

/-- On a state with unread tokens, the midpoint of the search interval
adds the power of two indexed by the remaining length after this round. -/
private def midpoint (s : List Bool) : List Bool :=
  BinArith.add (pairEncode (pairSndD (pairSndD s))
    (Nat.bits (2 ^ ((pairFstD (pairSndD s)).drop 1).length)))

/-- Compare the midpoint's fixed power with the input. The accepted lower
endpoint is retained as a binary word, and the remaining width decreases by one. -/
private def round (d : ℕ) (s : List Bool) : List Bool :=
  if pairFstD (pairSndD s) = [] then s
  else
    let cand := midpoint s
    let test := BinArith.le
      (pairEncode (Nat.bits (bitsVal cand ^ d)) (pairFstD s))
    pairEncode (pairFstD s)
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (if test then cand else pairSndD (pairSndD s)))

/-- Each search round is polynomial-time by the word projections and the
binary addition, multiplication and comparison interfaces. -/
private theorem polyTimeComputable_round (d : ℕ) : PolyTimeComputable (round d) := by
  have htail : PolyTimeComputable (fun s => (pairFstD (pairSndD s)).drop 1) :=
    polyTimeComputable_drop 1 |>.comp polyTimeComputable_slot2
  have hmid : PolyTimeComputable midpoint :=
    polyTimeComputable_add.comp
      (polyTimeComputable_slot3.pairEncode (polyTimeComputable_powerOfTwo.comp htail))
  have htest := polyTimeComputable_le.comp
    (((polyTimeComputable_fixedPower d).comp hmid).pairEncode polyTimeComputable_pairFstD)
  have hupdate := polyTimeComputable_ite htest hmid polyTimeComputable_slot3
  have hbranch := polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_slot2) polyTimeComputable_id
    (polyTimeComputable_pairFstD.pairEncode (htail.pairEncode hupdate))
  simpa only [Function.comp_apply, round, decide_eq_true_eq] using hbranch

/-- The true root lies in the half-open interval of width two to the number
of remaining rounds, with the original normalized argument retained. -/
private def Invariant (d : ℕ) (z s : List Bool) : Prop :=
  ∃ (u : List Bool) (r : ℕ),
    s = pairEncode (Nat.bits (bitsVal z)) (pairEncode u (Nat.bits r)) ∧
      u.length ≤ z.length ∧ r ≤ PadQuad.nu d (bitsVal z) ∧
      PadQuad.nu d (bitsVal z) < r + 2 ^ u.length

/-- The full binary width covers every possible root of the input. -/
private theorem invariant_init (d : ℕ) (z : List Bool) : Invariant d z (init z) := by
  refine ⟨z, 0, rfl, le_rfl, Nat.zero_le _, ?_⟩
  rw [Nat.zero_add]
  exact (PadQuad.nu_le _ _).trans_lt (bitsVal_lt_two_pow z)

/-- A nonempty round splits the invariant interval into equal halves. The
midpoint's power is within the original value exactly when the midpoint is at
most the root. The remaining word loses one letter. An empty round is fixed. -/
private theorem invariant_round {d : ℕ} (hd : 1 ≤ d) {z s : List Bool}
    (hs : Invariant d z s) : Invariant d z (round d s) ∧
      (0 < (pairFstD (pairSndD s)).length →
        (pairFstD (pairSndD (round d s))).length < (pairFstD (pairSndD s)).length) ∧
      ((pairFstD (pairSndD s)).length = 0 → round d s = s) := by
  obtain ⟨u, r, rfl, hlu, hlow, hhigh⟩ := hs
  cases u with
  | nil =>
      simp only [round, pairFstD_pairEncode, pairSndD_pairEncode, ↓reduceIte,
        List.length_nil, Nat.lt_irrefl, false_implies, true_implies, and_true]
      exact ⟨[], r, rfl, hlu, hlow, hhigh⟩
  | cons b u =>
      let v := PadQuad.nu d (bitsVal z)
      let k := 2 ^ u.length
      have htest : (r + k) ^ d ≤ bitsVal z ↔ r + k ≤ v :=
        ⟨PadQuad.le_nu hd, fun h => (Nat.pow_le_pow_left h _).trans (PadQuad.nu_pow_le hd _)⟩
      have hwidth : 2 ^ (b :: u).length = k + k := by
        simp only [List.length_cons, pow_succ, k, Nat.mul_two]
      rw [hwidth] at hhigh
      have hr :
          round d (pairEncode (Nat.bits (bitsVal z)) (pairEncode (b :: u) (Nat.bits r))) =
            pairEncode (Nat.bits (bitsVal z))
              (pairEncode u (Nat.bits (if r + k ≤ v then r + k else r))) := by
        simp only [round, pairFstD_pairEncode, pairSndD_pairEncode, List.cons_ne_nil,
          ↓reduceIte, midpoint, List.drop_succ_cons, List.drop_zero, add_pairEncode,
          bitsVal_bits, le_pairEncode, decide_eq_true_eq]
        change pairEncode (Nat.bits (bitsVal z))
          (pairEncode u (if (r + k) ^ d ≤ bitsVal z then Nat.bits (r + k) else Nat.bits r)) = _
        by_cases h : r + k ≤ v
        · rw [if_pos (htest.mpr h), if_pos h]
        · rw [if_neg (fun h' => h (htest.mp h')), if_neg h]
      rw [hr]
      refine ⟨?_, ?_, ?_⟩
      · have hu : u.length ≤ z.length := by simp only [List.length_cons] at hlu; omega
        by_cases h : r + k ≤ v
        · refine ⟨u, r + k, by rw [if_pos h], hu, h, ?_⟩
          change v < r + k + k
          omega
        · exact ⟨u, r, by rw [if_neg h], hu, hlow, by exact Nat.lt_of_not_ge h⟩
      · simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons]
        omega
      · simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons]
        omega

/-- The interval representation is linear in the original binary width.
The lower endpoint fits because it is at most the root of the input. -/
private theorem length_le_of_invariant {d : ℕ} {z s : List Bool} (h : Invariant d z s) :
    s.length ≤ 5 * (z.length + 1) := by
  obtain ⟨u, r, rfl, hu, hr, -⟩ := h
  have hn := length_bits_bitsVal_le z
  have hl := length_bits_le_of_le z (hr.trans (PadQuad.nu_le _ _)) le_rfl
  simp only [length_pairEncode]
  omega

/-- The binary root can be computed in time polynomial in the binary input
width. The truncated subtraction produces the shifted root used by the
sharp unary polynomial evaluator.

**Proof sketch.** Reuse the guarded word loop with the interval round. The
lower endpoint is never above the root, and the interval halves at every
round until the remaining word is empty. The final interval has width one.
Project the lower endpoint and subtract one. -/
theorem polyTimeComputable_shifted_root (d : ℕ) (hd : 1 ≤ d) :
    PolyTimeComputable (fun z => Nat.bits (PadQuad.nu d (bitsVal z) - 1)) := by
  let loops (z : List Bool) := (round d)^[z.length + 1] (init z)
  have hinit : PolyTimeComputable init :=
    polyTimeComputable_normBits.pairEncode
      (polyTimeComputable_id.pairEncode (polyTimeComputable_const _))
  have hpreserve : ∀ (z s : List Bool), Invariant d z s → Invariant d z (round d s) :=
    fun _ _ h => (invariant_round hd h).1
  have hloops : PolyTimeComputable loops := by
    simpa only [pow_one, one_mul] using
      BinArith.polyTimeComputable_iterate (polyTimeComputable_round d) hinit 1 1 5 1
        (fun z i _ => by simpa only [pow_one] using
          length_le_of_invariant (iterate_invariant (Invariant d z) (hpreserve z) i
            (invariant_init d z)))
  have hresult (z : List Bool) :
      pairSndD (pairSndD (loops z)) = Nat.bits (PadQuad.nu d (bitsVal z)) := by
    have hzero := iterate_measure_eq_zero (g := round d) (Invariant d z)
      (fun s => (pairFstD (pairSndD s)).length) (hpreserve z)
      (fun _ h => (invariant_round hd h).2.1)
      (fun _ h => (invariant_round hd h).2.2) (z.length + 1) (init z)
      (invariant_init d z) (by simp only [init, pairFstD_pairEncode, pairSndD_pairEncode]; omega)
    change (pairFstD (pairSndD (loops z))).length = 0 at hzero
    obtain ⟨u, r, hword, -, hlow, hhigh⟩ :=
      iterate_invariant (Invariant d z) (hpreserve z) (z.length + 1) (invariant_init d z)
    change loops z = _ at hword
    rw [hword] at hzero ⊢
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at hzero ⊢
    rw [hzero, pow_zero] at hhigh
    congr 1
    omega
  have hsub := polyTimeComputable_sub.comp
    ((polyTimeComputable_slot3.comp hloops).pairEncode (polyTimeComputable_const (Nat.bits 1)))
  convert hsub using 1
  funext z
  simp only [Function.comp_apply, hresult, sub_pairEncode]


end TCSlib.Cryptography.PadQuad
