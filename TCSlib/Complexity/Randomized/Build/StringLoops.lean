/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Bool.Count
import TCSlib.Complexity.Randomized.Build.StateLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# String loops: majority, pairwise xor, equality test and block map

The four string functions of `TCSlib.Complexity.Randomized.Repetition` —
`Complexity.polyTimeComputable_majority` (the vote of [PS10, Algorithm 89.6]),
`Complexity.polyTimeComputable_pairXor` (the one-time pad of [PS10, Algorithms 92.1 and 99.1]
and the mask of [PS10, Algorithm 104.3]), `Complexity.polyTimeComputable_pairEq` (the test
`f(z_i) = y` of [PS10, Algorithm 38.5]) and `Complexity.polyTimeComputable_blockMap` (the
blockwise evaluation of `prodFun` in [PS10, Theorem 35.1]) — are **state loops** in the sense
of `TCSlib.Complexity.Randomized.Build.StateLoop`: a state word `⟨z, s⟩` retains the input `z`,
the state `s` consumes the input one bit (or one block) per round, a test `acc` fires for the
first time when the input is exhausted, and `out` reads the answer off the final state.

This file supplies, for each of the four, the loop data (`start`, `step`, `acc`, `out`, the
number of rounds), the polynomial-time proofs of the data, the closed form of the orbit, its
length bound and the values of `acc` and `out` along it:

* `Complexity.StateLoop.MajLoop` — state `⟨rest, ⟨1^{#true}, 1^{#false}⟩⟩`, one bit per round;
* `Complexity.StateLoop.XorLoop` — state `⟨a', ⟨b', c⟩⟩`, one xor bit appended per round;
* `Complexity.StateLoop.EqLoop` — state `⟨a', ⟨b', flag⟩⟩`, the flag recording a mismatch;
* `Complexity.StateLoop.BlockLoop` — state `⟨rest, c⟩`, one block of `b(|fst z|)` bits per
  round, the accumulator extended by `g` of the block.

The assembly through `Complexity.polyTimeComputable_iterateFind` (the private state-loop form
`polyTimeComputable_stateFind`) and the four public theorems live in
`TCSlib.Complexity.Randomized.Repetition`.

## Main definitions

* `Complexity.StateLoop.MajLoop`, `Complexity.StateLoop.XorLoop`, `Complexity.StateLoop.EqLoop`,
  `Complexity.StateLoop.BlockLoop` — the state-loop data of the four string functions.

## Main results

* The `orbit_eq` closed forms, `orbit_length_le` bounds, `acc_orbit_false`/`acc_orbit_true`
  values and `out_orbit` identities of the four loops; `Complexity.StateLoop.EqLoop.verdict_eq`
  (equal lengths and equal prefixes is equality).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Algorithms 89.6, 92.1, 99.1 and 104.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines; §2.2, the class FP.)
-/

namespace Complexity.StateLoop

open Turing

/-! ### `majority`: consume the word, counting `true`s and `false`s in unary -/

namespace MajLoop

/-- The initial state `⟨w, ⟨[], []⟩⟩`: the whole word remains, both counters empty. -/
def start (w : List Bool) : List Bool := pairEncode w (pairEncode [] [])

/-- The step on `⟨w, ⟨rest, ⟨t, f⟩⟩⟩`: drop the first bit of `rest` and append a token to the
counter of its value. -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (if (pairFstD (pairSndD v)).headD false then
      pairEncode (true :: pairFstD (pairSndD (pairSndD v))) (pairSndD (pairSndD (pairSndD v)))
    else pairEncode (pairFstD (pairSndD (pairSndD v))) (true :: pairSndD (pairSndD (pairSndD v))))

/-- The acceptance test: the remaining word is empty. -/
def acc (v : List Bool) : Bool := decide (pairFstD (pairSndD v) = [])

/-- The output: the verdict `#false + 1 ≤ #true`, i.e. a strict majority of `true`. -/
def out (v : List Bool) : List Bool :=
  [decide ((true :: pairSndD (pairSndD (pairSndD v))).length ≤
    (pairFstD (pairSndD (pairSndD v))).length)]

/-- The remaining word of the state word. -/
theorem rest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The `true` counter of the state word. -/
theorem trues_poly : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The `false` counter of the state word. -/
theorem falses_poly : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_id.pairEncode (polyTimeComputable_const (pairEncode [] []))

/-- The step is polynomial-time (`Complexity.polyTimeComputable_ite` on the head bit). -/
theorem step_poly : PolyTimeComputable step := by
  have hp : PolyTimeComputable fun v => [(pairFstD (pairSndD v)).headD false] :=
    headBit_poly.comp rest_poly
  have h := (tail_poly.comp rest_poly).pairEncode (polyTimeComputable_ite hp
    (((cons_poly true).comp trues_poly).pairEncode falses_poly)
    (trues_poly.pairEncode ((cons_poly true).comp falses_poly)))
  convert h using 1

/-- The acceptance test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun v => [acc v] :=
  isNil_poly.comp rest_poly

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  lenLe_comp trues_poly ((cons_poly true).comp falses_poly)

/-- The closed form of the orbit for `i ≤ |w|`:
`⟨w.drop i, ⟨1^{#true (w.take i)}, 1^{#false (w.take i)}⟩⟩`. -/
theorem orbit_eq (w : List Bool) : ∀ i ≤ w.length, orbit start step w i =
    pairEncode (w.drop i)
      (pairEncode (List.replicate ((w.take i).count true) true)
        (List.replicate ((w.take i).count false) true))
  | 0, _ => by simp [start]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq w i (Nat.le_of_succ_le hi)]
    obtain ⟨c, hc⟩ : ∃ c, w[i]? = some c := ⟨_, List.getElem?_eq_getElem hi⟩
    have htake : w.take (i + 1) = w.take i ++ [c] := by rw [List.take_succ, hc]; rfl
    have hhead : (w.drop i).headD false = c := by
      rw [List.headD_eq_head?_getD, List.head?_drop, hc]; rfl
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop, hhead, htake,
      List.count_append]
    cases c <;> simp [List.replicate_succ]

/-- The states of the first `|w|` rounds have length at most `5|w| + 4`. -/
theorem orbit_length_le (w : List Bool) (i : ℕ) (hi : i ≤ w.length) :
    (orbit start step w i).length ≤ 5 * w.length + 4 := by
  rw [orbit_eq w i hi, length_pairEncode, length_pairEncode, List.length_replicate,
    List.length_replicate, List.length_drop]
  have h1 : (w.take i).count true ≤ (w.take i).length := List.count_le_length
  have h2 : (w.take i).count false ≤ (w.take i).length := List.count_le_length
  rw [List.length_take] at h1 h2
  omega

/-- Before round `|w|` the remaining word is nonempty, so `acc` is `false`. -/
theorem acc_orbit_false (w : List Bool) (i : ℕ) (hi : i < w.length) :
    acc (pairEncode w (orbit start step w i)) = false := by
  rw [orbit_eq w i hi.le]
  simp [acc, List.drop_eq_nil_iff, hi]

/-- At round `|w|` the remaining word is empty, so `acc` is `true`. -/
theorem acc_orbit_true (w : List Bool) : acc (pairEncode w (orbit start step w w.length)) = true := by
  rw [orbit_eq w w.length le_rfl]
  simp [acc]

/-- At round `|w|` the output is the majority verdict `[decide (|w| < 2 · #true w)]`
(`List.count_true_add_count_false`). -/
theorem out_orbit (w : List Bool) :
    out (pairEncode w (orbit start step w w.length)) = [decide (w.length < 2 * w.count true)] := by
  rw [orbit_eq w w.length le_rfl]
  simp only [out, pairFstD_pairEncode, pairSndD_pairEncode, List.take_length, List.length_cons,
    List.length_replicate]
  have := List.count_true_add_count_false w
  congr 1
  exact decide_eq_decide.mpr ⟨fun h' => by omega, fun h' => by omega⟩

end MajLoop

/-! ### `pairXor`: consume both components, emitting one xor bit per round -/

namespace XorLoop

/-- The initial state `⟨fst z, ⟨snd z, []⟩⟩`: both components remain, empty accumulator. -/
def start (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairEncode (pairSndD z) [])

/-- The step on `⟨z, ⟨a, ⟨b, c⟩⟩⟩`: `⟨a.tail, ⟨b.tail, c ++ [xor (head a) (head b)]⟩⟩`. -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (pairEncode (pairFstD (pairSndD (pairSndD v))).tail
      (pairSndD (pairSndD (pairSndD v)) ++
        [xor ((pairFstD (pairSndD v)).headD false)
          ((pairFstD (pairSndD (pairSndD v))).headD false)]))

/-- The acceptance test: one of the two remaining components is empty. -/
def acc (v : List Bool) : Bool :=
  decide (pairFstD (pairSndD v) = []) || decide (pairFstD (pairSndD (pairSndD v)) = [])

/-- The output: the accumulator. -/
def out (v : List Bool) : List Bool := pairSndD (pairSndD (pairSndD v))

/-- The number of rounds: the length of the shorter component. -/
def rounds (z : List Bool) : ℕ := min (pairFstD z).length (pairSndD z).length

/-- The remaining first component of the state word. -/
theorem fstRest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The remaining second component of the state word. -/
theorem sndRest_poly : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The accumulator of the state word. -/
theorem accum_poly : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The xor of the two head bits of the state word, as a one-bit output. -/
theorem xorBit_poly : PolyTimeComputable fun v =>
    [xor ((pairFstD (pairSndD v)).headD false) ((pairFstD (pairSndD (pairSndD v))).headD false)] := by
  have hpa : PolyTimeComputable fun v => [(pairFstD (pairSndD v)).headD false] :=
    headBit_poly.comp fstRest_poly
  have hpb : PolyTimeComputable fun v => [(pairFstD (pairSndD (pairSndD v))).headD false] :=
    headBit_poly.comp sndRest_poly
  exact xor_poly hpa hpb

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step :=
  (tail_poly.comp fstRest_poly).pairEncode
    ((tail_poly.comp sndRest_poly).pairEncode (accum_poly.append xorBit_poly))

/-- The acceptance test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun v => [acc v] := by
  have ha : PolyTimeComputable fun v => [decide (pairFstD (pairSndD v) = [])] :=
    isNil_poly.comp fstRest_poly
  have hb : PolyTimeComputable fun v => [decide (pairFstD (pairSndD (pairSndD v)) = [])] :=
    isNil_poly.comp sndRest_poly
  exact or_poly ha hb

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := accum_poly

/-- The closed form of the orbit for `i ≤ rounds z`:
`⟨a.drop i, ⟨b.drop i, (zipWith xor a b).take i⟩⟩` with `a = fst z`, `b = snd z`. -/
theorem orbit_eq (z : List Bool) : ∀ i ≤ rounds z, orbit start step z i =
    pairEncode ((pairFstD z).drop i)
      (pairEncode ((pairSndD z).drop i) ((List.zipWith xor (pairFstD z) (pairSndD z)).take i))
  | 0, _ => by simp [start]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq z i (Nat.le_of_succ_le hi)]
    have ha : i < (pairFstD z).length := by unfold rounds at hi; omega
    have hb : i < (pairSndD z).length := by unfold rounds at hi; omega
    have hza : (pairFstD z)[i]? = some (pairFstD z)[i] := List.getElem?_eq_getElem ha
    have hzb : (pairSndD z)[i]? = some (pairSndD z)[i] := List.getElem?_eq_getElem hb
    have hzip : (List.zipWith xor (pairFstD z) (pairSndD z))[i]? =
        some (xor (pairFstD z)[i] (pairSndD z)[i]) := by
      rw [List.getElem?_zipWith, hza, hzb]
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop,
      List.headD_eq_head?_getD, List.head?_drop, hza, hzb, Option.getD_some, List.take_succ, hzip,
      Option.toList_some]

/-- The states of the first `rounds z` rounds have length at most `5|z| + 4`. -/
theorem orbit_length_le (z : List Bool) (i : ℕ) (hi : i ≤ rounds z) :
    (orbit start step z i).length ≤ 5 * z.length + 4 := by
  rw [orbit_eq z i hi, length_pairEncode, length_pairEncode, List.length_drop, List.length_drop,
    List.length_take, List.length_zipWith]
  have := length_pairFstD_add_pairSndD_le z
  omega

/-- Before round `rounds z` both remaining components are nonempty, so `acc` is `false`. -/
theorem acc_orbit_false (z : List Bool) (i : ℕ) (hi : i < rounds z) :
    acc (pairEncode z (orbit start step z i)) = false := by
  rw [orbit_eq z i hi.le]
  unfold rounds at hi
  simp only [acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, List.drop_eq_nil_iff]
  omega

/-- At round `rounds z` one remaining component is empty, so `acc` is `true`. -/
theorem acc_orbit_true (z : List Bool) : acc (pairEncode z (orbit start step z (rounds z))) = true := by
  rw [orbit_eq z _ le_rfl]
  simp only [acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_true_iff,
    decide_eq_true_eq, List.drop_eq_nil_iff, rounds]
  omega

/-- At round `rounds z` the output is `zipWith xor (fst z) (snd z)`. -/
theorem out_orbit (z : List Bool) :
    out (pairEncode z (orbit start step z (rounds z))) =
      List.zipWith xor (pairFstD z) (pairSndD z) := by
  rw [orbit_eq z _ le_rfl]
  simp only [out, pairSndD_pairEncode]
  have : rounds z = (List.zipWith xor (pairFstD z) (pairSndD z)).length := by
    rw [List.length_zipWith]; rfl
  rw [this, List.take_length]

end XorLoop

/-! ### `pairEq`: consume both components, recording the first mismatch -/

namespace EqLoop

/-- The step on `⟨z, ⟨a, ⟨b, flag⟩⟩⟩`: `⟨a.tail, ⟨b.tail, flag'⟩⟩` where `flag'` is `[true]` if the
head bits differ and `flag` otherwise (`[]` means "no mismatch so far"). -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (pairEncode (pairFstD (pairSndD (pairSndD v))).tail
      (if xor ((pairFstD (pairSndD v)).headD false)
          ((pairFstD (pairSndD (pairSndD v))).headD false) then [true]
        else pairSndD (pairSndD (pairSndD v))))

/-- The output: both remaining components are empty and no mismatch was recorded. -/
def out (v : List Bool) : List Bool :=
  [decide (pairFstD (pairSndD v) = []) && decide (pairFstD (pairSndD (pairSndD v)) = []) &&
    decide (pairSndD (pairSndD (pairSndD v)) = [])]

/-- The mismatch flag after `i` rounds: `[]` if the first `i` bits agree, `[true]` otherwise. -/
def flag (a b : List Bool) (i : ℕ) : List Bool := if a.take i = b.take i then [] else [true]

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step :=
  (tail_poly.comp XorLoop.fstRest_poly).pairEncode
    ((tail_poly.comp XorLoop.sndRest_poly).pairEncode
      (polyTimeComputable_ite XorLoop.xorBit_poly (polyTimeComputable_const [true])
        XorLoop.accum_poly))

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := by
  have ha : PolyTimeComputable fun v => [decide (pairFstD (pairSndD v) = [])] :=
    isNil_poly.comp XorLoop.fstRest_poly
  have hb : PolyTimeComputable fun v => [decide (pairFstD (pairSndD (pairSndD v)) = [])] :=
    isNil_poly.comp XorLoop.sndRest_poly
  have hc : PolyTimeComputable fun v => [decide (pairSndD (pairSndD (pairSndD v)) = [])] :=
    isNil_poly.comp XorLoop.accum_poly
  exact polyTimeComputable_and (polyTimeComputable_and ha hb) hc

/-- Two words ending in one bit each are equal iff their bodies and their last bits are. -/
theorem append_singleton_eq_iff (l₁ l₂ : List Bool) (c₁ c₂ : Bool) :
    l₁ ++ [c₁] = l₂ ++ [c₂] ↔ l₁ = l₂ ∧ c₁ = c₂ := by
  constructor
  · intro h
    exact ⟨List.append_inj_left' h rfl, List.singleton_inj.mp (List.append_inj_right' h rfl)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The flag after `i + 1` rounds: set if the `i`-th bits differ, else unchanged. -/
theorem flag_succ (a b : List Bool) (i : ℕ) (ca cb : Bool) (hca : a[i]? = some ca)
    (hcb : b[i]? = some cb) :
    flag a b (i + 1) = if xor ca cb then [true] else flag a b i := by
  unfold flag
  rw [List.take_succ, List.take_succ, hca, hcb, Option.toList_some, Option.toList_some]
  cases ca <;> cases cb <;> simp [append_singleton_eq_iff]

/-- The flag has length at most one. -/
theorem length_flag_le (a b : List Bool) (i : ℕ) : (flag a b i).length ≤ 1 := by
  unfold flag
  split_ifs <;> simp

/-- The closed form of the orbit for `i ≤ XorLoop.rounds z`:
`⟨a.drop i, ⟨b.drop i, flag a b i⟩⟩` with `a = fst z`, `b = snd z`. -/
theorem orbit_eq (z : List Bool) : ∀ i ≤ XorLoop.rounds z, orbit XorLoop.start step z i =
    pairEncode ((pairFstD z).drop i)
      (pairEncode ((pairSndD z).drop i) (flag (pairFstD z) (pairSndD z) i))
  | 0, _ => by simp [XorLoop.start, flag]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq z i (Nat.le_of_succ_le hi)]
    have ha : i < (pairFstD z).length := by unfold XorLoop.rounds at hi; omega
    have hb : i < (pairSndD z).length := by unfold XorLoop.rounds at hi; omega
    have hza : (pairFstD z)[i]? = some (pairFstD z)[i] := List.getElem?_eq_getElem ha
    have hzb : (pairSndD z)[i]? = some (pairSndD z)[i] := List.getElem?_eq_getElem hb
    rw [flag_succ _ _ i _ _ hza hzb]
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop,
      List.headD_eq_head?_getD, List.head?_drop, hza, hzb, Option.getD_some]

/-- The states of the first `rounds z` rounds have length at most `5|z| + 5`. -/
theorem orbit_length_le (z : List Bool) (i : ℕ) (hi : i ≤ XorLoop.rounds z) :
    (orbit XorLoop.start step z i).length ≤ 5 * z.length + 5 := by
  rw [orbit_eq z i hi, length_pairEncode, length_pairEncode, List.length_drop, List.length_drop]
  have := length_pairFstD_add_pairSndD_le z
  have := length_flag_le (pairFstD z) (pairSndD z) i
  omega

/-- Before round `XorLoop.rounds z` both remaining components are nonempty, so `XorLoop.acc`
is `false`. -/
theorem acc_orbit_false (z : List Bool) (i : ℕ) (hi : i < XorLoop.rounds z) :
    XorLoop.acc (pairEncode z (orbit XorLoop.start step z i)) = false := by
  rw [orbit_eq z i hi.le]
  unfold XorLoop.rounds at hi
  simp only [XorLoop.acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, List.drop_eq_nil_iff]
  omega

/-- At round `XorLoop.rounds z` one remaining component is empty, so `XorLoop.acc` is `true`. -/
theorem acc_orbit_true (z : List Bool) :
    XorLoop.acc (pairEncode z (orbit XorLoop.start step z (XorLoop.rounds z))) = true := by
  rw [orbit_eq z _ le_rfl]
  simp only [XorLoop.acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_true_iff,
    decide_eq_true_eq, List.drop_eq_nil_iff, XorLoop.rounds]
  omega

/-- The verdict read off the final state is the equality test. -/
theorem verdict_eq (a b : List Bool) :
    (decide (a.drop (min a.length b.length) = []) && decide (b.drop (min a.length b.length) = []) &&
      decide (flag a b (min a.length b.length) = [])) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab
    simp [flag]
  · rw [decide_eq_false hab]
    rcases Nat.lt_trichotomy a.length b.length with hl | hl | hl
    · rw [Nat.min_eq_left hl.le]
      have : ¬ (b.drop a.length = []) := by rw [List.drop_eq_nil_iff]; omega
      simp [this]
    · rw [Nat.min_eq_left hl.le]
      have : flag a b a.length = [true] := by
        unfold flag
        rw [List.take_length, hl, List.take_length, if_neg hab]
      simp [this]
    · rw [Nat.min_eq_right hl.le]
      have : ¬ (a.drop b.length = []) := by rw [List.drop_eq_nil_iff]; omega
      simp [this]

/-- At round `rounds z` the output is `[decide (fst z = snd z)]`. -/
theorem out_orbit (z : List Bool) :
    out (pairEncode z (orbit XorLoop.start step z (XorLoop.rounds z))) =
      [decide (pairFstD z = pairSndD z)] := by
  rw [orbit_eq z _ le_rfl]
  simp only [out, pairFstD_pairEncode, pairSndD_pairEncode, XorLoop.rounds]
  rw [verdict_eq]

end EqLoop

/-! ### `blockMap`: consume the second component block by block -/

namespace BlockLoop

/-- The initial state `⟨snd z, []⟩`: the whole second component remains, empty accumulator. -/
def start (z : List Bool) : List Bool := pairEncode (pairSndD z) []

/-- The block length read off the state word `⟨z, s⟩`: `b(|fst z|)`. -/
def blk (b : PolyExpr) (v : List Bool) : ℕ := b.eval (pairFstD (pairFstD v)).length

/-- The step on `⟨z, ⟨rest, c⟩⟩`: `⟨rest.drop k, c ++ g (rest.take k)⟩` with `k = b(|fst z|)`. -/
def step (b : PolyExpr) (g : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode ((pairFstD (pairSndD v)).drop (blk b v))
    (pairSndD (pairSndD v) ++ g ((pairFstD (pairSndD v)).take (blk b v)))

/-- The acceptance test: fewer than `k` bits remain, or `k = 0`. -/
def acc (b : PolyExpr) (v : List Bool) : Bool :=
  decide ((true :: pairFstD (pairSndD v)).length ≤ blk b v) || decide (blk b v ≤ 0)

/-- The output: the accumulator. -/
def out (v : List Bool) : List Bool := pairSndD (pairSndD v)

/-- The number of rounds: the number of full blocks `|snd z| / b(|fst z|)`. -/
def rounds (b : PolyExpr) (z : List Bool) : ℕ :=
  (pairSndD z).length / b.eval (pairFstD z).length

/-- The unary parameter `fst z` of the state word. -/
theorem param_poly : PolyTimeComputable fun v => pairFstD (pairFstD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The remaining word of the state word. -/
theorem rest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The accumulator of the state word. -/
theorem accum_poly : PolyTimeComputable fun v => pairSndD (pairSndD v) :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])

/-- The step is polynomial-time (the typed cuts `Complexity.polyTimeComputable_pairDropPoly`
and `polyTimeComputable_pairTakePoly` on `⟨fst (fst v), rest⟩`). -/
theorem step_poly (b : PolyExpr) {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (step b g) := by
  have hdrop : PolyTimeComputable fun v => (pairFstD (pairSndD v)).drop (blk b v) := by
    convert (polyTimeComputable_pairDropPoly b).comp (param_poly.pairEncode rest_poly) using 1
    funext v
    simp [blk]
  have htake : PolyTimeComputable fun v => (pairFstD (pairSndD v)).take (blk b v) := by
    convert (polyTimeComputable_pairTakePoly b).comp (param_poly.pairEncode rest_poly) using 1
    funext v
    simp [blk]
  exact hdrop.pairEncode (accum_poly.append (hg.comp htake))

/-- The acceptance test is polynomial-time (two length tests against `1^{k}`). -/
theorem acc_poly (b : PolyExpr) : PolyTimeComputable fun v => [acc b v] := by
  have h1 : PolyTimeComputable fun v => [decide ((true :: pairFstD (pairSndD v)).length ≤ blk b v)] := by
    convert lenLe_comp (unaryPoly_comp b param_poly) ((cons_poly true).comp rest_poly) using 1
    funext v
    simp [blk]
  have h2 : PolyTimeComputable fun v => [decide (blk b v ≤ 0)] := by
    convert lenLe_comp (polyTimeComputable_const []) (unaryPoly_comp b param_poly) using 1
    funext v
    simp [blk]
  exact or_poly h1 h2

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := accum_poly

/-- The closed form of the orbit (all rounds): with `k = b(|fst z|)` and `s = snd z`,
`⟨s.drop (i k), g (block 0) ++ ⋯ ++ g (block (i-1))⟩` where `block j = (s.drop (j k)).take k`. -/
theorem orbit_eq (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) (i : ℕ) :
    orbit start (step b g) z i =
      pairEncode ((pairSndD z).drop (i * b.eval (pairFstD z).length))
        ((List.range i).flatMap fun j =>
          g (((pairSndD z).drop (j * b.eval (pairFstD z).length)).take
            (b.eval (pairFstD z).length))) := by
  induction i with
  | zero => simp [start]
  | succ i ih =>
    rw [orbit_succ, ih, Nat.succ_mul]
    simp only [step, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop,
      List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The states of the first `rounds b z` rounds have length at most
`2|z| + 2 + |z| · C (b(|z|) + 1)^c` when `|g y| ≤ C (|y| + 1)^c`.

**Proof sketch.** By `orbit_eq` the state is `⟨(snd z).drop (i k), acc_i⟩` with `k = b(|fst z|)`
and `acc_i` the concatenation of `i` chunks `g (block j)`; each block has length at most
`k ≤ b(|z|)` (`PolyExpr.eval_mono`, `Complexity.length_pairFstD_le`), so each chunk has length
at most `C (b(|z|) + 1)^c`, and `StateLoop.length_flatMap_range_le` bounds `|acc_i|` by
`i · C (b(|z|) + 1)^c ≤ |z| · C (b(|z|) + 1)^c` since `i ≤ |snd z| / k ≤ |z|`
(`Nat.div_le_self`, `length_pairFstD_add_pairSndD_le`); `PolyExpr.eval_subst` and
`PolyExpr.eval_normal` identify the bound with the stated expression. -/
theorem orbit_length_le (b : PolyExpr) (g : List Bool → List Bool) (C c : ℕ)
    (hg : ∀ y, (g y).length ≤ C * (y.length + 1) ^ c) (z : List Bool) (i : ℕ)
    (hi : i ≤ rounds b z) :
    (orbit start (step b g) z i).length ≤
      (PolyExpr.add (.mul (.const 2) .var)
        (.add (.const 2) (.mul .var ((PolyExpr.normal C c).subst b)))).eval z.length := by
  rw [orbit_eq, length_pairEncode, List.length_drop]
  have hk : b.eval (pairFstD z).length ≤ b.eval z.length := b.eval_mono (length_pairFstD_le z)
  have hzs := length_pairFstD_add_pairSndD_le z
  have hi' : i ≤ z.length :=
    hi.trans ((Nat.div_le_self _ _).trans (by omega))
  have hchunk : ∀ j < i, (g (((pairSndD z).drop (j * b.eval (pairFstD z).length)).take
      (b.eval (pairFstD z).length))).length ≤ C * (b.eval z.length + 1) ^ c := by
    intro j _
    refine (hg _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    rw [List.length_take]
    omega
  have hfm := length_flatMap_range_le _ _ i hchunk
  have hle := hfm.trans (Nat.mul_le_mul_right _ hi')
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
    PolyExpr.eval_subst, PolyExpr.eval_normal]
  generalize z.length * (C * (b.eval z.length + 1) ^ c) = Q at hle
  omega

/-- Before round `rounds b z` at least `k` bits remain and `k > 0`, so `acc` is `false`. -/
theorem acc_orbit_false (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) (i : ℕ)
    (hi : i < rounds b z) : acc b (pairEncode z (orbit start (step b g) z i)) = false := by
  rw [orbit_eq]
  simp only [acc, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons,
    List.length_drop, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  unfold rounds at hi
  have hk : 0 < b.eval (pairFstD z).length := by
    rcases Nat.eq_zero_or_pos (b.eval (pairFstD z).length) with h0 | h0
    · rw [h0, Nat.div_zero] at hi
      omega
    · exact h0
  have hmul := (Nat.le_div_iff_mul_le hk).mp hi
  rw [Nat.succ_mul] at hmul
  omega

/-- At round `rounds b z` fewer than `k` bits remain (or `k = 0`), so `acc` is `true`. -/
theorem acc_orbit_true (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) :
    acc b (pairEncode z (orbit start (step b g) z (rounds b z))) = true := by
  rw [orbit_eq]
  simp only [acc, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons,
    List.length_drop, Bool.or_eq_true_iff, decide_eq_true_eq, rounds]
  rcases Nat.eq_zero_or_pos (b.eval (pairFstD z).length) with hk | hk
  · right
    omega
  · left
    have h1 := Nat.lt_mul_div_succ (pairSndD z).length hk
    have h2 := Nat.div_mul_le_self (pairSndD z).length (b.eval (pairFstD z).length)
    rw [Nat.mul_succ, Nat.mul_comm (b.eval (pairFstD z).length)] at h1
    omega

/-- At round `rounds b z` the output is the concatenation of `g` over the full blocks. -/
theorem out_orbit (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) :
    out (pairEncode z (orbit start (step b g) z (rounds b z))) =
      (List.range (rounds b z)).flatMap fun i =>
        g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take
          (b.eval (pairFstD z).length)) := by
  rw [orbit_eq]
  simp [out]

end BlockLoop

end Complexity.StateLoop
