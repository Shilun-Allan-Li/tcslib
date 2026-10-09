/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The majority-aggregated block test

The strict-majority customer of the bounded block-query loop
(`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`), split from
`TCSlib.Complexity.ClassNP.PolyTimeBlockTests` for size: the loop state
carries two unary vote counters, and at countdown exhaustion the emitted bit
is their strict comparison.

## Main definitions

None — the loop state, step, and chunk functions are private to this file.

## Main results

* `Complexity.polyTimeComputable_blockMajorityTest` — the strict-majority
  aggregated one-bit block test of a polynomial-time one-bit indicator is
  polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.4.1, repeated trials with a majority
  vote; Theorem 7.17.)
-/

namespace Complexity

open Turing

/-! #### The majority-aggregating loop -/

/-- One round of the majority-aggregating block loop on state
`pairEncode [true] (pairEncode countdown (pairEncode (pairEncode uT uF)
(pairEncode x rem)))`: push one vote onto the passed (`uT`) or failed (`uF`)
unary counter according to the indicator of the current block, drop the
block, decrement the countdown. -/
private noncomputable def majStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode [true]
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode
          (if MultiTapeTM.indicator V
              (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
            pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
              (pairSndD (pairFstD (pairSndD (pairSndD s))))
          else
            pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
              (true :: pairSndD (pairFstD (pairSndD (pairSndD s)))))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s))))))

/-- The chunk function: at countdown exhaustion, emit one bit comparing the
two unary vote counters strictly (`uF < uT`). -/
private def majEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then []
  else if isNilB (pairFstD (pairSndD s)) then
    [!decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
      (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]
  else []

/-- The initial state: live marker, unary countdown `a'·(n+1)^k'`, empty vote
counters, and the normalized input pair. -/
private def majInit (a' k' : ℕ) (z : List Bool) : List Bool :=
  pairEncode [true]
    (pairEncode (List.replicate (a' * ((pairFstD z).length + 1) ^ k') true)
      (pairEncode (pairEncode [] [])
        (pairEncode (pairFstD z) (pairSndD z))))

/-- The majority round is polynomial-time.
**Proof sketch.** As the OR round, with the flag update replaced by the
two-counter vote push, assembled from the same `FP` combinators. -/
private theorem polyTimeComputable_majStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (majStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hacc : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hind : PolyTimeComputable (fun s =>
      [MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))]) :=
    hV.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have huT : PolyTimeComputable (fun s =>
      pairFstD (pairFstD (pairSndD (pairSndD s)))) :=
    polyTimeComputable_pairFstD.comp hacc
  have huF : PolyTimeComputable (fun s =>
      pairSndD (pairFstD (pairSndD (pairSndD s)))) :=
    polyTimeComputable_pairSndD.comp hacc
  have hconsT : PolyTimeComputable (fun s =>
      true :: pairFstD (pairFstD (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_prepend [true]).comp huT
  have hconsF : PolyTimeComputable (fun s =>
      true :: pairSndD (pairFstD (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_prepend [true]).comp huF
  have hvote : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V
          (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
        pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
          (pairSndD (pairFstD (pairSndD (pairSndD s))))
      else
        pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
          (true :: pairSndD (pairFstD (pairSndD (pairSndD s))))) :=
    polyTimeComputable_ite hind (hconsT.pairEncode huF) (huT.pairEncode hconsF)
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode
          (if MultiTapeTM.indicator V
              (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
            pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
              (pairSndD (pairFstD (pairSndD (pairSndD s))))
          else
            pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
              (true :: pairSndD (pairFstD (pairSndD (pairSndD s)))))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      (hvote.pairEncode ((polyTimeComputable_sliceDropAt a k).comp hzz))
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    ((polyTimeComputable_const [true]).pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

/-- The majority chunk function is polynomial-time.
**Proof sketch.** The emitted bit is the negated pair length test
`Complexity.polyTimeComputable_lenLe` on the swapped vote counters, guarded
by the two emptiness tests. -/
private theorem polyTimeComputable_majEmit : PolyTimeComputable majEmit := by
  have hacc : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have hswap : PolyTimeComputable (fun s =>
      pairEncode (pairSndD (pairFstD (pairSndD (pairSndD s))))
        (pairFstD (pairFstD (pairSndD (pairSndD s))))) :=
    (polyTimeComputable_pairSndD.comp hacc).pairEncode
      (polyTimeComputable_pairFstD.comp hacc)
  have hle : PolyTimeComputable (fun s =>
      [decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
        (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]) := by
    have h := polyTimeComputable_lenLe.comp hswap
    have heq : (fun s =>
        [decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
          (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]) =
        ((fun z => [decide ((pairSndD z).length ≤ (pairFstD z).length)]) ∘
          (fun s => pairEncode (pairSndD (pairFstD (pairSndD (pairSndD s))))
            (pairFstD (pairFstD (pairSndD (pairSndD s)))))) := by
      funext s
      simp [Function.comp]
    rw [heq]
    exact h
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const [])
    (polyTimeComputable_ite ht2 (polyTimeComputable_not hle)
      (polyTimeComputable_const []))

private theorem polyTimeComputable_majInit (a' k' : ℕ) :
    PolyTimeComputable (majInit a' k') := by
  have hcnt : PolyTimeComputable
      (fun z => List.replicate (a' * ((pairFstD z).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp polyTimeComputable_pairFstD
  exact (polyTimeComputable_const [true]).pairEncode
    (hcnt.pairEncode ((polyTimeComputable_const (pairEncode [] [])).pairEncode
      (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD)))

/-- The vote push grows the accumulator by at most four symbols. -/
private theorem length_majVote_le (b : Bool) (acc : List Bool) :
    (if b then pairEncode (true :: pairFstD acc) (pairSndD acc)
      else pairEncode (pairFstD acc) (true :: pairSndD acc)).length ≤ acc.length + 4 := by
  have hb := length_pair_components_le acc
  cases b with
  | true =>
    rw [if_pos rfl, length_pairEncode, List.length_cons]
    omega
  | false =>
    rw [if_neg (by simp), length_pairEncode, List.length_cons]
    omega

/-- One majority round respects the slack measure `|s| + 16·|countdown s|`.
**Proof sketch.** As the OR round's length bound, except that the vote push
can grow the state by a bounded constant (`length_majVote_le`); the countdown
loses one symbol per round, so sixteen units of slack per remaining round
absorb the growth. -/
private theorem length_majStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (majStep V a k s).length +
      16 * (pairFstD (pairSndD (majStep V a k s))).length ≤
      max (s.length + 16 * (pairFstD (pairSndD s)).length) 2 := by
  unfold majStep
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [if_pos rfl]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode, pairFstD_nil]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [if_pos rfl]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode, pairFstD_nil]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hvote := length_majVote_le
        (MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))
        (pairFstD (pairSndD (pairSndD s)))
      have hslice := length_sliceDropAt_le a k (pairSndD (pairSndD (pairSndD s)))
      have hslice' : (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))).length ≤
          (pairSndD (pairSndD (pairSndD s))).length + 2 := le_trans hslice (by omega)
      have hY := length_pair_components_le (pairSndD (pairSndD s))
      have hlens : s.length =
          2 * (pairFstD s).length + 2 +
            (2 * (pairFstD (pairSndD s)).length + 2 + (pairSndD (pairSndD s)).length) := by
        conv_lhs => rw [hs]
        rw [length_pairEncode]
        congr 2
        conv_lhs => rw [ht]
        rw [length_pairEncode]
      have hcd1 : 1 ≤ (pairFstD (pairSndD s)).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hcd)
      have hf1 : 1 ≤ (pairFstD s).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hf)
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, length_pairEncode,
        List.length_drop, List.length_cons, List.length_nil]
      omega

/-- Orbit envelope for the majority loop. -/
private theorem length_majStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((majStep V a k)^[i] w).length ≤ 17 * (w.length + 1) ^ 1 := by
  have hmax : ((majStep V a k)^[i] w).length +
      16 * (pairFstD (pairSndD ((majStep V a k)^[i] w))).length ≤
      max (w.length + 16 * (pairFstD (pairSndD w)).length) 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_majStep_le V a k _) (max_le ih (le_max_right _ _))
  have h1 : (pairFstD (pairSndD w)).length ≤ w.length :=
    le_trans (length_pairFstD_le _) (length_pairSndD_le w)
  rw [pow_one]
  omega

/-- The done state is absorbing for the majority loop. -/
private theorem majStep_done (V : Language Bool) (a k : ℕ) :
    majStep V a k blockDone = blockDone := by
  unfold majStep
  simp [blockDone, isNilB]

/-- Closed form of the majority loop's orbit up to countdown exhaustion.
**Proof sketch.** As the OR orbit, with `List.countP` over `List.range`
replacing the OR: the vote push turns the passed counter `cT i` into
`cT i + 1` exactly when the current block's indicator holds
(`List.countP_append` at `List.range_succ`), and the failed counter is
`i - cT i` throughout. -/
private theorem majStep_orbit (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD z).length + 1) ^ k') :
    (majStep V a k)^[i] (majInit a' k' z) =
      pairEncode [true]
        (pairEncode
          (List.replicate (a' * ((pairFstD z).length + 1) ^ k' - i) true)
          (pairEncode
            (pairEncode
              (List.replicate ((List.range i).countP (fun j =>
                MultiTapeTM.indicator V
                  (pairEncode (pairFstD z) (blockAt a k z j)))) true)
              (List.replicate (i - (List.range i).countP (fun j =>
                MultiTapeTM.indicator V
                  (pairEncode (pairFstD z) (blockAt a k z j)))) true))
            (pairEncode (pairFstD z)
              ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k)))))) := by
  induction i with
  | zero => simp [majInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD z).length + 1) ^ k' := Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD z).length + 1) ^ k' - i =
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold majStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    have hle : (List.range i).countP (fun j =>
        MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) ≤ i :=
      le_trans List.countP_le_length (by simp)
    have hcnt : (List.range (i + 1)).countP (fun j =>
        MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
        (List.range i).countP (fun j =>
          MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) +
        (if MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
          then 1 else 0) := by
      rw [List.range_succ, List.countP_append]
      simp [List.countP_cons]
    have hdrop1 : (true :: List.replicate
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) true).drop 1 =
        List.replicate (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) true := rfl
    have hslice2 : sliceDropAt a k (pairEncode (pairFstD z)
        ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k)))) =
        pairEncode (pairFstD z)
          ((pairSndD z).drop ((i + 1) * (a * ((pairFstD z).length + 1) ^ k))) := by
      rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
      congr 2
      ring
    have hvoteq : (if MultiTapeTM.indicator V (sliceTakeAt a k (pairEncode (pairFstD z)
        ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))))) then
          pairEncode (true :: List.replicate ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
            (List.replicate (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
        else
          pairEncode (List.replicate ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
            (true :: List.replicate (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)) =
        pairEncode
          (List.replicate ((List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
          (List.replicate (i + 1 - (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true) := by
      rw [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode]
      cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD z)
          (((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
            (a * ((pairFstD z).length + 1) ^ k))) with
      | true =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = true := hb
        have hcT1 : (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) + 1 := by
          rw [hcnt, hb']
          simp
        rw [if_pos rfl, hcT1, List.replicate_succ,
          show i + 1 - ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) + 1) =
            i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))
          from by omega]
      | false =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = false := hb
        have hcT0 : (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) := by
          rw [hcnt, hb']
          simp
        rw [if_neg (by simp), hcT0,
          show i + 1 - (List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) + 1
          from by omega, List.replicate_succ]
    rw [hdrop1, hslice2, hvoteq]

/-- Beyond exhaustion the majority orbit sits at the done state. -/
private theorem majStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD z).length + 1) ^ k' < i) :
    (majStep V a k)^[i] (majInit a' k' z) = blockDone := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (majStep V a k)^[K + 1] (majInit a' k' z) = blockDone := by
    rw [Function.iterate_succ_apply', majStep_orbit V a k a' k' z (le_refl K)]
    unfold majStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, majStep_done]

/-- The majority loop's machine-level output is the single aggregated bit.
**Proof sketch.** As the OR output lemma; at exhaustion the emitted
comparison of the unary counters `¬(cT ≤ K - cT)` is the strict majority
`K < 2·cT`, by `decide_not` and arithmetic. -/
private theorem majLoop_output (V : Language Bool) (a k a' k' : ℕ) (z : List Bool) :
    (List.range (a' * ((majInit a' k' z).length + 1) ^ k' + 1)).flatMap
      (fun i => majEmit ((majStep V a k)^[i] (majInit a' k' z))) =
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun j => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z j))))] := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  have hlen : (pairFstD z).length ≤ (majInit a' k' z).length := by
    simp only [majInit, length_pairEncode, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hKN : K < a' * ((majInit a' k' z).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  have hcT : (List.range K).countP (fun j =>
      MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) ≤ K :=
    le_trans List.countP_le_length (by simp)
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), majStep_orbit V a k a' k' z (le_of_lt hiK)]
    unfold majEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, majStep_orbit V a k a' k' z (le_refl K)]
    unfold majEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega)]
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
    congr 1
    rw [← decide_not]
    exact decide_eq_decide.mpr (by omega)
  · rw [if_neg (by omega), majStep_orbit_done V a k a' k' z hiK]
    unfold majEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The strict-majority-aggregated block test of a polynomial-time one-bit
indicator is polynomial-time.

**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
flag replaced by two unary vote counters (passed and failed blocks); at
countdown exhaustion the emitted bit is the strict comparison of their
lengths (`Complexity.polyTimeComputable_lenLe` after a `pairSwap`), which
equals `a'·(n+1)^k' < 2·(passed votes)` since the counts sum to the round
total. -/
theorem polyTimeComputable_blockMajorityTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun i => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z i))))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_majStep hV a k)
    polyTimeComputable_majEmit a' k' 17 1 (length_majStep_iterate V a k)
  have heq : (fun z => [decide (a' * ((pairFstD z).length + 1) ^ k' <
      2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
        (fun i => MultiTapeTM.indicator V
          (pairEncode (pairFstD z) (blockAt a k z i))))]) =
      ((fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
        (fun i => majEmit ((majStep V a k)^[i] w))) ∘ majInit a' k') := by
    funext z
    rw [Function.comp_apply, majLoop_output V a k a' k' z]
  rw [heq]
  exact hloop.comp (polyTimeComputable_majInit a' k')

end Complexity
