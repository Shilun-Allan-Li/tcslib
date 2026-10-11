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
`TCSlib.Complexity.ClassNP.PolyTimeBlockTests` for size: an instance of the countdown
block loop `Complexity.BlockLoop` whose remainder carries two unary vote counters, and
whose chunk at countdown exhaustion is their strict comparison.

## Main definitions

None — the loop's round, chunk and initial state are private to this file.

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
block, decrement the countdown.  An instance of `Complexity.BlockLoop.step` with the
live marker `[true]` as head. -/
private noncomputable def majStep (V : Language Bool) (a k : ℕ) : List Bool → List Bool :=
  BlockLoop.step (fun _ _ => [true])
    (fun _ r => pairEncode
      (if MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD r)) then
        pairEncode (true :: pairFstD (pairFstD r)) (pairSndD (pairFstD r))
      else
        pairEncode (pairFstD (pairFstD r)) (true :: pairSndD (pairFstD r)))
      (sliceDropAt a k (pairSndD r)))

/-- The chunk function: at countdown exhaustion, emit one bit comparing the
two unary vote counters strictly (`uF < uT`). -/
private def majEmit : List Bool → List Bool :=
  BlockLoop.emit (fun s => [!decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
    (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)])

/-- The initial state: live marker, unary countdown `a'·(n+1)^k'`, empty vote
counters, and the normalized input pair. -/
private def majInit (a' k' : ℕ) (z : List Bool) : List Bool :=
  pairEncode [true]
    (pairEncode (List.replicate (a' * ((pairFstD z).length + 1) ^ k') true)
      (pairEncode (pairEncode [] [])
        (pairEncode (pairFstD z) (pairSndD z))))

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

/-- The majority loop's machine-level output is the single aggregated bit.
**Proof sketch.** `Complexity.BlockLoop.loop_output` with the live marker as every head
and remainders `⟨⟨1^cT i, 1^(i - cT i)⟩, ⟨x, rem.drop (i·B)⟩⟩`, where `cT i` counts the
passing blocks among the first `i` (`List.countP_append` at `List.range_succ`): the vote
push adds the `i`-th block's vote and the block is dropped.  At exhaustion the emitted
comparison of the unary counters `¬(cT ≤ K - cT)` is the strict majority `K < 2·cT`, by
`decide_not` and arithmetic. -/
private theorem majLoop_output (V : Language Bool) (a k a' k' : ℕ) (z : List Bool) :
    (List.range (a' * ((majInit a' k' z).length + 1) ^ k' + 1)).flatMap
      (fun i => majEmit ((majStep V a k)^[i] (majInit a' k' z))) =
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun j => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z j))))] := by
  have hlen : (pairFstD z).length ≤ (majInit a' k' z).length := by
    simp only [majInit, length_pairEncode, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hcT : ∀ i, (List.range i).countP (fun j =>
      MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) ≤ i :=
    fun i => le_trans List.countP_le_length (by simp)
  refine (BlockLoop.loop_output (g := majStep V a k) rfl (fun _ => [true])
    (fun i => pairEncode
      (pairEncode
        (List.replicate ((List.range i).countP (fun j =>
          MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
        (List.replicate (i - (List.range i).countP (fun j =>
          MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true))
      (pairEncode (pairFstD z)
        ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k)))))
    (by simp [majInit]) (fun _ _ => by simp) (fun _ _ => rfl) (fun i _ => ?_)
    (BlockLoop.lt_polyBudget_of_le a' k' hlen)).trans ?_
  · simp only [pairFstD_pairEncode, pairSndD_pairEncode, BlockLoop.sliceDropAt_pairEncode_drop,
      BlockLoop.sliceTakeAt_pairEncode_drop]
    have hcnt : (List.range (i + 1)).countP (fun j =>
        MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
        (List.range i).countP (fun j =>
          MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) +
        (if MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
          then 1 else 0) := by
      rw [List.range_succ, List.countP_append]
      simp [List.countP_cons]
    have hle := hcT i
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
  · have hK := hcT (a' * ((pairFstD z).length + 1) ^ k')
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
    congr 1
    rw [← decide_not]
    exact decide_eq_decide.mpr (by omega)

/-- The strict-majority-aggregated block test of a polynomial-time one-bit
indicator is polynomial-time.

**Proof sketch.** `Complexity.BlockLoop.polyTimeComputable_countdown` for the countdown
block loop whose head is the live marker and whose remainder carries two unary vote
counters (passed and failed blocks); the vote push is an `ite` on the block's indicator;
at countdown exhaustion the emitted bit is the strict comparison of their lengths
(`Complexity.polyTimeComputable_lenLe` after a `pairSwap`), which equals
`a'·(n+1)^k' < 2·(passed votes)` since the counts sum to the round total.  The vote push
grows the counters by at most four symbols (`length_majVote_le`), well within the
slack `16`. -/
theorem polyTimeComputable_blockMajorityTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun i => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z i))))]) := by
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hacc : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  -- the vote push: an `ite` on the block's indicator over the two `true ::` prepends
  have hind : PolyTimeComputable (fun s =>
      [MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))]) :=
    hV.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have huT : PolyTimeComputable (fun s =>
      pairFstD (pairFstD (pairSndD (pairSndD s)))) :=
    polyTimeComputable_pairFstD.comp hacc
  have huF : PolyTimeComputable (fun s =>
      pairSndD (pairFstD (pairSndD (pairSndD s)))) :=
    polyTimeComputable_pairSndD.comp hacc
  have hvote : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V
          (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
        pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
          (pairSndD (pairFstD (pairSndD (pairSndD s))))
      else
        pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
          (true :: pairSndD (pairFstD (pairSndD (pairSndD s))))) :=
    polyTimeComputable_ite hind (((polyTimeComputable_prepend [true]).comp huT).pairEncode huF)
      (huT.pairEncode ((polyTimeComputable_prepend [true]).comp huF))
  -- the emitted bit: the negated length test on the swapped counters
  have hle : PolyTimeComputable (fun s =>
      [decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
        (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]) := by
    have h := polyTimeComputable_lenLe.comp (huF.pairEncode huT)
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
  exact BlockLoop.polyTimeComputable_countdown (g := majStep V a k) (e := majEmit) rfl rfl
    [true] a' k' 16 (polyTimeComputable_const [true])
    (hvote.pairEncode ((polyTimeComputable_sliceDropAt a k).comp hzz))
    (polyTimeComputable_not hle) polyTimeComputable_pairFstD
    ((polyTimeComputable_const (pairEncode [] [])).pairEncode
      (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD))
    (fun f r _ => by
      have hpush := length_majVote_le
        (MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD r))) (pairFstD r)
      have hslice := length_sliceDropAt_le a k (pairSndD r)
      have hY := length_pair_components_le r
      simp only [length_pairEncode, List.length_cons, List.length_nil]
      omega)
    (majLoop_output V a k a' k')

end Complexity
