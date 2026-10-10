/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The aggregated block tests

The three customers of the bounded block-query loop
(`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): the one-bit OR,
strict-majority, and XOR-then-OR aggregations of a polynomial-time one-bit
indicator over polynomially many polynomial-length blocks are polynomial-time.
Each is an instance of `Complexity.polyTimeComputable_emitIter` with the
aggregation state (flag, vote counters, XOR mask) carried inside the loop's
tape-resident state word; the per-round work is assembled from the existing
`FP` combinators, and the orbit is computed in closed form by induction.

These are the `PolyTimeComputable` engines of the `P`-closure lemmas
`Complexity.mem_P_of_blockAny` / `_blockMajority` / `_blockXorAny` in
`TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.blockAt` — the `i`-th length-`a·(n+1)^k` block of the second
  component of a pair, where `n` is the first component's length.

## Main results

* `Complexity.polyTimeComputable_blockAnyTest` / `_blockXorAnyTest` — the
  aggregated one-bit OR and XOR-then-OR block tests of a polynomial-time
  one-bit indicator are polynomial-time.  The strict-majority test lives in
  `TCSlib.Complexity.ClassNP.PolyTimeBlockMajority`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3, Theorem 7.8; §7.4.1; Theorems
  7.17–7.18: the implicit "simulate the machine on each block" closures.)
-/

namespace Complexity

open Turing

/-- The `i`-th length-`a·(n+1)^k` block of the second component of a pair,
where `n` is the first component's length. -/
def blockAt (a k : ℕ) (z : List Bool) (i : ℕ) : List Bool :=
  ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
    (a * ((pairFstD z).length + 1) ^ k)

/-! #### The OR-aggregating loop -/

/-- One round of the OR-aggregating block loop on state
`pairEncode [flag] (pairEncode countdown (pairEncode x rem))`: OR the
indicator of the current block into the flag, drop the block, decrement the
unary countdown.  A done or malformed state is sent to the absorbing
`blockDone`; an exhausted countdown is sent to `blockDone` one step after the
chunk function has emitted the flag. -/
private noncomputable def anyStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode
      (if MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
        else pairFstD s)
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (sliceDropAt a k (pairSndD (pairSndD s))))

/-- The chunk function: emit the flag exactly at countdown exhaustion. -/
private def anyEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then []
  else if isNilB (pairFstD (pairSndD s)) then pairFstD s
  else []

/-- The initial state: clear flag, unary countdown `a'·(n+1)^k'`, and the
normalized input pair. -/
private def anyInit (a' k' : ℕ) (z : List Bool) : List Bool :=
  pairEncode [false]
    (pairEncode (List.replicate (a' * ((pairFstD z).length + 1) ^ k') true)
      (pairEncode (pairFstD z) (pairSndD z)))

/-- The OR round is polynomial-time.
**Proof sketch.** Assemble the two guards, the indicator of the sliced block,
the flag update, the countdown tail, and the dropped remainder from the `FP`
combinators (`polyTimeComputable_ite`/`pairEncode`/`comp` and the slice
primitives). -/
private theorem polyTimeComputable_anyStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (anyStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD s)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hind : PolyTimeComputable
      (fun s => [MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s)))]) :=
    hV.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have hflag : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
      else pairFstD s) :=
    polyTimeComputable_ite hind (polyTimeComputable_const [true]) polyTimeComputable_pairFstD
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (sliceDropAt a k (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      ((polyTimeComputable_sliceDropAt a k).comp hzz)
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    (hflag.pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

private theorem polyTimeComputable_anyEmit : PolyTimeComputable anyEmit := by
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const [])
    (polyTimeComputable_ite ht2 polyTimeComputable_pairFstD (polyTimeComputable_const []))

private theorem polyTimeComputable_anyInit (a' k' : ℕ) :
    PolyTimeComputable (anyInit a' k') := by
  have hcnt : PolyTimeComputable
      (fun z => List.replicate (a' * ((pairFstD z).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp polyTimeComputable_pairFstD
  exact (polyTimeComputable_const [false]).pairEncode
    (hcnt.pairEncode (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD))

/-- One loop round never grows the state beyond `max` with the done state's
length.
**Proof sketch.** The done branches have length two.  A live round keeps the
flag within the old flag's length, shortens the countdown, and replaces the
remainder by a dropped slice; summing the `Turing.length_pairEncode`
decompositions, the round shrinks the state by at least the two symbols the
countdown loses. -/
private theorem length_anyStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (anyStep V a k s).length ≤ max s.length 2 := by
  unfold anyStep
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [if_pos rfl]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [if_pos rfl]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hslice := length_sliceDropAt_le a k (pairSndD (pairSndD s))
      have hfl : (if MultiTapeTM.indicator V
          (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
          else pairFstD s).length ≤ (pairFstD s).length := by
        cases MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s)))
        · simp
        · simpa using Nat.one_le_iff_ne_zero.mpr
            (by simpa [List.length_eq_zero_iff] using hf)
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
      rw [length_pairEncode, length_pairEncode]
      simp only [List.length_drop]
      have hslice' : (sliceDropAt a k (pairSndD (pairSndD s))).length ≤
          (pairSndD (pairSndD s)).length + 2 :=
        le_trans hslice (by omega)
      omega

/-- Orbit envelope for the OR loop, in the shape
`Complexity.polyTimeComputable_emitIter` consumes. -/
private theorem length_anyStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((anyStep V a k)^[i] w).length ≤ 2 * (w.length + 1) ^ 1 := by
  have hmax : ((anyStep V a k)^[i] w).length ≤ max w.length 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_anyStep_le V a k _) (max_le ih (le_max_right _ _))
  refine le_trans hmax ?_
  rw [pow_one]
  exact max_le (by omega) (by omega)

/-- The done state is absorbing. -/
private theorem anyStep_done (V : Language Bool) (a k : ℕ) :
    anyStep V a k blockDone = blockDone := by
  unfold anyStep
  simp [blockDone, isNilB]

/-- Closed form of the OR loop's orbit up to countdown exhaustion.
**Proof sketch.** Induction on the round index: the guards see a one-bit flag
and a positive countdown, so the step fires; the slice primitives advance the
remainder by one block, `List.range_succ` extends the OR by the current
block's indicator, and the countdown loses one `true`. -/
private theorem anyStep_orbit (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD z).length + 1) ^ k') :
    (anyStep V a k)^[i] (anyInit a' k' z) =
      pairEncode
        [(List.range i).any (fun j => MultiTapeTM.indicator V
          (pairEncode (pairFstD z) (blockAt a k z j)))]
        (pairEncode
          (List.replicate (a' * ((pairFstD z).length + 1) ^ k' - i) true)
          (pairEncode (pairFstD z)
            ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))))) := by
  induction i with
  | zero => simp [anyInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD z).length + 1) ^ k' := Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD z).length + 1) ^ k' - i =
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold anyStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    rw [pairFstD_pairEncode, pairSndD_pairEncode]
    congr 1
    · rw [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode]
      rw [List.range_succ, List.any_append]
      cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD z)
          (((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
            (a * ((pairFstD z).length + 1) ^ k))) with
      | true =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = true := hb
        simp [hb']
      | false =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = false := hb
        simp [hb']
    · congr 1
      · rw [pairFstD_pairEncode]
        simp
      · rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
        congr 2
        ring

/-- Beyond exhaustion the orbit sits at the done state. -/
private theorem anyStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD z).length + 1) ^ k' < i) :
    (anyStep V a k)^[i] (anyInit a' k' z) = blockDone := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (anyStep V a k)^[K + 1] (anyInit a' k' z) = blockDone := by
    rw [Function.iterate_succ_apply', anyStep_orbit V a k a' k' z (le_refl K)]
    unfold anyStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, anyStep_done]

/-- The OR loop's machine-level output is the single aggregated bit.
**Proof sketch.** The countdown exhausts within the machine's larger round
budget (the input embeds its own first component, and the schedule is
monotone).  Rounds before exhaustion emit nothing, the exhaustion round emits
the flag, and the absorbing done state emits nothing after it, so the
single-live-chunk concatenation lemma applies. -/
private theorem anyLoop_output (V : Language Bool) (a k a' k' : ℕ) (z : List Bool) :
    (List.range (a' * ((anyInit a' k' z).length + 1) ^ k' + 1)).flatMap
      (fun i => anyEmit ((anyStep V a k)^[i] (anyInit a' k' z))) =
      [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
        (fun j => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))] := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  have hlen : (pairFstD z).length ≤ (anyInit a' k' z).length := by
    rw [anyInit, length_pairEncode, length_pairEncode, length_pairEncode]
    omega
  have hKN : K < a' * ((anyInit a' k' z).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), anyStep_orbit V a k a' k' z (le_of_lt hiK)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, anyStep_orbit V a k a' k' z (le_refl K)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega), pairFstD_pairEncode]
  · rw [if_neg (by omega), anyStep_orbit_done V a k a' k' z hiK]
    unfold anyEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The OR-aggregated block test of a polynomial-time one-bit indicator is
polynomial-time: one bit saying whether some of the `a'·(n+1)^k'` blocks of
length `a·(n+1)^k` passes the test on `Turing.pairEncode`d (first component,
block).

**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`.
The loop state is `pairEncode [flag] (pairEncode countdown (pairEncode x rem))`
with a unary countdown initialized at `a'·(|x|+1)^k'`
(`Complexity.polyTimeComputable_polyUnary`); each round ORs the indicator of
`sliceTakeAt a k` into the flag, drops the block (`sliceDropAt a k`), and
decrements; the chunk function emits `[flag]` exactly at countdown exhaustion
(the step then moves to an absorbing done state), so the concatenated output
is the single aggregated bit.  The orbit is computed in closed form by
induction on the round index. -/
theorem polyTimeComputable_blockAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_anyStep hV a k)
    polyTimeComputable_anyEmit a' k' 2 1 (length_anyStep_iterate V a k)
  have heq : (fun z => [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
      (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))]) =
      ((fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
        (fun i => anyEmit ((anyStep V a k)^[i] w))) ∘ anyInit a' k') := by
    funext z
    rw [Function.comp_apply, anyLoop_output V a k a' k' z]
  rw [heq]
  exact hloop.comp (polyTimeComputable_anyInit a' k')

/-! #### The XOR-shifted OR loop -/

/-- One round of the XOR-shifted OR loop on state
`pairEncode [flag] (pairEncode countdown (pairEncode v (pairEncode x u)))`:
XOR the mask `v` with the current block of `u`, test paired with `x`, OR
into the flag, drop the block, decrement. -/
private noncomputable def xorStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode
      (if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
        else pairFstD s)
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode (pairFstD (pairSndD (pairSndD s)))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s))))))

/-- The initial state of the XOR-shifted loop on the nested pair
`⟨⟨x, u⟩, v⟩`: clear flag, unary countdown `a'·(|x|+1)^k'`, the mask `v`, and
the normalized `⟨x, u⟩`. -/
private def xorInit (a' k' : ℕ) (w : List Bool) : List Bool :=
  pairEncode [false]
    (pairEncode
      (List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k') true)
      (pairEncode (pairSndD w)
        (pairEncode (pairFstD (pairFstD w)) (pairSndD (pairFstD w)))))

/-- The XOR-shifted round is polynomial-time.
**Proof sketch.** As the OR round, with the per-round test precomposed with
the truncating XOR of the carried mask and the sliced block
(`Complexity.polyTimeComputable_xorD`). -/
private theorem polyTimeComputable_xorStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (xorStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hmask : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hblk : PolyTimeComputable (fun s =>
      pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))) :=
    polyTimeComputable_pairSndD.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have htest : PolyTimeComputable (fun s =>
      [MultiTapeTM.indicator V
        (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
          (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
            (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))))))]) :=
    hV.comp ((polyTimeComputable_pairFstD.comp hzz).pairEncode
      (polyTimeComputable_xorD.comp (hmask.pairEncode hblk)))
  have hflag : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
        else pairFstD s) :=
    polyTimeComputable_ite htest (polyTimeComputable_const [true])
      polyTimeComputable_pairFstD
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode (pairFstD (pairSndD (pairSndD s)))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      (hmask.pairEncode ((polyTimeComputable_sliceDropAt a k).comp hzz))
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    (hflag.pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

private theorem polyTimeComputable_xorInit (a' k' : ℕ) :
    PolyTimeComputable (xorInit a' k') := by
  have hx : PolyTimeComputable (fun w => pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hu : PolyTimeComputable (fun w => pairSndD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hcnt : PolyTimeComputable (fun w =>
      List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp hx
  exact (polyTimeComputable_const [false]).pairEncode
    (hcnt.pairEncode (polyTimeComputable_pairSndD.pairEncode (hx.pairEncode hu)))

/-- One XOR-shifted round respects the slack measure `|s| + 16·|countdown s|`.
**Proof sketch.** As the majority round's bound; the mask is copied verbatim
and the joint-projection bound `length_pair_components_le` charges it against
the old state. -/
private theorem length_xorStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (xorStep V a k s).length +
      16 * (pairFstD (pairSndD (xorStep V a k s))).length ≤
      max (s.length + 16 * (pairFstD (pairSndD s)).length) 2 := by
  unfold xorStep
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
      have hfl : (if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
          else pairFstD s).length ≤ (pairFstD s).length := by
        cases MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))))))
        · simp
        · simpa using Nat.one_le_iff_ne_zero.mpr
            (by simpa [List.length_eq_zero_iff] using hf)
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
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, length_pairEncode,
        List.length_drop]
      omega

/-- Orbit envelope for the XOR-shifted loop. -/
private theorem length_xorStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((xorStep V a k)^[i] w).length ≤ 17 * (w.length + 1) ^ 1 := by
  have hmax : ((xorStep V a k)^[i] w).length +
      16 * (pairFstD (pairSndD ((xorStep V a k)^[i] w))).length ≤
      max (w.length + 16 * (pairFstD (pairSndD w)).length) 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_xorStep_le V a k _) (max_le ih (le_max_right _ _))
  have h1 : (pairFstD (pairSndD w)).length ≤ w.length :=
    le_trans (length_pairFstD_le _) (length_pairSndD_le w)
  rw [pow_one]
  omega

/-- The done state is absorbing for the XOR-shifted loop. -/
private theorem xorStep_done (V : Language Bool) (a k : ℕ) :
    xorStep V a k blockDone = blockDone := by
  unfold xorStep
  simp [blockDone, isNilB]

/-- Closed form of the XOR-shifted loop's orbit up to countdown exhaustion.
**Proof sketch.** As the OR orbit, with the carried mask constant and the
per-round indicator applied to the mask XORed with the current block
(`xorD_pairEncode`). -/
private theorem xorStep_orbit (V : Language Bool) (a k a' k' : ℕ) (w : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD (pairFstD w)).length + 1) ^ k') :
    (xorStep V a k)^[i] (xorInit a' k' w) =
      pairEncode
        [(List.range i).any (fun j => MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairFstD w))
            (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) j))))]
        (pairEncode
          (List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - i) true)
          (pairEncode (pairSndD w)
            (pairEncode (pairFstD (pairFstD w))
              ((pairSndD (pairFstD w)).drop
                (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))))) := by
  induction i with
  | zero => simp [xorInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD (pairFstD w)).length + 1) ^ k' :=
      Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - i =
        (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold xorStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    have hdrop1 : (true :: List.replicate
        (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) true).drop 1 =
        List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) true :=
      rfl
    have hslice2 : sliceDropAt a k (pairEncode (pairFstD (pairFstD w))
        ((pairSndD (pairFstD w)).drop
          (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))) =
        pairEncode (pairFstD (pairFstD w))
          ((pairSndD (pairFstD w)).drop
            ((i + 1) * (a * ((pairFstD (pairFstD w)).length + 1) ^ k))) := by
      rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
      congr 2
      ring
    rw [hdrop1, hslice2]
    congr 2
    simp only [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode, xorD_pairEncode]
    rw [List.range_succ, List.any_append]
    cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
        (List.zipWith xor (pairSndD w)
          (((pairSndD (pairFstD w)).drop
            (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k))).take
              (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))) with
    | true =>
      have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))) = true := hb
      simp [hb']
    | false =>
      have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))) = false := hb
      simp [hb']

/-- Beyond exhaustion the XOR-shifted orbit sits at the done state. -/
private theorem xorStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (w : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD (pairFstD w)).length + 1) ^ k' < i) :
    (xorStep V a k)^[i] (xorInit a' k' w) = blockDone := by
  set K := a' * ((pairFstD (pairFstD w)).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (xorStep V a k)^[K + 1] (xorInit a' k' w) = blockDone := by
    rw [Function.iterate_succ_apply', xorStep_orbit V a k a' k' w (le_refl K)]
    unfold xorStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, xorStep_done]

/-- The XOR-shifted loop's machine-level output is the single aggregated bit.
**Proof sketch.** As the OR output lemma, over the nested pairing: the
countdown is scheduled at the inner first component's length, which the
initial state's length dominates. -/
private theorem xorLoop_output (V : Language Bool) (a k a' k' : ℕ) (w : List Bool) :
    (List.range (a' * ((xorInit a' k' w).length + 1) ^ k' + 1)).flatMap
      (fun i => anyEmit ((xorStep V a k)^[i] (xorInit a' k' w))) =
      [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
        (fun j => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) j))))] := by
  set K := a' * ((pairFstD (pairFstD w)).length + 1) ^ k' with hK
  have hlen : (pairFstD (pairFstD w)).length ≤ (xorInit a' k' w).length := by
    have h1 : (pairFstD (pairFstD w)).length ≤ w.length :=
      le_trans (length_pairFstD_le _) (length_pairFstD_le w)
    simp only [xorInit, length_pairEncode, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hKN : K < a' * ((xorInit a' k' w).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), xorStep_orbit V a k a' k' w (le_of_lt hiK)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, xorStep_orbit V a k a' k' w (le_refl K)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega), pairFstD_pairEncode]
  · rw [if_neg (by omega), xorStep_orbit_done V a k a' k' w hiK]
    unfold anyEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The XOR-then-OR aggregated block test of a polynomial-time one-bit
indicator is polynomial-time: the input is a nested pair
`⟨⟨x, u⟩, v⟩`; block `i` is drawn from `u`, XORed bitwise with `v`
(truncating, `Complexity.xorD`), and tested paired with `x`.

**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
per-round test precomposed with the XOR mask: the loop state additionally
carries `v`, and the round's test input is
`pairEncode x (xorD (pairEncode v block))`
(`Complexity.polyTimeComputable_xorD`). -/
theorem polyTimeComputable_blockXorAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun w =>
      [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_xorStep hV a k)
    polyTimeComputable_anyEmit a' k' 17 1 (length_xorStep_iterate V a k)
  have heq : (fun w => [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
      (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
        (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))))]) =
      ((fun v => (List.range (a' * (v.length + 1) ^ k' + 1)).flatMap
        (fun i => anyEmit ((xorStep V a k)^[i] v))) ∘ xorInit a' k') := by
    funext w
    rw [Function.comp_apply, xorLoop_output V a k a' k' w]
  rw [heq]
  exact hloop.comp (polyTimeComputable_xorInit a' k')

end Complexity
