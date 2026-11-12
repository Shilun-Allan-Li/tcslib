/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyConfig

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The configuration-tableau circuit

Correctness of the configuration-tableau program of `CircuitComplexity/PSubsetPPolyConfig`
and the resulting circuit: for an arbitrary machine `M`, a virtual-input layout `ℓ`
(input bits and constants) of length `N` and a budget `T`, a fan-in-two circuit of size
`n + 2 + (T + 1)(k (2T + 1) + N + 3) · K_M` that outputs `1` on `x` iff some step `s < T`
of `M` on the virtual input `ℓ(x)` emits `1`.  This standard configuration tableau is
not in [AB09] (which proves Thm 6.6 only via oblivious machines); it adapts the 6.6
construction to arbitrary machines.

## Main definitions

* `Complexity.cfgCircuit M n ℓ T` — the circuit.

## Main results

* `Complexity.cfgProg_blocks` — every block of the program is the true block.
* `Complexity.cfgCircuit_eval`, `Complexity.cfgCircuit_isFaninTwo`,
  `Complexity.cfgCircuit_size_le`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6.)
-/

namespace Complexity

open Turing BoolCircuit CfgTableau

variable {M : FinTM Bool} {ℓ : List BitSrc} {T : ℕ}

/-- Reading bit `c · i + j` of a concatenation of chunks of length `c`. -/
private theorem getD_flatMap_chunk {α β : Type} (l : List α) (g : α → List β) {c : ℕ}
    (hg : ∀ a, (g a).length = c) (rest : List β) {i j : ℕ} (hi : i < l.length) (hj : j < c)
    (d : β) : ((l.flatMap g) ++ rest).getD (c * i + j) d = (g l[i]).getD j d := by
  have h := take_drop_flatMap_append l g hg rest hi
  have h2 := congrArg (fun l' => l'.getD j d) h
  simp only at h2
  rw [← h2, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj,
    List.getElem?_drop, Nat.mul_comm]

/-- **An input block is correct** when all earlier blocks are.

**Proof sketch.** Read the source bits off the padded source list: the flags are
constants, the input symbol at `p` comes from the layout (`1 ≤ p ≤ N` gives `ℓ[p − 1]`, a
bit of the virtual input; otherwise blank), and the remaining bits come from earlier
blocks, which are correct by hypothesis.  These are the previous-step head bits of
positions `p − 1, p, p + 1` and the same-step running symbol at `p − 1` (constants at the
boundaries, where the true values vanish).  At step `0` conclude with
`Complexity.cfgF_inp_zero`, otherwise decode the previous snapshot and conclude with
`Complexity.cfgF_inp_succ`. -/
private theorem inp_block {x : List Bool} {blocks : List (List Bool)} {t p : ℕ}
    (hℓ : ∀ s ∈ ℓ, ∀ bs, BitSrc.eval x bs s = BitSrc.eval x [] s)
    (hB : ∀ i' < inpIdx M ℓ.length T t p,
      blocks.getD i' [] = cfgExp M ℓ T (ℓ.map (BitSrc.eval x [])) i')
    (hp : p < ℓ.length + 2) :
    cfgF M (some none) ((padSrcs M (inpSrcs M ℓ T t p)).map (BitSrc.eval x blocks)) =
      inpExp M (ℓ.map (BitSrc.eval x [])) t p := by
  set w := ℓ.map (BitSrc.eval x []) with hw
  have hwl : w.length = ℓ.length := by simp [hw]
  set l := (padSrcs M (inpSrcs M ℓ T t p)).map (BitSrc.eval x blocks) with hl
  -- the eleven leading source bits, read off the padded source list
  have g : ∀ j (hj : j < 11), l.getD j false =
      (([.const (decide (t = 0)), .const (decide (p = 1)), .const (decide (p = 0)),
        .const (decide (p = ℓ.length + 1)),
        .const (decide (1 ≤ p ∧ p ≤ ℓ.length)),
        if 1 ≤ p ∧ p ≤ ℓ.length then ℓ.getD (p - 1) (.const false) else .const false,
        ihSrc M ℓ T t (p - 1) (decide (t ≠ 0 ∧ 1 ≤ p)), ihSrc M ℓ T t p (decide (t ≠ 0)),
        ihSrc M ℓ T t (p + 1) (decide (t ≠ 0 ∧ p ≤ ℓ.length)),
        ichSrc M ℓ T t p 1, ichSrc M ℓ T t p 2] : List BitSrc).map
          (BitSrc.eval x blocks)).getD j false := by
    intro j hj
    rw [hl, padSrcs, inpSrcs, List.append_assoc, List.map_append,
      List.getD_append _ _ _ _ (by simpa using hj)]
  -- the input symbol of this position, read through the layout
  have hsym : (inputBitAt w p).isSome = decide (1 ≤ p ∧ p ≤ ℓ.length) ∧
      (inputBitAt w p).getD false = BitSrc.eval x blocks
        (if 1 ≤ p ∧ p ≤ ℓ.length then ℓ.getD (p - 1) (.const false) else .const false) := by
    by_cases h : 1 ≤ p ∧ p ≤ ℓ.length
    · have hlt : p - 1 < ℓ.length := by omega
      have hx : inputBitAt w p = some (BitSrc.eval x [] ℓ[p - 1]) := by
        simp [inputBitAt, show p ≠ 0 by omega, hw, List.getElem?_map,
          List.getElem?_eq_getElem hlt]
      rw [hx, if_pos h, List.getD_eq_getElem _ _ hlt]
      simp [h, hℓ _ (List.getElem_mem hlt) blocks]
    · have hx : inputBitAt w p = none := by
        unfold inputBitAt
        split_ifs with h0
        · rfl
        · exact List.getElem?_eq_none (by rw [hwl]; omega)
      rw [hx, if_neg h]
      simp [h, BitSrc.eval]
  -- the running symbol of position `p - 1`, at the same step
  have hch : ∀ j, j = 1 ∨ j = 2 → BitSrc.eval x blocks (ichSrc M ℓ T t p j) =
      (optBits (if p = 0 then none else inpChain M w t (p - 1))).getD (j - 1) false := by
    intro j hj
    by_cases h0 : p = 0
    · subst h0
      rcases hj with rfl | rfl <;> simp [ichSrc, BitSrc.eval, optBits]
    · simp only [ichSrc, ne_eq, h0, not_false_eq_true, if_true, if_false]
      rw [eval_block hB (by simp only [inpIdx]; omega), cfgExp_inpIdx M ℓ T w t (by omega)]
      rcases hj with rfl | rfl <;> simp [inpExp, optBits]
  cases t with
  | zero =>
    -- step `0`: the head starts at position `1`
    apply cfgF_inp_zero M w p l
    · rw [g 0 (by omega)]; simp [BitSrc.eval]
    · rw [g 1 (by omega)]; simp [BitSrc.eval]
    · rw [g 4 (by omega)]; simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, BitSrc.eval]
      exact hsym.1.symm
    · rw [g 5 (by omega)]; simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
      exact hsym.2.symm
    · rw [g 9 (by omega)]
      have := hch 1 (Or.inl rfl)
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [optBits]
    · rw [g 10 (by omega)]
      have := hch 2 (Or.inr rfl)
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [optBits]
  | succ t =>
    -- step `t + 1`: previous-step head bits, then the local rule
    have hprev_lt : ∀ p', p' < ℓ.length + 2 →
        inpIdx M ℓ.length T t p' < inpIdx M ℓ.length T (t + 1) p := fun p' hp' => by
      have := inpIdx_lt_succ M ℓ.length T t hp'
      simp only [inpIdx] at this ⊢; omega
    have hih : ∀ p' (ok : Bool), (ok = true → p' < ℓ.length + 2) →
        BitSrc.eval x blocks (ihSrc M ℓ T (t + 1) p' ok) =
          if ok then decide (((cfgAt M w t).inputPos : ℕ) = p') else false := by
      intro p' ok hok
      unfold ihSrc
      cases ok with
      | false => simp [BitSrc.eval]
      | true =>
        simp only [if_true, Nat.add_sub_cancel]
        rw [eval_block hB (hprev_lt p' (hok rfl)), cfgExp_inpIdx M ℓ T w t (hok rfl)]
        simp [inpExp]
    have hip : ((cfgAt M w t).inputPos : ℕ) < ℓ.length + 2 := by
      have := (cfgAt M w t).inputPos.isLt; omega
    apply cfgF_inp_succ M w t p (by omega) l
    · rw [g 0 (by omega)]; simp [BitSrc.eval]
    · have key := drop_take_padSrcs (M := M) (f := BitSrc.eval x blocks)
        [.const (decide (t + 1 = 0)), .const (decide (p = 1)), .const (decide (p = 0)),
          .const (decide (p = ℓ.length + 1)),
          .const (decide (1 ≤ p ∧ p ≤ ℓ.length)),
          if 1 ≤ p ∧ p ≤ ℓ.length then ℓ.getD (p - 1) (.const false) else .const false,
          ihSrc M ℓ T (t + 1) (p - 1) (decide (t + 1 ≠ 0 ∧ 1 ≤ p)),
          ihSrc M ℓ T (t + 1) p (decide (t + 1 ≠ 0)),
          ihSrc M ℓ T (t + 1) (p + 1) (decide (t + 1 ≠ 0 ∧ p ≤ ℓ.length)),
          ichSrc M ℓ T (t + 1) p 1, ichSrc M ℓ T (t + 1) p 2] (prevSnapSrcs M ℓ T (t + 1))
      simp only [List.length_cons, List.length_nil, length_prevSnapSrcs] at key
      rw [hl, inpSrcs, key, prevSnapSrcs_eval hB
        ((snapIdx_lt_succ M ℓ.length T t).trans_le (by simp only [inpIdx]; omega)),
        snapDecode_snapEncode]
    · rw [g 2 (by omega)]; simp [BitSrc.eval]
    · rw [g 3 (by omega)]; simp [BitSrc.eval, hwl]
    · rw [g 4 (by omega)]; simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, BitSrc.eval]
      exact hsym.1.symm
    · rw [g 5 (by omega)]; simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
      exact hsym.2.symm
    · rw [g 6 (by omega)]
      have := hih (p - 1) (decide (t + 1 ≠ 0 ∧ 1 ≤ p)) (fun _ => by omega)
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]
      by_cases h1 : 1 ≤ p <;> simp [h1]
    · rw [g 7 (by omega)]
      have := hih p (decide (t + 1 ≠ 0)) (fun _ => hp)
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp
    · rw [g 8 (by omega)]
      have := hih (p + 1) (decide (t + 1 ≠ 0 ∧ p ≤ ℓ.length)) (fun h => by simp at h; omega)
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]
      by_cases h1 : p ≤ ℓ.length
      · simp [h1]
      · simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, h1, and_false, decide_false,
          Bool.false_eq_true, if_false]
        symm; rw [decide_eq_false_iff_not]; omega
    · rw [g 9 (by omega)]
      have := hch 1 (Or.inl rfl)
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [optBits]
    · rw [g 10 (by omega)]
      have := hch 2 (Or.inr rfl)
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [optBits]

/-- The work-tape sources of the snapshot: the running symbols at the right end of each
window. -/
def snapWorkSrcs (t : ℕ) : List BitSrc :=
  (List.finRange M.k).flatMap (fun τ =>
    [.block (cellIdx M ℓ.length T t τ (2 * T)) 3, .block (cellIdx M ℓ.length T t τ (2 * T)) 4])

/-- The snapshot reads two bits per work tape. -/
@[simp] theorem length_snapWorkSrcs (t : ℕ) : (snapWorkSrcs (M := M) (ℓ := ℓ) (T := T) t).length = 2 * M.k := by
  rw [snapWorkSrcs, length_flatMap_const _ _ (c := 2) (fun _ => rfl), List.length_finRange,
    Nat.mul_comm]

/-- **The snapshot block is correct** when all earlier blocks are.

**Proof sketch.** The first four source bits are the time-`0` flag, the previous
accumulator (a bit of the previous snapshot block), and the running input symbol at
position `N + 1`, which is the input symbol (`Complexity.inpChain_right`).  Bits
`4 + 2τ` and `5 + 2τ` are the running symbol of work tape `τ` at the right end `T` of its
window, which is the symbol under its head (`Complexity.workChain_right`, the head being
within distance `t ≤ T` of the origin).  Then come the bits of the previous snapshot,
which decode to it.  `Complexity.cfgF_snap` concludes. -/
private theorem snap_block {x : List Bool} {blocks : List (List Bool)} {t : ℕ}
    (hB : ∀ i' < snapIdx M ℓ.length T t,
      blocks.getD i' [] = cfgExp M ℓ T (ℓ.map (BitSrc.eval x [])) i')
    (ht : t ≤ T) :
    cfgF M none ((padSrcs M (snapSrcs M ℓ T t)).map (BitSrc.eval x blocks)) =
      snapExp M (ℓ.map (BitSrc.eval x [])) t := by
  set w := ℓ.map (BitSrc.eval x []) with hw
  have hwl : w.length = ℓ.length := by simp [hw]
  set lit : List BitSrc := [.const (decide (t = 0)),
    if t = 0 then .const false else .block (snapIdx M ℓ.length T (t - 1)) (snapWidth M),
    .block (inpIdx M ℓ.length T t (ℓ.length + 1)) 1,
    .block (inpIdx M ℓ.length T t (ℓ.length + 1)) 2] with hlit
  have hsplit : snapSrcs M ℓ T t = lit ++ snapWorkSrcs (M := M) (ℓ := ℓ) (T := T) t ++
      prevSnapSrcs M ℓ T t := rfl
  set l := (padSrcs M (snapSrcs M ℓ T t)).map (BitSrc.eval x blocks) with hl
  have g : ∀ j (hj : j < 4), l.getD j false = (lit.map (BitSrc.eval x blocks)).getD j false := by
    intro j hj
    rw [hl, hsplit, padSrcs, List.append_assoc, List.append_assoc, List.map_append,
      List.getD_append _ _ _ _ (by simpa [hlit] using hj)]
  -- the running input symbol at the right end is the input symbol
  have hinp : inpIdx M ℓ.length T t (ℓ.length + 1) < snapIdx M ℓ.length T t :=
    inpIdx_lt_snapIdx M ℓ.length T t (by omega)
  have hinpc : (inpExp M w t (ℓ.length + 1)) =
      decide (((cfgAt M w t).inputPos : ℕ) = ℓ.length + 1) ::
        optBits (cfgAt M w t).inputSymbol := by
    rw [inpExp, ← hwl, inpChain_right]
  -- the work running symbols, read from the right end of each window
  have hwork : ∀ (τ : Fin M.k) (j : ℕ), j < 2 → l.getD (4 + 2 * τ + j) false =
      (optBits ((cfgAt M w t).workTapeSymbols τ)).getD j false := by
    intro τ j hj
    have hlitlen : (lit.map (BitSrc.eval x blocks)).length = 4 := by simp [hlit]
    rw [hl, hsplit, padSrcs, List.append_assoc, List.append_assoc, List.map_append,
      List.getD_append_right _ _ _ _ (by omega), hlitlen,
      show 4 + 2 * (τ : ℕ) + j - 4 = 2 * τ + j by omega, List.map_append, snapWorkSrcs,
      List.map_flatMap, getD_flatMap_chunk _ _ (c := 2) (fun _ => by simp) _
        (by simp) hj, List.getElem_finRange]
    have hc : cellIdx M ℓ.length T t τ (2 * T) < snapIdx M ℓ.length T t :=
      (cellIdx_lt_inpIdx M ℓ.length T t τ (by omega) 0).trans
        (inpIdx_lt_snapIdx M ℓ.length T t (by omega))
    have hz : 2 * (T : ℤ) - T = T := by ring
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
        Fin.cast_mk, Fin.eta] <;>
      rw [eval_block hB hc, cfgExp_cellIdx M ℓ T w t τ (by omega)] <;>
      simp [cellExp, optBits, hz, workChain_right M w ht τ]
  -- apply the snapshot rule; the remaining goals are the source bits, in order
  apply cfgF_snap M w t l
  · rw [g 0 (by omega)]; simp [hlit, BitSrc.eval]
  · intro h0
    rw [g 1 (by omega)]
    simp only [hlit, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
      if_neg h0]
    have hlt : snapIdx M ℓ.length T (t - 1) < snapIdx M ℓ.length T t := by
      have h1 := snapIdx_lt_succ M ℓ.length T (t - 1)
      rw [Nat.sub_add_cancel (by omega)] at h1
      simp only [snapIdx] at h1 ⊢; omega
    rw [eval_block hB hlt, cfgExp_snapIdx, snapExp,
      List.getD_append_right _ _ _ _ (by simp)]
    simp
  · rw [g 2 (by omega)]
    simp only [hlit, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
    rw [eval_block hB hinp, cfgExp_inpIdx M ℓ T w t (by omega), hinpc]
    simp [optBits]
  · rw [g 3 (by omega)]
    simp only [hlit, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
    rw [eval_block hB hinp, cfgExp_inpIdx M ℓ T w t (by omega), hinpc]
    simp [optBits]
  · intro τ
    have := hwork τ 0 (by omega)
    simpa [optBits] using this
  · intro τ
    have := hwork τ 1 (by omega)
    rw [show 4 + 2 * (τ : ℕ) + 1 = 5 + 2 * τ by omega] at this
    simpa [optBits] using this
  · intro h0
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have key := drop_take_padSrcs (M := M) (f := BitSrc.eval x blocks)
      (lit ++ snapWorkSrcs (M := M) (ℓ := ℓ) (T := T) (t' + 1)) (prevSnapSrcs M ℓ T (t' + 1))
    simp only [List.length_append, length_snapWorkSrcs, length_prevSnapSrcs, hlit,
      List.length_cons, List.length_nil] at key
    have hlt : snapIdx M ℓ.length T t' < snapIdx M ℓ.length T (t' + 1) := by
      have h1 := snapIdx_lt_succ M ℓ.length T t'
      simp only [snapIdx] at h1 ⊢; omega
    rw [hl, hsplit, show 4 + 2 * M.k = 0 + 1 + 1 + 1 + 1 + 2 * M.k by omega, key,
      prevSnapSrcs_eval hB hlt, snapDecode_snapEncode, Nat.add_sub_cancel]

/-! ## Well-formedness -/

section WF

variable {n : ℕ}

private theorem prev_lt {t i : ℕ} {a : ℕ} (ha : a < t * cfgStride M ℓ.length T)
    (hi : t * cfgStride M ℓ.length T ≤ i) : a < i := lt_of_lt_of_le ha hi

private theorem prevStep_lt {t a i : ℕ} (ht : t ≠ 0)
    (ha : a < (t - 1 + 1) * cfgStride M ℓ.length T) (hi : t * cfgStride M ℓ.length T ≤ i) :
    a < i := by
  rw [Nat.sub_add_cancel (by omega)] at ha; omega

/-- The previous-snapshot sources read only blocks of the previous step. -/
theorem prevSnapSrcs_valid {t i : ℕ} (hi : t * cfgStride M ℓ.length T ≤ i) :
    ∀ s ∈ prevSnapSrcs M ℓ T t, s.Valid n (cfgWidth M) i := by
  intro s hs
  simp only [prevSnapSrcs, List.mem_map, List.mem_range] at hs
  obtain ⟨j, hj, rfl⟩ := hs
  split_ifs with h
  · trivial
  · exact ⟨prevStep_lt h (snapIdx_lt_succ M ℓ.length T (t - 1)) hi, by unfold cfgWidth; omega⟩

/-- The sources of a work-cell instruction are valid: they read only earlier blocks.

**Proof sketch.** Each source is a constant, a block of the previous step (before
the current step's first block, `Complexity.cellIdx_lt_succ`), or the block of the cell to
the left in the same step. -/
theorem cellSrcs_valid {t : ℕ} {τ : Fin M.k} {r : ℕ} (hr : r < 2 * T + 1) :
    ∀ s ∈ cellSrcs M ℓ T t τ r, s.Valid n (cfgWidth M) (cellIdx M ℓ.length T t τ r) := by
  have hle := le_cellIdx M ℓ.length T t τ r
  have hw : ∀ j, j < 5 → j < cfgWidth M := fun j hj => by unfold cfgWidth; omega
  have hnb : ∀ r' (ok : Bool) j, j < 5 → (ok = true → r' < 2 * T + 1) →
      (nbSrc M ℓ T t τ r' ok j).Valid n (cfgWidth M) (cellIdx M ℓ.length T t τ r) := by
    intro r' ok j hj hok
    unfold nbSrc
    split_ifs with h
    · exact ⟨prevStep_lt h.1 (cellIdx_lt_succ M ℓ.length T (t - 1) τ (hok h.2)) hle, hw j hj⟩
    · trivial
  have hch : ∀ j, j < 5 →
      (chSrc M ℓ T t τ r j).Valid n (cfgWidth M) (cellIdx M ℓ.length T t τ r) := by
    intro j hj
    unfold chSrc
    split_ifs with h
    · exact ⟨by simp only [cellIdx]; omega, hw j hj⟩
    · trivial
  intro s hs
  simp only [cellSrcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    hs
  all_goals first
    | trivial
    | exact hnb _ _ _ (by omega) (fun h => by simp at h; omega)
    | exact hnb _ _ _ (by omega) (fun _ => hr)
    | exact hch _ (by omega)
    | exact prevSnapSrcs_valid hle s hs

/-- The sources of an input instruction are valid: they read only earlier blocks and the layout.

**Proof sketch.** Constants are valid.  The previous-step head bits and the
previous snapshot are blocks of step `t − 1`, hence before step `t`.  The same-step
running symbol is the block of position `p − 1 < p`.  A layout entry is an input or a
constant by hypothesis (validity at instruction `0` excludes blocks), so it is valid
everywhere. -/
theorem inpSrcs_valid (hℓ : ∀ s ∈ ℓ, s.Valid n (cfgWidth M) 0) {t p : ℕ}
    (hp : p < ℓ.length + 2) :
    ∀ s ∈ inpSrcs M ℓ T t p, s.Valid n (cfgWidth M) (inpIdx M ℓ.length T t p) := by
  have hle : t * cfgStride M ℓ.length T ≤ inpIdx M ℓ.length T t p := by
    simp only [inpIdx]; omega
  have hw : ∀ j, j < 5 → j < cfgWidth M := fun j hj => by unfold cfgWidth; omega
  have hih : ∀ p' (ok : Bool), (ok = true → t ≠ 0 ∧ p' < ℓ.length + 2) →
      (ihSrc M ℓ T t p' ok).Valid n (cfgWidth M) (inpIdx M ℓ.length T t p) := by
    intro p' ok hok
    unfold ihSrc
    split_ifs with h
    · exact ⟨prevStep_lt (hok h).1 (inpIdx_lt_succ M ℓ.length T (t - 1) (hok h).2) hle,
        hw 0 (by omega)⟩
    · trivial
  have hich : ∀ j, j < 5 →
      (ichSrc M ℓ T t p j).Valid n (cfgWidth M) (inpIdx M ℓ.length T t p) := by
    intro j hj
    unfold ichSrc
    split_ifs with h
    · exact ⟨by simp only [inpIdx]; omega, hw j hj⟩
    · trivial
  -- case on the source
  intro s hs
  simp only [inpSrcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hs
  all_goals first
    | trivial
    | exact hih _ _ (fun h => by simp at h; omega)
    | exact hich _ (by omega)
    | exact prevSnapSrcs_valid hle s hs
    | skip
  split_ifs with h
  · have hm : ℓ.getD (p - 1) (.const false) ∈ ℓ := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have := hℓ _ hm
    revert this
    cases ℓ.getD (p - 1) (.const false) with
    | input k => exact id
    | const b => exact fun _ => trivial
    | block a j => exact fun h => absurd h.1 (Nat.not_lt_zero _)
  · trivial

/-- The sources of a snapshot instruction are valid: they read only earlier blocks.

**Proof sketch.** Each source is a constant, a block of the previous step, or a block of
the same step that comes before the snapshot: the input block `N + 1` and the work-cell
blocks at the right end of each window. -/
theorem snapSrcs_valid {t : ℕ} :
    ∀ s ∈ snapSrcs M ℓ T t, s.Valid n (cfgWidth M) (snapIdx M ℓ.length T t) := by
  have hle : t * cfgStride M ℓ.length T ≤ snapIdx M ℓ.length T t := by
    simp only [snapIdx]; omega
  have hw : ∀ j, j < 5 → j < cfgWidth M := fun j hj => by unfold cfgWidth; omega
  intro s hs
  simp only [snapSrcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_finRange, true_and] at hs
  rcases hs with ((rfl | rfl | rfl | rfl) | ⟨τ, hs⟩) | hs
  · trivial
  · split_ifs with h
    · trivial
    · exact ⟨prevStep_lt h (snapIdx_lt_succ M ℓ.length T (t - 1)) hle, by unfold cfgWidth; omega⟩
  · exact ⟨inpIdx_lt_snapIdx M ℓ.length T t (by omega), hw 1 (by omega)⟩
  · exact ⟨inpIdx_lt_snapIdx M ℓ.length T t (by omega), hw 2 (by omega)⟩
  · have hc := (cellIdx_lt_inpIdx M ℓ.length T t τ (show 2 * T < 2 * T + 1 by omega) 0).trans
      (inpIdx_lt_snapIdx M ℓ.length T t (by omega))
    rcases hs with rfl | rfl
    · exact ⟨hc, hw 3 (by omega)⟩
    · exact ⟨hc, hw 4 (by omega)⟩
  · exact prevSnapSrcs_valid hle s hs

/-- A padded source list has exactly `cfgArity M` entries. -/
theorem length_padSrcs (l : List BitSrc) (hl : l.length ≤ cfgArity M) :
    (padSrcs M l).length = cfgArity M := by
  simp [padSrcs]; omega

/-- The configuration-tableau program is well formed, with `cfgArity M` sources per
instruction.

**Proof sketch.** Decode the instruction index as a work cell, an input position or a
snapshot (`Complexity.cfgIdx_cases`).  Its sources are the padded sources of that kind,
valid by `Complexity.cellSrcs_valid`, `Complexity.inpSrcs_valid` or
`Complexity.snapSrcs_valid` (padding adds only constants).  The source counts are at most
`cfgArity M`, so padding makes them exactly `cfgArity M`. -/
theorem cfgProg_wf (hℓ : ∀ s ∈ ℓ, s.Valid n (cfgWidth M) 0) :
    ProgWF n (cfgWidth M) (cfgProg M ℓ T) ∧
      ∀ ins ∈ cfgProg M ℓ T, ins.srcs.length = cfgArity M := by
  constructor
  · -- validity: decode the instruction and use the per-kind validity lemmas
    intro i hi s hs
    rw [cfgProg_getElem] at hs
    rw [length_cfgProg] at hi
    have hpad : ∀ l : List BitSrc, s ∈ padSrcs M l → s ∈ l ∨ s = .const false := by
      intro l h
      rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_replicate.mp h).2
    rcases cfgIdx_cases M ℓ.length T hi with ⟨t, -, τ, r, hr, rfl⟩ | ⟨t, -, p, hp, rfl⟩ |
      ⟨t, -, rfl⟩
    · simp only [cfgInstr, cfgPos_cellIdx M ℓ.length T t τ hr] at hs
      rcases hpad _ hs with h | rfl
      · exact cellSrcs_valid hr s h
      · trivial
    · simp only [cfgInstr, cfgPos_inpIdx M ℓ.length T t hp] at hs
      rcases hpad _ hs with h | rfl
      · exact inpSrcs_valid hℓ hp s h
      · trivial
    · simp only [cfgInstr, cfgPos_snapIdx M ℓ.length T t] at hs
      rcases hpad _ hs with h | rfl
      · exact snapSrcs_valid s h
      · trivial
  · -- arity: every padded source list has exactly `cfgArity M` entries
    intro ins hins
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hins
    unfold cfgInstr
    split <;> apply length_padSrcs
    · simp [cellSrcs, cfgArity]
    · simp [inpSrcs, cfgArity]; omega
    · rename_i t _
      rw [show snapSrcs M ℓ T t = _ ++ snapWorkSrcs (M := M) (ℓ := ℓ) (T := T) t ++
        prevSnapSrcs M ℓ T t from rfl]
      simp [cfgArity]; omega

end WF

/-! ## Correctness of the program and the circuit -/

/-- Sources of the layout (inputs and constants) do not read blocks. -/
private theorem eval_layout {n : ℕ} {s : BitSrc} (hs : s.Valid n (cfgWidth M) 0) (x : List Bool)
    (bs : List (List Bool)) : BitSrc.eval x bs s = BitSrc.eval x [] s := by
  cases s with
  | input k => rfl
  | const b => rfl
  | block a j => exact absurd hs.1 (Nat.not_lt_zero _)

/-- **Every block of the configuration-tableau program is the true block** (for the virtual
input `ℓ(x)`).

**Proof sketch.** Strong induction on the block index.  Each block is the local rule of its
kind applied to its sources (`BoolCircuit.progBlocks_getD`), which read only earlier,
hence correct, blocks; `Complexity.CfgTableau.cell_block` and the private lemmas `inp_block` and
`snap_block` then give the true block. -/
theorem cfgProg_blocks {n : ℕ} (hℓ : ∀ s ∈ ℓ, s.Valid n (cfgWidth M) 0) (x : List Bool) :
    ∀ i < (cfgProg M ℓ T).length, (progBlocks (cfgF M) x (cfgProg M ℓ T)).getD i [] =
      cfgExp M ℓ T (ℓ.map (BitSrc.eval x [])) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hB : ∀ i' < i, (progBlocks (cfgF M) x (cfgProg M ℓ T)).getD i' [] =
      cfgExp M ℓ T (ℓ.map (BitSrc.eval x [])) i' := fun i' h => ih i' h (by omega)
  rw [progBlocks_getD (cfgF M) x _ (cfgProg_wf hℓ).1 hi, cfgProg_getElem]
  rw [length_cfgProg] at hi
  rcases cfgIdx_cases M ℓ.length T hi with ⟨t, ht, τ, r, hr, rfl⟩ | ⟨t, ht, p, hp, rfl⟩ |
    ⟨t, ht, rfl⟩
  · simp only [cfgInstr, cfgPos_cellIdx M ℓ.length T t τ hr]
    rw [cfgExp_cellIdx M ℓ T _ t τ hr]
    exact cell_block hB ht hr
  · simp only [cfgInstr, cfgPos_inpIdx M ℓ.length T t hp]
    rw [cfgExp_inpIdx M ℓ T _ t hp]
    exact inp_block (fun s hs bs => eval_layout (hℓ s hs) x bs) hB hp
  · simp only [cfgInstr, cfgPos_snapIdx M ℓ.length T t]
    rw [cfgExp_snapIdx M ℓ T _ t]
    exact snap_block hB ht

variable (M) in
/-- **The configuration-tableau circuit** of `M` on `n` inputs, for the virtual input laid
out by `ℓ` and `T` steps: the compiled program, with output the accumulator of step `T`. -/
noncomputable def cfgCircuit (n : ℕ) (ℓ : List BitSrc) (T : ℕ) : DAGCircuit n :=
  progCircuit (cfgArity M) (cfgWidth M) (cfgF M) n (cfgProg M ℓ T) (snapIdx M ℓ.length T T)
    (snapWidth M)

variable (M) in
/-- The per-instruction gate count of the configuration tableau: a constant of `M`. -/
noncomputable def cfgConst : ℕ :=
  Finset.univ.sup (kindWidth (cfgArity M) (cfgWidth M) (cfgF M))

/-- **Correctness of the configuration-tableau circuit**: on input `x` it outputs `1` iff
some step `s < T` of `M`'s run on the virtual input `ℓ(x)` emits `1`. -/
theorem cfgCircuit_eval {n : ℕ} (hℓ : ∀ s ∈ ℓ, s.Valid n (cfgWidth M) 0) (x : Fin n → Bool) :
    (cfgCircuit M n ℓ T).eval x = decide (∃ s < T,
      emitted M (snapshotAt M (ℓ.map (BitSrc.eval (List.ofFn x) [])) s) = some true) := by
  have hlt : snapIdx M ℓ.length T T < (cfgProg M ℓ T).length := by
    rw [length_cfgProg]; exact snapIdx_lt_succ M ℓ.length T T
  rw [cfgCircuit, progCircuit_eval _ _ _ _ (cfgProg_wf hℓ).1 (cfgProg_wf hℓ).2 hlt
    (by unfold cfgWidth; omega), cfgProg_blocks hℓ _ _ hlt, cfgExp_snapIdx, snapExp,
    List.getD_append_right _ _ _ _ (by simp)]
  simp [tableauAccepted]

/-- The configuration-tableau circuit has fan-in at most two. -/
theorem cfgCircuit_isFaninTwo (n : ℕ) : (cfgCircuit M n ℓ T).IsFaninTwo :=
  progCircuit_isFaninTwo _ _ _ _ _ _ _

/-- The configuration-tableau circuit has at most
`n + 2 + (T + 1)(k (2T + 1) + N + 3) · K_M` vertices. -/
theorem cfgCircuit_size_le (n : ℕ) :
    (cfgCircuit M n ℓ T).size ≤
      n + 2 + (T + 1) * (M.k * (2 * T + 1) + ℓ.length + 3) * cfgConst M := by
  have := progCircuit_size_le (cfgArity M) (cfgWidth M) (cfgF M) n (cfgProg M ℓ T)
    (snapIdx M ℓ.length T T) (snapWidth M)
  rw [length_cfgProg] at this
  exact this

end Complexity
