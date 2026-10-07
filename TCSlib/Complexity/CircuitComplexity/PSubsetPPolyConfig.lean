/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyConfigStep
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyProgram

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The configuration tableau of an arbitrary machine

The classical tableau circuit for an arbitrary (not necessarily oblivious) machine `M`
run for `T` steps on a *virtual* input `w` of length `N` whose bits are input bits or
constants (a `BoolCircuit.BitSrc` layout `ℓ`): for every step `t ≤ T` the circuit holds,
for each work tape and each cell of the window `[−T, T]`, a constant-size block (head
here?, content, running symbol), for each input position a block (head here?, running
symbol), and the snapshot with the acceptance accumulator.  It is written as a gadget
program (`CircuitComplexity/PSubsetPPolyProgram.lean`) over the local rules of
`CircuitComplexity/PSubsetPPolyConfigStep.lean`, and has size
`O(T · (k T + N))`, polynomial in `T` and `N`.

This is a standard (non-[AB09]) configuration tableau adapting the construction of
[AB09, Thm 6.6] to machines that are not known to be oblivious — in this library, for
advice machines, which are only required to behave on pairs `⟨x, αₙ⟩` and so cannot be fed to `Complexity.oblivious_of_mem_DTIME`
(which needs a decider on all inputs).

## Main definitions

* `Complexity.cfgProg M ℓ T` — the gadget program; `Complexity.cfgCircuit M n ℓ T` — its
  circuit.
* `Complexity.cellIdx`, `Complexity.inpIdx`, `Complexity.snapIdx` — the block layout.

## Main results

* `Complexity.cfgCircuit_eval` — on input `x`, the circuit outputs `1` iff some step
  `s < T` of `M`'s run on the virtual input `ℓ(x)` emits `1`.
* `Complexity.cfgCircuit_isFaninTwo`, `Complexity.cfgCircuit_size_le` — fan-in two, and
  size at most `n + 2 + (T + 1)(k(2T + 1) + N + 3) · K_M`.

## Divergences from [AB09]

* The book proves Thm 6.6 only via oblivious machines; this quadratic-size configuration
  tableau is not in [AB09].  It adapts the 6.6 construction and is used here because the
  advice direction of [AB09, Thm 6.18] needs it (see above).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6; §6.3, Theorem 6.18.)
-/

namespace Complexity

open Turing BoolCircuit CfgTableau

variable (M : FinTM Bool)

/-- The block width of the configuration tableau. -/
def cfgWidth : ℕ := snapWidth M + 5

/-- The number of source bits of an instruction (all kinds padded to it). -/
def cfgArity : ℕ := snapWidth M + 2 * M.k + 13

section Layout

variable (N T : ℕ)

/-- The number of blocks per step: `k (2T + 1)` work cells, `N + 2` input positions, one
snapshot. -/
def cfgStride : ℕ := M.k * (2 * T + 1) + N + 3

/-- The block of cell `r` (position `r − T`) of work tape `τ` at step `t`. -/
def cellIdx (t : ℕ) (τ : Fin M.k) (r : ℕ) : ℕ := t * cfgStride M N T + τ * (2 * T + 1) + r

/-- The block of input position `p` at step `t`. -/
def inpIdx (t p : ℕ) : ℕ := t * cfgStride M N T + M.k * (2 * T + 1) + p

/-- The snapshot block of step `t`. -/
def snapIdx (t : ℕ) : ℕ := t * cfgStride M N T + M.k * (2 * T + 1) + N + 2

/-- What a block index stands for. -/
inductive CfgPos (k : ℕ) where
  /-- A work cell. -/
  | cell (t : ℕ) (τ : Fin k) (r : ℕ)
  /-- An input position. -/
  | inp (t p : ℕ)
  /-- A snapshot. -/
  | snap (t : ℕ)

/-- Decode a block index. -/
def cfgPos (i : ℕ) : CfgPos M.k :=
  if h : i % cfgStride M N T < M.k * (2 * T + 1) then
    .cell (i / cfgStride M N T)
      ⟨i % cfgStride M N T / (2 * T + 1), (Nat.div_lt_iff_lt_mul (by omega)).mpr h⟩
      (i % cfgStride M N T % (2 * T + 1))
  else if i % cfgStride M N T < M.k * (2 * T + 1) + N + 2 then
    .inp (i / cfgStride M N T) (i % cfgStride M N T - M.k * (2 * T + 1))
  else .snap (i / cfgStride M N T)

private theorem stride_pos : 0 < cfgStride M N T := by unfold cfgStride; omega

private theorem div_mod_stride (t o : ℕ) (ho : o < cfgStride M N T) :
    (t * cfgStride M N T + o) / cfgStride M N T = t ∧
      (t * cfgStride M N T + o) % cfgStride M N T = o := by
  have hS := stride_pos M N T
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt ho, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]

private theorem cell_off_lt (τ : Fin M.k) {r : ℕ} (hr : r < 2 * T + 1) :
    τ * (2 * T + 1) + r < M.k * (2 * T + 1) := by
  have := Nat.mul_le_mul_right (2 * T + 1) (Nat.succ_le_of_lt τ.isLt)
  rw [Nat.succ_mul] at this; omega

/-- The index of work cell `r` of tape `τ` at step `t` decodes to that cell. -/
theorem cfgPos_cellIdx (t : ℕ) (τ : Fin M.k) {r : ℕ} (hr : r < 2 * T + 1) :
    cfgPos M N T (cellIdx M N T t τ r) = .cell t τ r := by
  have hlt := cell_off_lt M T τ hr
  obtain ⟨h1, h2⟩ := div_mod_stride M N T t (τ * (2 * T + 1) + r)
    (by unfold cfgStride; omega)
  have hdiv : (τ * (2 * T + 1) + r) / (2 * T + 1) = τ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  have hmod : (τ * (2 * T + 1) + r) % (2 * T + 1) = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  unfold cfgPos cellIdx
  rw [Nat.add_assoc] at *
  simp only [h1, h2, dif_pos hlt, hmod]
  congr 1
  exact Fin.ext hdiv

/-- The index of input position `p` at step `t` decodes to that position. -/
theorem cfgPos_inpIdx (t : ℕ) {p : ℕ} (hp : p < N + 2) :
    cfgPos M N T (inpIdx M N T t p) = .inp t p := by
  obtain ⟨h1, h2⟩ := div_mod_stride M N T t (M.k * (2 * T + 1) + p)
    (by unfold cfgStride; omega)
  unfold cfgPos inpIdx
  rw [Nat.add_assoc] at *
  simp only [h1, h2, dif_neg (show ¬ M.k * (2 * T + 1) + p < M.k * (2 * T + 1) by omega),
    if_pos (show M.k * (2 * T + 1) + p < M.k * (2 * T + 1) + N + 2 by omega),
    Nat.add_sub_cancel_left]

/-- The index of the snapshot of step `t` decodes to that snapshot. -/
theorem cfgPos_snapIdx (t : ℕ) : cfgPos M N T (snapIdx M N T t) = .snap t := by
  obtain ⟨h1, h2⟩ := div_mod_stride M N T t (M.k * (2 * T + 1) + N + 2)
    (by unfold cfgStride; omega)
  unfold cfgPos snapIdx
  rw [show t * cfgStride M N T + M.k * (2 * T + 1) + N + 2 =
    t * cfgStride M N T + (M.k * (2 * T + 1) + N + 2) by omega] at *
  simp only [h1, h2, dif_neg (show ¬ M.k * (2 * T + 1) + N + 2 < M.k * (2 * T + 1) by omega),
    if_neg (show ¬ M.k * (2 * T + 1) + N + 2 < M.k * (2 * T + 1) + N + 2 by omega)]

/-- Every block index below `(T + 1) · stride` is a work cell, an input position or a
snapshot of some step `t ≤ T`.

**Proof sketch.** Write `i = (i / S) S + i % S` with `S` the stride, and case on the
offset `i % S`: below `k (2T + 1)` it is `τ (2T + 1) + r` with `τ`, `r` its quotient and
remainder; then come the `N + 2` input positions and finally the snapshot. -/
theorem cfgIdx_cases {i : ℕ} (hi : i < (T + 1) * cfgStride M N T) :
    (∃ t ≤ T, ∃ τ : Fin M.k, ∃ r < 2 * T + 1, i = cellIdx M N T t τ r) ∨
    (∃ t ≤ T, ∃ p < N + 2, i = inpIdx M N T t p) ∨
    (∃ t ≤ T, i = snapIdx M N T t) := by
  have hS := stride_pos M N T
  have ht : i / cfgStride M N T ≤ T := by
    have := (Nat.div_lt_iff_lt_mul hS).mpr hi; omega
  have hdm := Nat.div_add_mod i (cfgStride M N T)
  have e1 := Nat.mul_comm (i / cfgStride M N T) (cfgStride M N T)
  have hmS : i % cfgStride M N T < cfgStride M N T := Nat.mod_lt _ hS
  by_cases h1 : i % cfgStride M N T < M.k * (2 * T + 1)
  · have hτ : i % cfgStride M N T / (2 * T + 1) < M.k :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr h1
    refine Or.inl ⟨_, ht, ⟨_, hτ⟩, i % cfgStride M N T % (2 * T + 1), Nat.mod_lt _ (by omega), ?_⟩
    have := Nat.div_add_mod (i % cfgStride M N T) (2 * T + 1)
    have e2 := Nat.mul_comm (i % cfgStride M N T / (2 * T + 1)) (2 * T + 1)
    simp only [cellIdx]
    omega
  · by_cases h2 : i % cfgStride M N T < M.k * (2 * T + 1) + N + 2
    · refine Or.inr (Or.inl ⟨_, ht, i % cfgStride M N T - M.k * (2 * T + 1), by omega, ?_⟩)
      simp only [inpIdx]; omega
    · refine Or.inr (Or.inr ⟨_, ht, ?_⟩)
      have : i % cfgStride M N T = M.k * (2 * T + 1) + N + 2 := by
        have hSv : cfgStride M N T = M.k * (2 * T + 1) + N + 3 := rfl
        omega
      simp only [snapIdx]; omega

/-- A work-cell block of step `t` comes before every block of step `t + 1`. -/
theorem cellIdx_lt_succ (t : ℕ) (τ : Fin M.k) {r : ℕ} (hr : r < 2 * T + 1) :
    cellIdx M N T t τ r < (t + 1) * cfgStride M N T := by
  have := cell_off_lt M T τ hr
  simp only [cellIdx, Nat.succ_mul, cfgStride] at *; omega

/-- An input block of step `t` comes before every block of step `t + 1`. -/
theorem inpIdx_lt_succ (t : ℕ) {p : ℕ} (hp : p < N + 2) :
    inpIdx M N T t p < (t + 1) * cfgStride M N T := by
  simp only [inpIdx, Nat.succ_mul, cfgStride]; omega

/-- The snapshot block of step `t` comes before every block of step `t + 1`. -/
theorem snapIdx_lt_succ (t : ℕ) : snapIdx M N T t < (t + 1) * cfgStride M N T := by
  simp only [snapIdx, Nat.succ_mul, cfgStride]; omega

/-- A work-cell block of step `t` comes after every block of earlier steps. -/
theorem le_cellIdx (t : ℕ) (τ : Fin M.k) (r : ℕ) : t * cfgStride M N T ≤ cellIdx M N T t τ r := by
  simp only [cellIdx]; omega

/-- Within a step, the input blocks come before the snapshot block. -/
theorem inpIdx_lt_snapIdx (t : ℕ) {p : ℕ} (hp : p < N + 2) :
    inpIdx M N T t p < snapIdx M N T t := by
  simp only [inpIdx, snapIdx]; omega

/-- Within a step, the work-cell blocks come before the input blocks. -/
theorem cellIdx_lt_inpIdx (t : ℕ) (τ : Fin M.k) {r : ℕ} (hr : r < 2 * T + 1) (p : ℕ) :
    cellIdx M N T t τ r < inpIdx M N T t p := by
  have := cell_off_lt M T τ hr
  simp only [cellIdx, inpIdx]; omega

end Layout

/-! ## The program -/

section Program

variable (ℓ : List BitSrc) (T : ℕ)

/-- The sources of the previous snapshot (constants at step `0`). -/
def prevSnapSrcs (t : ℕ) : List BitSrc :=
  (List.range (snapWidth M)).map fun j =>
    if t = 0 then .const false else .block (snapIdx M ℓ.length T (t - 1)) j

/-- Bit `j` of the previous-step block of work cell `r` (if `ok`; else `0`). -/
def nbSrc (t : ℕ) (τ : Fin M.k) (r : ℕ) (ok : Bool) (j : ℕ) : BitSrc :=
  if t ≠ 0 ∧ ok = true then .block (cellIdx M ℓ.length T (t - 1) τ r) j else .const false

/-- Bit `j` of the same-step block of the work cell left of `r` (`0` at `r = 0`). -/
def chSrc (t : ℕ) (τ : Fin M.k) (r j : ℕ) : BitSrc :=
  if r ≠ 0 then .block (cellIdx M ℓ.length T t τ (r - 1)) j else .const false

/-- The sources of work cell `r` of tape `τ` at step `t`, in the layout of `cfgF`. -/
def cellSrcs (t : ℕ) (τ : Fin M.k) (r : ℕ) : List BitSrc :=
  [.const (decide (t = 0)), .const (decide (r = T)),
    nbSrc M ℓ T t τ (r - 1) (decide (1 ≤ r)) 0, nbSrc M ℓ T t τ (r - 1) (decide (1 ≤ r)) 1,
    nbSrc M ℓ T t τ (r - 1) (decide (1 ≤ r)) 2,
    nbSrc M ℓ T t τ r true 0, nbSrc M ℓ T t τ r true 1, nbSrc M ℓ T t τ r true 2,
    nbSrc M ℓ T t τ (r + 1) (decide (r + 1 < 2 * T + 1)) 0,
    nbSrc M ℓ T t τ (r + 1) (decide (r + 1 < 2 * T + 1)) 1,
    nbSrc M ℓ T t τ (r + 1) (decide (r + 1 < 2 * T + 1)) 2,
    chSrc M ℓ T t τ r 3, chSrc M ℓ T t τ r 4] ++ prevSnapSrcs M ℓ T t

/-- The previous-step head bit of input position `p'` (if `ok`; else `0`). -/
def ihSrc (t p' : ℕ) (ok : Bool) : BitSrc :=
  if ok = true then .block (inpIdx M ℓ.length T (t - 1) p') 0 else .const false

/-- Bit `j` of the same-step block of input position `p − 1` (`0` at `p = 0`). -/
def ichSrc (t p j : ℕ) : BitSrc :=
  if p ≠ 0 then .block (inpIdx M ℓ.length T t (p - 1)) j else .const false

/-- The sources of input position `p` at step `t`, in the layout of `cfgF`: the virtual
input bit at `p` is read from the layout `ℓ`. -/
def inpSrcs (t p : ℕ) : List BitSrc :=
  [.const (decide (t = 0)), .const (decide (p = 1)), .const (decide (p = 0)),
    .const (decide (p = ℓ.length + 1)),
    .const (decide (1 ≤ p ∧ p ≤ ℓ.length)),
    if 1 ≤ p ∧ p ≤ ℓ.length then ℓ.getD (p - 1) (.const false) else .const false,
    ihSrc M ℓ T t (p - 1) (decide (t ≠ 0 ∧ 1 ≤ p)), ihSrc M ℓ T t p (decide (t ≠ 0)),
    ihSrc M ℓ T t (p + 1) (decide (t ≠ 0 ∧ p ≤ ℓ.length)),
    ichSrc M ℓ T t p 1, ichSrc M ℓ T t p 2] ++ prevSnapSrcs M ℓ T t

/-- The sources of the snapshot of step `t`, in the layout of `cfgF`. -/
def snapSrcs (t : ℕ) : List BitSrc :=
  [.const (decide (t = 0)),
    if t = 0 then .const false else .block (snapIdx M ℓ.length T (t - 1)) (snapWidth M),
    .block (inpIdx M ℓ.length T t (ℓ.length + 1)) 1,
    .block (inpIdx M ℓ.length T t (ℓ.length + 1)) 2] ++
  (List.finRange M.k).flatMap (fun τ =>
    [.block (cellIdx M ℓ.length T t τ (2 * T)) 3, .block (cellIdx M ℓ.length T t τ (2 * T)) 4]) ++
  prevSnapSrcs M ℓ T t

/-- Pad a source list with constants to the common arity. -/
def padSrcs (l : List BitSrc) : List BitSrc :=
  l ++ List.replicate (cfgArity M - l.length) (.const false)

/-- The instruction of block `i`. -/
def cfgInstr (i : ℕ) : GInstr (CfgKind M.k) :=
  match cfgPos M ℓ.length T i with
  | .cell t τ r => ⟨some (some τ), padSrcs M (cellSrcs M ℓ T t τ r)⟩
  | .inp t p => ⟨some none, padSrcs M (inpSrcs M ℓ T t p)⟩
  | .snap t => ⟨none, padSrcs M (snapSrcs M ℓ T t)⟩

/-- **The configuration-tableau program** of `M` on the virtual input laid out by `ℓ`, for
`T` steps: `(T + 1) · stride` instructions. -/
def cfgProg : List (GInstr (CfgKind M.k)) :=
  (List.range ((T + 1) * cfgStride M ℓ.length T)).map (cfgInstr M ℓ T)

/-- The program has `(T + 1)` steps of `cfgStride` instructions each. -/
@[simp] theorem length_cfgProg :
    (cfgProg M ℓ T).length = (T + 1) * cfgStride M ℓ.length T := by
  simp [cfgProg]

/-- Instruction `i` of the program is `cfgInstr i`. -/
theorem cfgProg_getElem {i : ℕ} (hi : i < (cfgProg M ℓ T).length) :
    (cfgProg M ℓ T)[i] = cfgInstr M ℓ T i := by
  simp [cfgProg]

end Program

/-! ## The true blocks of the program -/

section Correct

variable (ℓ : List BitSrc) (T : ℕ)

/-- The true block at index `i`, for the virtual input `w`. -/
noncomputable def cfgExp (w : List Bool) (i : ℕ) : List Bool :=
  match cfgPos M ℓ.length T i with
  | .cell t τ r => cellExp M w T t τ r
  | .inp t p => inpExp M w t p
  | .snap t => snapExp M w t

/-- The true block at a work-cell index is that cell's true block. -/
theorem cfgExp_cellIdx (w : List Bool) (t : ℕ) (τ : Fin M.k) {r : ℕ} (hr : r < 2 * T + 1) :
    cfgExp M ℓ T w (cellIdx M ℓ.length T t τ r) = cellExp M w T t τ r := by
  simp [cfgExp, cfgPos_cellIdx M ℓ.length T t τ hr]

/-- The true block at an input index is that position's true block. -/
theorem cfgExp_inpIdx (w : List Bool) (t : ℕ) {p : ℕ} (hp : p < ℓ.length + 2) :
    cfgExp M ℓ T w (inpIdx M ℓ.length T t p) = inpExp M w t p := by
  simp [cfgExp, cfgPos_inpIdx M ℓ.length T t hp]

/-- The true block at a snapshot index is the true snapshot block. -/
theorem cfgExp_snapIdx (w : List Bool) (t : ℕ) :
    cfgExp M ℓ T w (snapIdx M ℓ.length T t) = snapExp M w t := by
  simp [cfgExp, cfgPos_snapIdx M ℓ.length T t]

/-- At time `0` the running symbol of a work tape is blank everywhere. -/
theorem workChain_zero (w : List Bool) (τ : Fin M.k) (z : ℤ) : workChain M w 0 τ z = none := by
  unfold workChain
  split <;> simp [cfgAt, MultiTapeTM.runFrom_zero, Cfg.init, Cfg.workTapeSymbols]

/-- Left of the window the running symbol is blank. -/
theorem workChain_left (w : List Bool) {t T : ℕ} (ht : t ≤ T) (τ : Fin M.k) :
    workChain M w t τ (-(T : ℤ) - 1) = none := by
  have := abs_workTapePos_le M w t τ
  rw [abs_le] at this
  unfold workChain
  rw [if_neg (by omega)]

/-- At the right end of the window the running symbol is the symbol under the head. -/
theorem workChain_right (w : List Bool) {t T : ℕ} (ht : t ≤ T) (τ : Fin M.k) :
    workChain M w t τ (T : ℤ) = (cfgAt M w t).workTapeSymbols τ := by
  have := abs_workTapePos_le M w t τ
  rw [abs_le] at this
  unfold workChain
  rw [if_pos (by omega)]

/-- At the right end of the input the running symbol is the input symbol. -/
theorem inpChain_right (w : List Bool) (t : ℕ) :
    inpChain M w t (w.length + 1) = (cfgAt M w t).inputSymbol := by
  unfold inpChain
  rw [if_pos (by have := (cfgAt M w t).inputPos.isLt; omega)]

variable {M ℓ T}

/-- Reading a source whose block is already correct. -/
theorem eval_block {x : List Bool} {blocks : List (List Bool)} {w : List Bool} {i a : ℕ}
    (hB : ∀ i' < i, blocks.getD i' [] = cfgExp M ℓ T w i') (ha : a < i) (j : ℕ) :
    BitSrc.eval x blocks (.block a j) = (cfgExp M ℓ T w a).getD j false := by
  simp only [BitSrc.eval]
  rw [hB a ha]

/-- Padding does not change the values of the original sources. -/
theorem padSrcs_map_take {f : BitSrc → Bool} (l : List BitSrc) :
    (((padSrcs M l).map f).take l.length) = l.map f := by
  simp [padSrcs, List.map_append, List.take_left' (List.length_map _)]

/-- After a prefix, a padded source list continues with the original suffix. -/
theorem drop_take_padSrcs {f : BitSrc → Bool} (pre rest : List BitSrc) :
    (((padSrcs M (pre ++ rest)).map f).drop pre.length).take rest.length = rest.map f := by
  simp only [padSrcs, List.append_assoc, List.map_append]
  rw [List.drop_left' (List.length_map _), List.take_left' (List.length_map _)]

/-- The previous-snapshot sources are `snapWidth M` bits. -/
@[simp] theorem length_prevSnapSrcs (t : ℕ) : (prevSnapSrcs M ℓ T t).length = snapWidth M := by
  simp [prevSnapSrcs]

/-- The previous-snapshot sources carry the encoding of the previous snapshot. -/
theorem prevSnapSrcs_eval {x : List Bool} {blocks : List (List Bool)} {w : List Bool} {i t : ℕ}
    (hB : ∀ i' < i, blocks.getD i' [] = cfgExp M ℓ T w i')
    (hi : snapIdx M ℓ.length T t < i) :
    (prevSnapSrcs M ℓ T (t + 1)).map (BitSrc.eval x blocks) = snapEncode M (snapshotAt M w t) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [prevSnapSrcs, List.map_map, List.getElem_map, List.getElem_range,
    Function.comp, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  rw [eval_block hB hi, cfgExp_snapIdx, snapExp, List.getD_append _ _ _ _ (by simpa using h2),
    List.getD_eq_getElem _ _ (by simpa using h2)]

namespace CfgTableau

/-- **A work-cell block is correct** when all earlier blocks are.

**Proof sketch.** Read the thirteen leading source bits off the padded source list:
the flags `t = 0` and `r = T`; the previous-step blocks of cells `r − 1, r, r + 1` (true
by hypothesis, and constants outside the window, where the head cannot be since
`|pos| ≤ t − 1 < T`); and the same-step running symbol of cell `r − 1` (blank at `r = 0`,
left of the window).  At step `0` conclude with `Complexity.cfgF_cell_zero` (the running
symbol is blank, `Complexity.workChain_zero`).  Otherwise the previous snapshot decodes
correctly (`Complexity.prevSnapSrcs_eval`) and `Complexity.cfgF_cell_succ` concludes. -/
theorem cell_block {x : List Bool} {blocks : List (List Bool)} {w : List Bool} {t : ℕ}
    {τ : Fin M.k} {r : ℕ}
    (hB : ∀ i' < cellIdx M ℓ.length T t τ r, blocks.getD i' [] = cfgExp M ℓ T w i')
    (ht : t ≤ T) (hr : r < 2 * T + 1) :
    cfgF M (some (some τ)) ((padSrcs M (cellSrcs M ℓ T t τ r)).map (BitSrc.eval x blocks)) =
      cellExp M w T t τ r := by
  set l := (padSrcs M (cellSrcs M ℓ T t τ r)).map (BitSrc.eval x blocks) with hl
  have hlt_same : r ≠ 0 → cellIdx M ℓ.length T t τ (r - 1) < cellIdx M ℓ.length T t τ r := by
    intro h; simp only [cellIdx]; omega
  have g : ∀ j (hj : j < 13), l.getD j false = BitSrc.eval x blocks
      ([.const (decide (t = 0)), .const (decide (r = T)),
        nbSrc M ℓ T t τ (r - 1) (decide (1 ≤ r)) 0, nbSrc M ℓ T t τ (r - 1) (decide (1 ≤ r)) 1,
        nbSrc M ℓ T t τ (r - 1) (decide (1 ≤ r)) 2,
        nbSrc M ℓ T t τ r true 0, nbSrc M ℓ T t τ r true 1, nbSrc M ℓ T t τ r true 2,
        nbSrc M ℓ T t τ (r + 1) (decide (r + 1 < 2 * T + 1)) 0,
        nbSrc M ℓ T t τ (r + 1) (decide (r + 1 < 2 * T + 1)) 1,
        nbSrc M ℓ T t τ (r + 1) (decide (r + 1 < 2 * T + 1)) 2,
        chSrc M ℓ T t τ r 3, chSrc M ℓ T t τ r 4].getD j (.const false)) := by
    intro j hj
    rw [hl, padSrcs, cellSrcs, List.append_assoc, List.map_append,
      List.getD_append _ _ _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj),
      List.getElem_map, List.getD_eq_getElem _ _ (by simpa using hj)]
  have hz' : ((r + 1 : ℕ) : ℤ) - T = (r : ℤ) - T + 1 := by push_cast; ring
  -- the running symbol on the left, at the same step
  have hcl : ∀ j, j = 3 ∨ j = 4 → BitSrc.eval x blocks (chSrc M ℓ T t τ r j) =
      (optBits (workChain M w t τ ((r : ℤ) - T - 1))).getD (j - 3) false := by
    intro j hj
    unfold chSrc
    split_ifs with h0
    · rw [eval_block hB (hlt_same h0), cfgExp_cellIdx M ℓ T w t τ (by omega)]
      have : ((r - 1 : ℕ) : ℤ) - T = (r : ℤ) - T - 1 := by omega
      rcases hj with rfl | rfl <;> simp [cellExp, optBits, this]
    · have h0 : r = 0 := by omega
      subst h0
      have := workChain_left M w ht τ
      simp only [Nat.cast_zero, zero_sub] at this ⊢
      rcases hj with rfl | rfl <;> simp [BitSrc.eval, this, optBits]
  cases t with
  | zero =>
    -- step `0`: the head is at the origin, everything is blank
    rw [cellExp]
    apply cfgF_cell_zero M w τ ((r : ℤ) - T) l
    · rw [g 0 (by omega)]; simp [BitSrc.eval]
    · rw [g 1 (by omega)]; simp only [BitSrc.eval, List.getD_cons_succ, List.getD_cons_zero]
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
    · rw [g 11 (by omega)]
      have := hcl 3 (Or.inl rfl)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this, workChain_zero]; rfl
  | succ t =>
    -- step `t + 1`: previous-step neighbour blocks, then the local rule
    have hprev_lt : ∀ r', r' < 2 * T + 1 →
        cellIdx M ℓ.length T t τ r' < cellIdx M ℓ.length T (t + 1) τ r := fun r' hr' =>
      (cellIdx_lt_succ M ℓ.length T t τ hr').trans_le (le_cellIdx M ℓ.length T (t + 1) τ r)
    have hnb : ∀ r' (ok : Bool) j, (ok = true → r' < 2 * T + 1) →
        BitSrc.eval x blocks (nbSrc M ℓ T (t + 1) τ r' ok j) =
          if ok then (cellExp M w T t τ r').getD j false else false := by
      intro r' ok j hok
      unfold nbSrc
      cases ok with
      | false => simp [BitSrc.eval]
      | true =>
        simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, and_self, if_true,
          Nat.add_sub_cancel]
        rw [eval_block hB (hprev_lt r' (hok rfl)), cfgExp_cellIdx M ℓ T w t τ (hok rfl)]
    have hpos := abs_workTapePos_le M w t τ
    rw [abs_le] at hpos
    rw [cellExp]
    apply cfgF_cell_succ M w t τ ((r : ℤ) - T) l
    · rw [g 0 (by omega)]; simp [BitSrc.eval]
    · have key := drop_take_padSrcs (M := M) (f := BitSrc.eval x blocks)
        [.const (decide (t + 1 = 0)), .const (decide (r = T)),
          nbSrc M ℓ T (t + 1) τ (r - 1) (decide (1 ≤ r)) 0,
          nbSrc M ℓ T (t + 1) τ (r - 1) (decide (1 ≤ r)) 1,
          nbSrc M ℓ T (t + 1) τ (r - 1) (decide (1 ≤ r)) 2,
          nbSrc M ℓ T (t + 1) τ r true 0, nbSrc M ℓ T (t + 1) τ r true 1,
          nbSrc M ℓ T (t + 1) τ r true 2,
          nbSrc M ℓ T (t + 1) τ (r + 1) (decide (r + 1 < 2 * T + 1)) 0,
          nbSrc M ℓ T (t + 1) τ (r + 1) (decide (r + 1 < 2 * T + 1)) 1,
          nbSrc M ℓ T (t + 1) τ (r + 1) (decide (r + 1 < 2 * T + 1)) 2,
          chSrc M ℓ T (t + 1) τ r 3, chSrc M ℓ T (t + 1) τ r 4] (prevSnapSrcs M ℓ T (t + 1))
      simp only [List.length_cons, List.length_nil, length_prevSnapSrcs] at key
      rw [hl, cellSrcs, key, prevSnapSrcs_eval hB
        ((snapIdx_lt_succ M ℓ.length T t).trans_le (le_cellIdx M ℓ.length T (t + 1) τ r)),
        snapDecode_snapEncode]
    · rw [g 2 (by omega)]
      have := hnb (r - 1) (decide (1 ≤ r)) 0 (fun _ => by omega)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]
      by_cases h1 : 1 ≤ r
      · simp only [h1, decide_true, if_true, cellExp, List.getD_cons_zero]
        congr 2; omega
      · simp only [h1, decide_false, Bool.false_eq_true, if_false]
        symm; rw [decide_eq_false_iff_not]; omega
    · rw [g 5 (by omega)]
      have := hnb r true 0 (fun _ => hr)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [cellExp]
    · rw [g 8 (by omega)]
      have := hnb (r + 1) (decide (r + 1 < 2 * T + 1)) 0 (fun h => by simpa using h)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]
      by_cases h1 : r + 1 < 2 * T + 1
      · simp only [h1, decide_true, if_true, cellExp, List.getD_cons_zero, hz']
      · simp only [h1, decide_false, Bool.false_eq_true, if_false]
        symm; rw [decide_eq_false_iff_not]; omega
    · rw [g 6 (by omega)]
      have := hnb r true 1 (fun _ => hr)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [cellExp, optBits]
    · rw [g 7 (by omega)]
      have := hnb r true 2 (fun _ => hr)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [cellExp, optBits]
    · rw [g 11 (by omega)]
      have := hcl 3 (Or.inl rfl)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [optBits]
    · rw [g 12 (by omega)]
      have := hcl 4 (Or.inr rfl)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
      rw [this]; simp [optBits]

end CfgTableau

end Correct

end Complexity
