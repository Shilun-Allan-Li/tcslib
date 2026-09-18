/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines: the setup phase

This file analyses the initialization of the length-only schedule. The explicit
configuration `setupCfg` isolates the three controller tapes, and phase-by-phase
run identities cover the arbitrary-input reset, the captured clock-word copy,
the fixed-width binary-budget conversion with its unary appends and borrow
sweeps, and the guide-zone layout in both directions. They compose into
`setupCfg_initializes`, the complete initialization run with its exact cost.
It was split out mechanically from `Robustness/Oblivious.lean` at the epoch-3→4
merge; provenance: epoch-3 fill, batch C.

## Main definitions

* `Complexity.setupCfg` — explicit setup configurations of the schedule.
* `Complexity.unaryTape` — the unary macrostep counter tape.

## Main results

* `Complexity.setupCfg_initializes` — the schedule's complete initialization run,
  from the reset start to the first macrostep check, with its exact duration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, Exercise 1.5.)
-/

namespace Complexity

open Turing

/-- An explicit setup configuration separates the captured clock work from
the three controller tapes. It is also used before the native input is parked. -/
def setupCfg (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x :=
  ⟨q, p, Fin.addCases (fun i => base.workTapes (i.castAdd 3))
    (fun j => if j.val = 0 then bt else if j.val = 1 then ut else gt),
    Fin.addCases (fun i => base.workTapePos (i.castAdd 3))
    (fun j => if j.val = 0 then b else if j.val = 1 then u else g), base.output⟩

/-- Applying a controller write to one explicit setup tape. -/
def setupWrite {A : Type} (t : ℤ → Option A) (z : ℤ)
    (w : Option (Option A)) : ℤ → Option A :=
  match w with | none => t | some s => Function.update t z s

/-- Setup actions update precisely the three explicit tapes and their heads. -/
private lemma setupCfg_apply (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q q' : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) (di : SignType)
    (ba ua ga : Option (Option OblSymbol) × SignType) :
    (oblAction (k := W.k) q' di ba ua ga).apply (setupCfg W a base q p b u g bt ut gt) =
      setupCfg W a base q' (moveInputPos p di) (b + ba.2) (u + ua.2) (g + ga.2)
        (setupWrite bt b ba.1) (setupWrite ut u ua.1) (setupWrite gt g ga.1) := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl
      · cases hb : ba.1 <;> simp [oblAction, setupCfg, setupWrite, hb]
      · cases hu : ua.1 <;> simp [oblAction, setupCfg, setupWrite, hu]
      · cases hg : ga.1 <;> simp [oblAction, setupCfg, setupWrite, hg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [oblAction, setupCfg]
  · exact List.append_nil _

/-- The native input read depends on the explicit setup input coordinate. -/
private lemma setupCfg_input (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    (setupCfg W a base q p b u g bt ut gt).inputSymbol =
      if p.val = 0 then none else x[p.val - 1]? := by
  unfold Cfg.inputSymbol
  simp only [setupCfg, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

/-- Read the three controller tapes in an explicit setup configuration. -/
private lemma setupCfg_reads (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    (fun j : Fin 3 => (setupCfg W a base q p b u g bt ut gt).workTapeSymbols (j.natAdd W.k)) =
      fun j => if j.val = 0 then bt b else if j.val = 1 then ut u else gt g := by
  funext j
  rcases finThree_cases j with rfl | rfl | rfl <;> simp [setupCfg, Cfg.workTapeSymbols]

/-- The input reset scans a known interior prefix to the left boundary in
exactly its length, preserving every work tape and work head. -/
private lemma setupCfg_reset_scan (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) (j : ℕ) (hj : j ≤ x.length) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .resetScan) ⟨j, by omega⟩ b u g bt ut gt) j =
      setupCfg W a base (some .resetScan) 0 b u g bt ut gt := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hin : (setupCfg W a base (some .resetScan) ⟨j + 1, by omega⟩ b u g bt ut gt).inputSymbol =
        some (x[j]'(by omega)) := by
      rw [setupCfg_input]
      simp
    change (obliviousSchedule W a).tm.runFrom
      (((obliviousSchedule W a).tm.tr .resetScan _ _).apply _) j = _
    rw [show (obliviousSchedule W a).tm.tr .resetScan
        (setupCfg W a base (some .resetScan) ⟨j + 1, by omega⟩ b u g bt ut gt).inputSymbol
        _ = oblAction (k := W.k) (some .resetScan) .neg (none, 0) (none, 0) (none, 0) by
      simp only [obliviousSchedule, hin]]
    rw [setupCfg_apply]
    simp only [setupWrite, SignType.coe_zero, add_zero]
    have hp : moveInputPos (⟨j + 1, by omega⟩ : Fin (x.length + 2)) .neg =
        ⟨j, by omega⟩ := by
      apply Fin.ext
      simp [moveInputPos, show j < x.length + 2 by omega]
    rw [hp]
    exact ih (by omega)

/-- Reset begins with a mandatory left move, so even the right blank boundary
and the empty input reach the left boundary before the final right move. -/
private lemma setupCfg_reset (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .resetStart) p b u g bt ut gt) (p.val - 1 + 2) =
      setupCfg W a base (some .copyLeft) ⟨1, by omega⟩ b u g bt ut gt := by
  have hp : moveInputPos p .neg = (⟨p.val - 1, by have := p.isLt; omega⟩ : Fin (x.length + 2)) := by
    apply Fin.ext
    simp only [moveInputPos, SignType.cast]
    split <;> simp_all <;> have := p.isLt <;> omega
  have hs : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .resetStart) p b u g bt ut gt) =
      setupCfg W a base (some .resetScan) ⟨p.val - 1, by have := p.isLt; omega⟩ b u g bt ut gt := by
    change ((obliviousSchedule W a).tm.tr .resetStart _ _).apply _ = _
    simp only [obliviousSchedule]
    rw [setupCfg_apply, hp]
    simp [setupWrite]
  have hs1 : (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .resetStart) p b u g bt ut gt) 1 =
      setupCfg W a base (some .resetScan) ⟨p.val - 1, by have := p.isLt; omega⟩ b u g bt ut gt := by
    simpa only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero] using hs
  rw [show p.val - 1 + 2 = 1 + (p.val - 1) + 1 by omega,
    MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hs1,
    setupCfg_reset_scan W a base b u g bt ut gt _ (by have := p.isLt; omega)]
  change ((obliviousSchedule W a).tm.tr .resetScan _ _).apply _ = _
  simp only [obliviousSchedule, setupCfg_input, Fin.val_zero, if_true]
  rw [setupCfg_apply]
  simp [setupWrite, moveInputPos]

/-- The partial guide after copying `j` native symbols. The left virtual
boundary has already been marked, and the origin is written on the first read. -/
private def copyGuide (j : ℕ) (z : ℤ) : Option OblSymbol :=
  if z = -1 then some .inside else if 0 ≤ z ∧ z < j then
    some (if z = 0 then .origin else .inside) else none

/-- The next copied symbol extends the guide by one cell. -/
private lemma copyGuide_next (j : ℕ) :
    Function.update (copyGuide j) (j : ℤ) (some (if j = 0 then .origin else .inside)) =
      copyGuide (j + 1) := by
  funext z
  by_cases hz : z = (j : ℤ)
  · subst z
    simp [copyGuide, show (j : ℤ) ≠ -1 by omega]
  · rw [Function.update_of_ne hz]
    have hh : (0 ≤ z ∧ z < (j : ℤ)) ↔ (0 ≤ z ∧ z < (j + 1 : ℕ)) := by omega
    simp only [copyGuide, hh]

/-- On a completed copied prefix, only the origin carries its special tag. -/
private lemma copyGuide_origin (j : ℕ) (z : ℤ) (hj : 0 < j) :
    copyGuide j z = some .origin ↔ z = 0 := by
  unfold copyGuide
  split_ifs <;> simp_all <;> omega

/-- The first input read marks the origin; subsequent reads use the same
copy loop without changing that mark. -/
private def copyPhase {S : Type} {a : ℕ} (j : ℕ) : OblPhase S a :=
  if j = 0 then .copyFirst else .copyMore

/-- The two left-boundary setup steps precede every copy, including empty input. -/
private lemma setupCfg_copy_left (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u : ℤ) (bt ut : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .copyLeft) p b u 0 bt ut (fun _ => none)) 2 =
      setupCfg W a base (some (copyPhase 0)) p b u 0 bt ut (copyGuide 0) := by
  have hc : Function.update (fun _ : ℤ => (none : Option OblSymbol)) (-1) (some .inside) =
      copyGuide 0 := by
    funext z
    simp only [Function.update_apply, copyGuide, Int.natCast_zero]
    split_ifs <;> first | rfl | omega
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (obliviousSchedule W a).tm.step
      (((obliviousSchedule W a).tm.tr .copyLeft _ _).apply _) = _
  simp only [obliviousSchedule]
  rw [setupCfg_apply]
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero,
    SignType.coe_neg_one, zero_add]
  change ((obliviousSchedule W a).tm.tr .copyLeftWrite _ _).apply _ = _
  simp only [obliviousSchedule]
  rw [setupCfg_apply]
  simp [setupWrite, hc, copyPhase]

/-- After any prefix of the copy scan, the native and guide heads have made
exactly the same number of right moves. No data value selects a movement. -/
private lemma setupCfg_copy_prefix (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (b u : ℤ) (bt ut : ℤ → Option OblSymbol) (j : ℕ) (hj : j ≤ x.length) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (copyPhase 0)) ⟨1, by omega⟩ b u 0 bt ut (copyGuide 0)) j =
      setupCfg W a base (some (copyPhase j)) ⟨j + 1, by omega⟩ b u j bt ut (copyGuide j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (setupCfg W a base (some (copyPhase j)) ⟨j + 1, by omega⟩ b u j bt ut
        (copyGuide j)).inputSymbol = some (x[j]'(by omega)) := by
      rw [setupCfg_input]
      simp
    have htr : ∀ ws, (obliviousSchedule W a).tm.tr (copyPhase j)
        (setupCfg W a base (some (copyPhase j)) ⟨j + 1, by omega⟩ b u j bt ut
          (copyGuide j)).inputSymbol ws =
        oblAction (k := W.k) (some (copyPhase (j + 1))) .pos (none, 0) (none, 0)
          (some (some (if j = 0 then .origin else .inside)), .pos) := by
      intro ws
      rw [hin]
      by_cases hz : j = 0 <;> simp [copyPhase, hz, obliviousSchedule]
    change ((obliviousSchedule W a).tm.tr (copyPhase j) _ _).apply _ = _
    rw [htr, setupCfg_apply]
    simp only [setupWrite, SignType.coe_zero, add_zero, SignType.coe_one, copyGuide_next]
    have hp : moveInputPos (⟨j + 1, by omega⟩ : Fin (x.length + 2)) .pos =
        ⟨j + 1 + 1, by omega⟩ := by
      apply Fin.ext
      simp only [moveInputPos, SignType.cast]
      split <;> simp_all <;> omega
    rw [hp]
    rfl

/-- The final blank read parks the input head and closes the copied guide. -/
private lemma setupCfg_copy_end (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (b u : ℤ) (bt ut : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (copyPhase x.length)) ⟨x.length + 1, by omega⟩
        b u x.length bt ut (copyGuide x.length)) =
      setupCfg W a base (some .copyReturn) ⟨x.length + 1, by omega⟩
        b u x.length bt ut (copyGuide (x.length + 1)) := by
  have hin : (setupCfg W a base (some (copyPhase x.length)) ⟨x.length + 1, by omega⟩
      b u x.length bt ut (copyGuide x.length)).inputSymbol = none := by
    rw [setupCfg_input]
    simp
  change ((obliviousSchedule W a).tm.tr (copyPhase x.length) _ _).apply _ = _
  have htr : ∀ ws, (obliviousSchedule W a).tm.tr (copyPhase x.length)
      (setupCfg W a base (some (copyPhase x.length)) ⟨x.length + 1, by omega⟩
        b u x.length bt ut (copyGuide x.length)).inputSymbol ws =
      oblAction (k := W.k) (some .copyReturn) 0 (none, 0) (none, 0)
        (some (some (if x.length = 0 then .origin else .inside)), 0) := by
    intro ws
    rw [hin]
    by_cases hz : x.length = 0 <;> simp [copyPhase, hz, obliviousSchedule]
  rw [htr, setupCfg_apply]
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, copyGuide_next]

/-- Returning across the copied guide costs exactly its current coordinate. -/
private lemma setupCfg_copy_return (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u : ℤ) (bt ut : ℤ → Option OblSymbol) (n j : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .copyReturn) p b u j bt ut (copyGuide (n + 1))) (j + 1) =
      setupCfg W a base (some .budgetStart) p b u 0 bt ut (copyGuide (n + 1)) := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((obliviousSchedule W a).tm.tr .copyReturn _ _).apply _ = _
    have hr : (setupCfg W a base (some .copyReturn) p b u 0 bt ut (copyGuide (n + 1))).workTapeSymbols
        (Fin.natAdd W.k (2 : Fin 3)) = copyGuide (n + 1) 0 := by
      simp [setupCfg, Cfg.workTapeSymbols]
    simp only [Int.natCast_zero, obliviousSchedule, hr,
      copyGuide_origin _ _ (Nat.succ_pos _), ite_true]
    rw [setupCfg_apply]
    simp [setupWrite]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    change (obliviousSchedule W a).tm.runFrom
      (((obliviousSchedule W a).tm.tr .copyReturn _ _).apply _) (j + 1) = _
    have hr : (setupCfg W a base (some .copyReturn) p b u (j + 1) bt ut (copyGuide (n + 1))).workTapeSymbols
        (Fin.natAdd W.k (2 : Fin 3)) = copyGuide (n + 1) (j + 1) := by
      simp [setupCfg, Cfg.workTapeSymbols]
    simp only [Nat.cast_add, Nat.cast_one, obliviousSchedule, hr,
      copyGuide_origin _ _ (Nat.succ_pos _),
      show (j : ℤ) + 1 ≠ 0 by omega, ite_false]
    rw [setupCfg_apply]
    simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero]
    convert ih using 1 <;> congr 1 <;> simp [SignType.cast] <;> omega

/-- The unary macrostep budget, with an origin sentinel and a blank end cell. -/
def unaryTape (N : ℕ) (z : ℤ) : Option OblSymbol :=
  if z = 0 then some .origin else if 1 ≤ z ∧ z ≤ N then some .unit else none

/-- Appending one unary marker extends exactly the allocated prefix. -/
private lemma unaryTape_next (N : ℕ) :
    Function.update (unaryTape N) ((N : ℤ) + 1) (some .unit) = unaryTape (N + 1) := by
  funext z
  by_cases hz : z = (N : ℤ) + 1
  · subst z
    simp [unaryTape, show (N : ℤ) + 1 ≠ 0 by omega]
  · rw [Function.update_of_ne hz]
    have hh : (1 ≤ z ∧ z ≤ (N : ℤ)) ↔ (1 ≤ z ∧ z ≤ (N + 1 : ℕ)) := by omega
    simp only [unaryTape, hh]

/-- Only the origin sentinel terminates the backwards budget scan. -/
private lemma clockTape_origin (w : List Bool) (z : ℤ) :
    clockTape w z = some .origin ↔ z = 0 := by
  by_cases hz : z = 0
  · simp [clockTape, hz]
  · simp only [clockTape, if_neg hz]
    cases FinTM.bufferTape w (z - 1) <;> simp [hz]

/-- The captured budget's right blank is one cell after its full fixed width. -/
private lemma clockTape_end (w : List Bool) : clockTape w ((w.length : ℤ) + 1) = none := by
  simp [clockTape, show (w.length : ℤ) + 1 ≠ 0 by omega]

/-- Rewinding the captured budget reaches its sentinel in exactly the head
coordinate, then moves right once to begin unary generation. -/
private lemma setupCfg_budget_back (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (u g : ℤ) (w : List Bool) (ut gt : ℤ → Option OblSymbol) (j : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .budgetBack) p j u g (clockTape w) ut gt) (j + 1) =
      setupCfg W a base (some (.append 0)) p 1 u g (clockTape w) ut gt := by
  have step (j : ℕ) : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .budgetBack) p j u g (clockTape w) ut gt) =
      if j = 0 then setupCfg W a base (some (.append 0)) p 1 u g (clockTape w) ut gt
      else setupCfg W a base (some .budgetBack) p ((j : ℤ) - 1) u g (clockTape w) ut gt := by
    have hr : (setupCfg W a base (some .budgetBack) p j u g (clockTape w) ut gt).workTapeSymbols
        (Fin.natAdd W.k (0 : Fin 3)) = clockTape w j := by
      simp [setupCfg, Cfg.workTapeSymbols]
    change ((obliviousSchedule W a).tm.tr .budgetBack _ _).apply _ = _
    simp only [obliviousSchedule, hr, clockTape_origin, Int.natCast_eq_zero]
    split <;> rw [setupCfg_apply] <;> simp_all [setupWrite, sub_eq_add_neg]
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step, if_pos rfl]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, step, if_neg (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using ih

/-- A full rewind starts one cell beyond the captured word and costs its
width plus two, independently of all budget bits. -/
private lemma setupCfg_budget_start (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (u g : ℤ) (w : List Bool) (ut gt : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .budgetStart) p (w.length + 1) u g (clockTape w) ut gt)
      (w.length + 2) =
      setupCfg W a base (some (.append 0)) p 1 u g (clockTape w) ut gt := by
  have hs : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .budgetStart) p (w.length + 1) u g (clockTape w) ut gt) =
      setupCfg W a base (some .budgetBack) p w.length u g (clockTape w) ut gt := by
    change ((obliviousSchedule W a).tm.tr .budgetStart _ _).apply _ = _
    simp only [obliviousSchedule]
    rw [setupCfg_apply]
    simp [setupWrite]
  rw [show w.length + 2 = (w.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs, setupCfg_budget_back]

/-- Each finite append phase writes exactly one marker; the phase counter
and unary coordinate advance together through the prescribed constant block. -/
private lemma setupCfg_append_prefix (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (N j : ℕ)
    (hj : j ≤ a + 1) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.append 0)) p b (N + 1) g bt (unaryTape N) gt) j =
      setupCfg W a base (some (.append ⟨j, by omega⟩)) p b (N + j + 1) g bt
        (unaryTape (N + j)) gt := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    change ((obliviousSchedule W a).tm.tr (.append ⟨j, by omega⟩) _ _).apply _ = _
    simp only [obliviousSchedule, show j < a + 1 by omega, dite_true]
    rw [setupCfg_apply]
    simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero]
    rw [show (N : ℤ) + j + 1 = ((N + j : ℕ) : ℤ) + 1 by omega, unaryTape_next]
    congr 1 <;> simp [SignType.cast] <;> omega

/-- Exactly `a+1` appended markers precede the next full-width borrow pass. -/
private lemma setupCfg_append (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (N : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.append 0)) p b (N + 1) g bt (unaryTape N) gt) (a + 2) =
      setupCfg W a base (some (.borrow true)) p b (N + (a + 1) + 1) g bt
        (unaryTape (N + (a + 1))) gt := by
  rw [MultiTapeTM.runFrom_succ_eq_step',
    setupCfg_append_prefix W a base p b g bt gt N (a + 1) (le_refl _)]
  change ((obliviousSchedule W a).tm.tr (.append ⟨a + 1, by omega⟩) _ _).apply _ = _
  simp only [obliviousSchedule, lt_self_iff_false, dite_false]
  rw [setupCfg_apply]
  simp [setupWrite]

/-- Moving a zipper frontier past an unchanged finite word preserves its tape. -/
private lemma sweepTape_shift {A : Type} (z : ℤ) (l w r : List (Option A)) :
    FinTM.sweepTape z l (w ++ r) =
      FinTM.sweepTape (z + w.length) (w.reverse ++ l) r := by
  induction w generalizing z l with
  | nil => simp
  | cons a w ih =>
    have hs : Function.update (FinTM.sweepTape z l (a :: (w ++ r))) z a =
        FinTM.sweepTape z l (a :: (w ++ r)) := by
      funext p
      by_cases hp : p = z
      · subst p
        simp [FinTM.sweepTape_read]
      · exact Function.update_of_ne hp _ _
    have hm := FinTM.sweepTape_right z l (w ++ r) a a
    rw [hs] at hm
    simp only [List.cons_append, List.length_cons, List.reverse_cons]
    rw [hm, ih]
    simp only [List.append_assoc, List.singleton_append]
    congr 1
    omega

/-- A captured budget word is the same tape as its explicit bit zipper. -/
private lemma clockTape_zipper (w : List Bool) :
    clockTape w = FinTM.sweepTape 1 [some .origin] (w.map (fun b => some (.bit b))) := by
  funext z
  by_cases hz : z = 0
  · subst z
    simp [clockTape, FinTM.sweepTape]
  · by_cases hl : z < 1
    · have hn : ¬0 ≤ z - 1 := by omega
      have hi : 1 ≤ (1 - 1 - z).toNat := by omega
      have he : ([some OblSymbol.origin] : List (Option OblSymbol))[(1 - 1 - z).toNat]? = none :=
        List.getElem?_eq_none hi
      simp only [clockTape, if_neg hz, FinTM.bufferTape, if_neg hn, Option.map_none,
        FinTM.sweepTape, if_pos hl, he, Option.join_none]
    · have hn : 0 ≤ z - 1 := by omega
      simp only [clockTape, if_neg hz, FinTM.bufferTape, if_pos hn,
        FinTM.sweepTape, if_neg hl, List.getElem?_map]
      cases w[(z - 1).toNat]? <;> rfl

/-- The rewritten word's end zipper reconstructs the complete captured tape. -/
private lemma clockTape_zipper_end (w : List Bool) :
    FinTM.sweepTape (1 + (w.length : ℤ))
      ((w.map (fun b => some (.bit b))).reverse ++ [some .origin]) [] = clockTape w := by
  rw [clockTape_zipper]
  have h := sweepTape_shift (A := OblSymbol) 1 [some .origin]
    (w.map (fun b => some (.bit b))) []
  simpa only [List.append_nil, List.length_map] using h.symm

/-- Focusing the captured-budget lane preserves the explicit setup structure. -/
private lemma laneCfg_setup (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q q' : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g z : ℤ) (bt ut gt : ℤ → Option OblSymbol) (l r : List (Option OblSymbol)) :
    laneCfg (setupCfg W a base q p b u g bt ut gt) (Fin.natAdd W.k (0 : Fin 3)) q' z l r =
      setupCfg W a base q' p z u g (FinTM.sweepTape z l r) ut gt := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hn : j.castAdd 3 ≠ Fin.natAdd W.k (0 : Fin 3) := by
        intro he
        have hh := congrArg Fin.val he
        change j.val = W.k + 0 at hh
        have := j.isLt
        omega
      simp [laneCfg, setupCfg, hn]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [laneCfg, setupCfg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hn : j.castAdd 3 ≠ Fin.natAdd W.k (0 : Fin 3) := by
        intro he
        have hh := congrArg Fin.val he
        change j.val = W.k + 0 at hh
        have := j.isLt
        omega
      simp [laneCfg, setupCfg, hn]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [laneCfg, setupCfg]
  · rfl

/-- The full-width borrow pass acts on the actual captured-budget tape while
all other setup tapes and the parked native input remain fixed. -/
private lemma setupCfg_borrow (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (u g : ℤ) (w : List Bool) (ut gt : ℤ → Option OblSymbol)
    (carry : Bool) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.borrow carry)) p 1 u g (clockTape w) ut gt) w.length =
      setupCfg W a base (some (.borrow (budgetBorrow carry w).1)) p (1 + w.length) u g
        (clockTape (budgetBorrow carry w).2) ut gt := by
  have h := obliviousSchedule_borrow_run W a
    (setupCfg W a base (some (.borrow carry)) p 1 u g (clockTape w) ut gt)
    carry w 1 [some .origin] []
  rw [laneCfg_setup, laneCfg_setup] at h
  simp only [List.append_nil, ← clockTape_zipper] at h
  have he : (1 : ℤ) + w.length = 1 + (budgetBorrow carry w).2.length := by
    rw [budgetBorrow_length]
  rw [he, clockTape_zipper_end] at h
  simpa only [budgetBorrow_length] using h

/-- The blank after a full borrow selects either the next fixed-width pass
or the allocation stage, according only to the budget underflow flag. -/
private lemma setupCfg_borrow_end (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (u g : ℤ) (w : List Bool) (ut gt : ℤ → Option OblSymbol)
    (carry : Bool) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (.borrow carry)) p (w.length + 1) u g (clockTape w) ut gt) =
      setupCfg W a base (some (if carry then .unaryStart else .budgetStart)) p
        (w.length + 1) u g (clockTape w) ut gt := by
  have hr : (setupCfg W a base (some (.borrow carry)) p (w.length + 1) u g
      (clockTape w) ut gt).workTapeSymbols (Fin.natAdd W.k (0 : Fin 3)) = none := by
    simp [setupCfg, Cfg.workTapeSymbols, clockTape_end]
  change ((obliviousSchedule W a).tm.tr (.borrow carry) _ _).apply _ = _
  simp only [obliviousSchedule, hr]
  split <;> rw [setupCfg_apply] <;> simp_all [setupWrite]

/-- One complete controller round has a content-independent cost at the
captured word's fixed width: rewind, append a constant block, borrow, end test. -/
private lemma setupCfg_budget_round (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (g : ℤ) (w : List Bool) (gt : ℤ → Option OblSymbol) (N : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .budgetStart) p (w.length + 1) (N + 1) g
        (clockTape w) (unaryTape N) gt) (2 * w.length + (a + 1) + 4) =
      setupCfg W a base
        (some (if (budgetBorrow true w).1 then .unaryStart else .budgetStart)) p
        (w.length + 1) (N + (a + 1) + 1) g
        (clockTape (budgetBorrow true w).2) (unaryTape (N + (a + 1))) gt := by
  rw [show 2 * w.length + (a + 1) + 4 = (w.length + 2) + ((a + 2) + (w.length + 1)) by omega,
    MultiTapeTM.runFrom_add, setupCfg_budget_start, MultiTapeTM.runFrom_add, setupCfg_append,
    MultiTapeTM.runFrom_succ_eq_step', setupCfg_borrow]
  have h := setupCfg_borrow_end W a base p (N + (a + 1) + 1) g (budgetBorrow true w).2
    (unaryTape (N + (a + 1))) gt (budgetBorrow true w).1
  simpa only [budgetBorrow_length, add_comm (1 : ℤ)] using h

/-- The counter constructor executes exactly one round for each budget value
down to zero. Its final unary length is therefore `(a+1)(v+1)` plus the
previous prefix, with no width loss when the binary word acquires high zeros. -/
private lemma setupCfg_budget_all (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (g : ℤ) (gt : ℤ → Option OblSymbol) (v : ℕ) :
    ∀ (w : List Bool) (N : ℕ), budgetValue w = v →
      ∃ w' : List Bool, w'.length = w.length ∧
        (obliviousSchedule W a).tm.runFrom
          (setupCfg W a base (some .budgetStart) p (w.length + 1) (N + 1) g
            (clockTape w) (unaryTape N) gt)
          ((v + 1) * (2 * w.length + (a + 1) + 4)) =
          setupCfg W a base (some .unaryStart) p (w.length + 1)
            (N + (a + 1) * (v + 1) + 1) g
            (clockTape w') (unaryTape (N + (a + 1) * (v + 1))) gt := by
  induction v with
  | zero =>
    intro w N hv
    refine ⟨(budgetBorrow true w).2, budgetBorrow_length _ _, ?_⟩
    have hf := (budgetBorrow_underflow w).2 hv
    simpa only [Int.natCast_zero, zero_add, one_mul, Nat.mul_one, Int.natCast_one, mul_one, hf, if_true]
      using setupCfg_budget_round W a base p g w gt N
  | succ v ih =>
    intro w N hv
    have hpos : 0 < budgetValue w := by omega
    have hval : budgetValue (budgetBorrow true w).2 = v := by
      have := budgetBorrow_value w hpos
      omega
    have hf : (budgetBorrow true w).1 = false := by
      cases hh : (budgetBorrow true w).1
      · rfl
      · have := (budgetBorrow_underflow w).1 hh
        omega
    obtain ⟨w', hlen, hrun⟩ := ih (budgetBorrow true w).2 (N + (a + 1)) hval
    refine ⟨w', hlen.trans (budgetBorrow_length _ _), ?_⟩
    rw [show (v + 1 + 1) * (2 * w.length + (a + 1) + 4) =
        (2 * w.length + (a + 1) + 4) + (v + 1) * (2 * w.length + (a + 1) + 4) by ring,
      MultiTapeTM.runFrom_add, setupCfg_budget_round, hf]
    simp only [Bool.false_eq_true, ite_false]
    simp only [budgetBorrow_length, Nat.cast_add, Nat.cast_one] at hrun
    convert hrun using 1 <;> congr 1 <;> push_cast <;> ring

/-- Only the unary sentinel has the origin tag. -/
private lemma unaryTape_origin (N : ℕ) (z : ℤ) : unaryTape N z = some .origin ↔ z = 0 := by
  unfold unaryTape
  split_ifs <;> simp_all

/-- Every allocated unary marker is present, and the following cell is blank. -/
lemma unaryTape_unit (N j : ℕ) (hj : j < N) : unaryTape N ((j : ℤ) + 1) = some .unit := by
  simp [unaryTape, show (j : ℤ) + 1 ≠ 0 by omega, show (j : ℤ) + 1 ≤ N by omega]

/-- The fixed unary segment is terminated by a blank cell. -/
lemma unaryTape_end (N : ℕ) : unaryTape N ((N : ℤ) + 1) = none := by
  simp [unaryTape, show (N : ℤ) + 1 ≠ 0 by omega]

/-- Both unary rewinds use the same path; only their successor phase differs. -/
private def unaryRewindPhase {S : Type} {a : ℕ} (last : Bool) : OblPhase S a :=
  if last then .unaryReset else .unaryBack

/-- A unary rewind crosses exactly the prescribed number of cells and returns
to cell one. It does not inspect any simulated source data. -/
private lemma setupCfg_unary_rewind (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (N j : ℕ) (last : Bool) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (unaryRewindPhase last)) p b j g bt (unaryTape N) gt) (j + 1) =
      setupCfg W a base (some (if last then .startCenter else .layoutRight 0)) p b 1 g bt (unaryTape N) gt := by
  have step (j : ℕ) : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (unaryRewindPhase last)) p b j g bt (unaryTape N) gt) =
      if j = 0 then
        setupCfg W a base (some (if last then .startCenter else .layoutRight 0)) p b 1 g bt (unaryTape N) gt
      else setupCfg W a base (some (unaryRewindPhase last)) p b ((j : ℤ) - 1) g bt (unaryTape N) gt := by
    have hr : (setupCfg W a base (some (unaryRewindPhase last)) p b j g bt (unaryTape N) gt).workTapeSymbols
        (Fin.natAdd W.k (1 : Fin 3)) = unaryTape N j := by
      simp [setupCfg, Cfg.workTapeSymbols]
    change ((obliviousSchedule W a).tm.tr (unaryRewindPhase last) _ _).apply _ = _
    have h0 : unaryTape N j = some .origin ↔ j = 0 := by
      rw [unaryTape_origin, Int.natCast_eq_zero]
    cases last <;> simp only [unaryRewindPhase, Bool.false_eq_true, ite_false, ite_true] at hr ⊢
    all_goals
      simp only [obliviousSchedule, hr, h0]
      split <;> rw [setupCfg_apply] <;> simp_all [setupWrite, sub_eq_add_neg]
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step, if_pos rfl]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, step, if_neg (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using ih

/-- Allocation begins by rewinding the complete newly constructed unary segment. -/
private lemma setupCfg_unary_start (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (N : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .unaryStart) p b (N + 1) g bt (unaryTape N) gt) (N + 2) =
      setupCfg W a base (some (.layoutRight 0)) p b 1 g bt (unaryTape N) gt := by
  have hs : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .unaryStart) p b (N + 1) g bt (unaryTape N) gt) =
      setupCfg W a base (some (unaryRewindPhase false)) p b N g bt (unaryTape N) gt := by
    change ((obliviousSchedule W a).tm.tr .unaryStart _ _).apply _ = _
    simp only [obliviousSchedule]
    rw [setupCfg_apply]
    simp [setupWrite, unaryRewindPhase]
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, setupCfg_unary_rewind]
  rfl

/-- The guide's common interior mark, retaining its unique origin. -/
private def guideMark (z : ℤ) : OblSymbol := if z = 0 then .origin else .inside

/-- An allocation prefix overwrites the first `j` cells in the chosen direction.
Every overwritten cell receives a structural mark, independently of input bits. -/
private def guideFill (right : Bool) (gt : ℤ → Option OblSymbol) (j : ℕ) (z : ℤ) : Option OblSymbol :=
  if 0 ≤ (if right then z else -z) ∧ (if right then z else -z) < j
    then some (guideMark z) else gt z

/-- An empty allocation prefix leaves the copied guide unchanged. -/
private lemma guideFill_zero (right : Bool) (gt : ℤ → Option OblSymbol) : guideFill right gt 0 = gt := by
  funext z
  simp only [guideFill, Int.natCast_zero]
  rw [if_neg (by omega)]

/-- Allocating guide cells preserves uniqueness of the origin. -/
private lemma guideFill_origin (right : Bool) (gt : ℤ → Option OblSymbol)
    (hg : ∀ z, gt z = some .origin ↔ z = 0) (j : ℕ) (z : ℤ) :
    guideFill right gt j z = some .origin ↔ z = 0 := by
  unfold guideFill guideMark
  split_ifs <;> simp_all [hg]

/-- Each allocation write extends the prefix by exactly one cell. -/
private lemma guideFill_next (right : Bool) (gt : ℤ → Option OblSymbol) (j : ℕ) :
    Function.update (guideFill right gt j) (if right then (j : ℤ) else -(j : ℤ))
      (some (guideMark (if right then (j : ℤ) else -(j : ℤ)))) = guideFill right gt (j + 1) := by
  funext z
  by_cases hz : z = if right then (j : ℤ) else -(j : ℤ)
  · subst z
    cases right <;> simp [guideFill]
  · rw [Function.update_of_ne hz]
    cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hz ⊢
    all_goals
      unfold guideFill
      simp only [Bool.false_eq_true, ite_false, ite_true, Nat.cast_add, Nat.cast_one]
      split_ifs <;> first | rfl | omega

/-- The two outward allocation passes have symmetric finite phases. -/
private def layoutPhase {S : Type} {a : ℕ} (right : Bool) (i : Fin 3) : OblPhase S a :=
  if right then .layoutRight i else .layoutLeft i

/-- Allocation movement direction, independent of the cell contents. -/
private def layoutMove (right : Bool) : SignType := if right then .pos else .neg

/-- A single allocation step follows the fixed three-cell-per-marker controller. -/
private lemma setupCfg_layout_step (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol)
    (right : Bool) (i : Fin 3) (hu : ut u = some .unit)
    (hg : gt g = some .origin ↔ g = 0) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (layoutPhase right i)) p b u g bt ut gt) =
      setupCfg W a base (some (layoutPhase right (nextThird i))) p b
        (u + (if i.val = 2 then (1 : ℤ) else 0)) (g + (layoutMove right : ℤ)) bt ut
        (Function.update gt g (some (guideMark g))) := by
  have hu' : (setupCfg W a base (some (layoutPhase right i)) p b u g bt ut gt).workTapeSymbols
      (Fin.natAdd W.k (1 : Fin 3)) = ut u := by simp [setupCfg, Cfg.workTapeSymbols]
  have hg' : (setupCfg W a base (some (layoutPhase right i)) p b u g bt ut gt).workTapeSymbols
      (Fin.natAdd W.k (2 : Fin 3)) = gt g := by simp [setupCfg, Cfg.workTapeSymbols]
  change ((obliviousSchedule W a).tm.tr (layoutPhase right i) _ _).apply _ = _
  cases right <;> simp only [layoutPhase, Bool.false_eq_true, ite_false, ite_true] at hu' hg' ⊢
  all_goals
    simp only [obliviousSchedule, hu', hg', hu, hg, ite_true]
    rw [setupCfg_apply]
    simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, guideMark]
    by_cases hi : i.val = 2 <;> simp [layoutPhase, layoutMove, hi]

/-- A local allocation write advances the explicit filled-guide invariant. -/
private lemma setupCfg_layout_fill (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u : ℤ) (bt ut gt : ℤ → Option OblSymbol)
    (right : Bool) (i : Fin 3) (j : ℕ) (hu : ut u = some .unit)
    (hg : ∀ z, gt z = some .origin ↔ z = 0) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (layoutPhase right i)) p b u
        (if right then (j : ℤ) else -(j : ℤ)) bt ut (guideFill right gt j)) =
      setupCfg W a base (some (layoutPhase right (nextThird i))) p b
        (u + (if i.val = 2 then (1 : ℤ) else 0))
        (if right then ((j + 1 : ℕ) : ℤ) else -((j + 1 : ℕ) : ℤ)) bt ut (guideFill right gt (j + 1)) := by
  rw [setupCfg_layout_step W a base p b u _ bt ut _ right i hu (guideFill_origin right gt hg j _),
    guideFill_next]
  cases right <;> simp [layoutMove] <;> congr 1 <;> omega

/-- The finite allocation phase is the remainder modulo three of the number
of guide cells already written. -/
private lemma nextThird_mod (j : ℕ) :
    nextThird ⟨j % 3, Nat.mod_lt _ (by omega)⟩ =
      ⟨(j + 1) % 3, Nat.mod_lt _ (by omega)⟩ := by
  apply Fin.ext
  rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with h | h | h
  all_goals simp [nextThird, h] <;> omega

/-- Every prefix of an outward allocation pass has exact time equal to its
number of guide cells, with the unary head moving once every three cells. -/
private lemma setupCfg_layout_prefix (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt gt : ℤ → Option OblSymbol)
    (right : Bool) (B j : ℕ) (hj : j ≤ 3 * B)
    (hg : ∀ z, gt z = some .origin ↔ z = 0) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (layoutPhase right 0)) p b 1 0 bt (unaryTape B) gt) j =
      setupCfg W a base (some (layoutPhase right ⟨j % 3, Nat.mod_lt _ (by omega)⟩)) p b
        (((j / 3 : ℕ) : ℤ) + 1) (if right then (j : ℤ) else -(j : ℤ)) bt (unaryTape B) (guideFill right gt j) := by
  induction j with
  | zero => cases right <;> simp [guideFill_zero]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hu : unaryTape B ((j / 3 : ℕ) + 1) = some .unit := by
      have hh := unaryTape_unit B (j / 3) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using hh
    rw [setupCfg_layout_fill W a base p b _ bt (unaryTape B) gt right _ j hu hg, nextThird_mod]
    congr 1
    simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
    split <;> omega

/-- At the fixed end of an allocation pass, the blank unary cell causes one
final interior write and moves to the outer boundary marker. -/
private lemma setupCfg_layout_end (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (right : Bool) (B : ℕ) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (layoutPhase right 0)) p b (B + 1) g bt (unaryTape B) gt) =
      setupCfg W a base (some (if right then .rightEdge else .leftEdge)) p b (B + 1)
        (g + (layoutMove right : ℤ)) bt (unaryTape B) (Function.update gt g (some .inside)) := by
  have hu : (setupCfg W a base (some (layoutPhase right 0)) p b (B + 1) g bt (unaryTape B) gt).workTapeSymbols
      (Fin.natAdd W.k (1 : Fin 3)) = none := by
    simp [setupCfg, Cfg.workTapeSymbols, unaryTape_end]
  change ((obliviousSchedule W a).tm.tr (layoutPhase right 0) _ _).apply _ = _
  cases right <;> simp only [layoutPhase, Bool.false_eq_true, ite_false, ite_true] at hu ⊢
  all_goals
    simp only [obliviousSchedule, hu, reduceCtorEq, ite_false]
    rw [setupCfg_apply]
    simp [setupWrite, layoutMove]

/-- The positive half of the guide, with its right outer boundary installed. -/
private def rightGuide (R : ℕ) : ℤ → Option OblSymbol :=
  Function.update (copyGuide (R + 1)) ((R : ℤ) + 1) (some (.edge true))

/-- Extending the copied guide to a radius containing the input overwrites
exactly its positive prefix. -/
private lemma guideFill_right_copy (n R : ℕ) (hn : n + 1 ≤ R) :
    guideFill true (copyGuide (n + 1)) R = copyGuide R := by
  funext z
  simp only [guideFill, ite_true, guideMark, copyGuide, Nat.cast_add, Nat.cast_one]
  split_ifs <;> first | rfl | omega

/-- The right-boundary write cannot alter the origin. -/
private lemma rightGuide_origin (R : ℕ) (z : ℤ) : rightGuide R z = some .origin ↔ z = 0 := by
  by_cases hz : z = (R : ℤ) + 1
  · subst z
    simp [rightGuide, show (R : ℤ) + 1 ≠ 0 by omega]
  · rw [rightGuide, Function.update_of_ne hz, copyGuide_origin _ _ (Nat.succ_pos _)]

/-- Filling the negative half and marking its boundary produces the complete
fixed guide, including the original left input boundary inside the interval. -/
private lemma guideFill_left_finish (R : ℕ) (hR : 0 < R) :
    Function.update
      (Function.update (guideFill false (rightGuide R) R) (-(R : ℤ)) (some .inside))
      (-(R : ℤ) - 1) (some (.edge false)) = guideTape R := by
  funext z
  simp only [Function.update_apply, guideFill, Bool.false_eq_true, ite_false,
    rightGuide, copyGuide, guideMark, guideTape, Nat.cast_add, Nat.cast_one]
  split_ifs <;> first | rfl | omega

/-- The right-boundary transition starts a read-only return across the newly
allocated half, decrementing the unary counter once before that return. -/
private lemma setupCfg_right_edge (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (B R : ℕ) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .rightEdge) p b (B + 1) (R + 1) bt (unaryTape B) (copyGuide (R + 1))) =
      setupCfg W a base (some (.layoutReturn 0)) p b B R bt (unaryTape B) (rightGuide R) := by
  change ((obliviousSchedule W a).tm.tr .rightEdge _ _).apply _ = _
  simp only [obliviousSchedule]
  rw [setupCfg_apply]
  simp [setupWrite, rightGuide]

/-- A return-allocation step does not write any tape and moves the unary head
left once per three guide cells. -/
private lemma setupCfg_layout_return_step (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol)
    (i : Fin 3) (hu : ut u ≠ some .origin) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (.layoutReturn i)) p b u g bt ut gt) =
      setupCfg W a base (some (.layoutReturn (nextThird i))) p b
        (u - (if i.val = 2 then (1 : ℤ) else 0)) (g - 1) bt ut gt := by
  have hr : (setupCfg W a base (some (.layoutReturn i)) p b u g bt ut gt).workTapeSymbols
      (Fin.natAdd W.k (1 : Fin 3)) = ut u := by simp [setupCfg, Cfg.workTapeSymbols]
  change ((obliviousSchedule W a).tm.tr (.layoutReturn i) _ _).apply _ = _
  simp only [obliviousSchedule, hr, if_neg hu]
  rw [setupCfg_apply]
  by_cases hi : i.val = 2 <;> simp [setupWrite, hi, sub_eq_add_neg]

/-- Every prefix of the return allocation has its exact deterministic state
and head positions, with all guide marks unchanged. -/
private lemma setupCfg_layout_return_prefix (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt gt : ℤ → Option OblSymbol) (B j : ℕ) (hj : j ≤ 3 * B) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.layoutReturn 0)) p b B (3 * B) bt (unaryTape B) gt) j =
      setupCfg W a base (some (.layoutReturn ⟨j % 3, Nat.mod_lt _ (by omega)⟩)) p b
        ((B : ℤ) - ((j / 3 : ℕ) : ℤ)) (3 * (B : ℤ) - j) bt (unaryTape B) gt := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hu : unaryTape B ((B : ℤ) - ((j / 3 : ℕ) : ℤ)) ≠ some .origin := by
      intro hh
      have := (unaryTape_origin B _).1 hh
      omega
    rw [setupCfg_layout_return_step W a base p b _ _ bt (unaryTape B) gt _ hu, nextThird_mod]
    congr 1
    · simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
      split <;> omega
    · push_cast
      omega

/-- The completed return allocation reaches the origin and starts the left
allocation pass, restoring the unary counter to cell one. -/
private lemma setupCfg_layout_return (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt gt : ℤ → Option OblSymbol) (B : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.layoutReturn 0)) p b B (3 * B) bt (unaryTape B) gt) (3 * B + 1) =
      setupCfg W a base (some (.layoutLeft 0)) p b 1 0 bt (unaryTape B) gt := by
  rw [MultiTapeTM.runFrom_succ_eq_step', setupCfg_layout_return_prefix W a base p b bt gt B _ (le_refl _)]
  simp only [Nat.mul_mod_right, show 3 * B / 3 = B by omega,
    Nat.cast_mul, Nat.cast_ofNat, sub_self, Fin.mk_zero]
  have hr : (setupCfg W a base (some (.layoutReturn 0)) p b 0 0 bt (unaryTape B) gt).workTapeSymbols
      (Fin.natAdd W.k (1 : Fin 3)) = some .origin := by simp [setupCfg, Cfg.workTapeSymbols, unaryTape]
  change ((obliviousSchedule W a).tm.tr (.layoutReturn 0) _ _).apply _ = _
  simp only [obliviousSchedule, hr, ite_true]
  rw [setupCfg_apply]
  simp [setupWrite]

/-- The positive allocation pass reaches radius `3B`, installs its outer
boundary, and starts the read-only return in exactly `3B+2` transitions. -/
private lemma setupCfg_layout_right (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (n B : ℕ) (hn : n + 1 ≤ B) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.layoutRight 0)) p b 1 0 bt (unaryTape B) (copyGuide (n + 1)))
      (3 * B + 2) =
      setupCfg W a base (some (.layoutReturn 0)) p b B (3 * B) bt (unaryTape B) (rightGuide (3 * B)) := by
  have hprefix := setupCfg_layout_prefix W a base p b bt (copyGuide (n + 1)) true B (3 * B)
    (le_refl _) (fun z => copyGuide_origin _ z (Nat.succ_pos _))
  simp only [layoutPhase, ite_true, Nat.mul_mod_right, show 3 * B / 3 = B by omega,
    guideFill_right_copy n (3 * B) (by omega), Nat.cast_mul, Nat.cast_ofNat, Fin.mk_zero] at hprefix
  have hput := setupCfg_layout_end W a base p b (3 * B) bt (copyGuide (3 * B)) true B
  have he : Function.update (copyGuide (3 * B)) (3 * (B : ℤ)) (some .inside) = copyGuide (3 * B + 1) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, if_neg (show 3 * B ≠ 0 by omega)] using copyGuide_next (3 * B)
  simp only [layoutPhase, layoutMove, ite_true, SignType.cast, he] at hput
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', hprefix, hput]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using setupCfg_right_edge W a base p b bt B (3 * B)

/-- The negative allocation pass completes the fixed guide and leaves its
head at the left outer boundary, ready for the final unary rewind. -/
private lemma setupCfg_layout_left (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (B : ℕ) (hB : 0 < B) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.layoutLeft 0)) p b 1 0 bt (unaryTape B) (rightGuide (3 * B)))
      (3 * B + 2) =
      setupCfg W a base (some .unaryReset) p b B (-(3 * (B : ℤ)) - 1) bt (unaryTape B) (guideTape (3 * B)) := by
  have hprefix := setupCfg_layout_prefix W a base p b bt (rightGuide (3 * B)) false B (3 * B)
    (le_refl _) (rightGuide_origin (3 * B))
  simp only [layoutPhase, Bool.false_eq_true, ite_false, Nat.mul_mod_right,
    show 3 * B / 3 = B by omega, Nat.cast_mul, Nat.cast_ofNat, Fin.mk_zero] at hprefix
  have hput := setupCfg_layout_end W a base p b (-(3 * (B : ℤ))) bt
    (guideFill false (rightGuide (3 * B)) (3 * B)) false B
  simp only [layoutPhase, layoutMove, Bool.false_eq_true, ite_false, SignType.cast, ← sub_eq_add_neg] at hput
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', hprefix, hput]
  change ((obliviousSchedule W a).tm.tr .leftEdge _ _).apply _ = _
  simp only [obliviousSchedule]
  rw [setupCfg_apply]
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero]
  have hg := guideFill_left_finish (3 * B) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hg
  rw [hg]
  congr 1
  simp [SignType.cast]

/-- The final allocation scan reaches the origin in its coordinate distance,
then enters the macrostep controller in one additional transition. -/
private lemma setupCfg_start_center (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u : ℤ) (bt ut : ℤ → Option OblSymbol) (R j : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .startCenter) p b u (-(j : ℤ)) bt ut (guideTape R)) (j + 1) =
      setupCfg W a base (some .macroCheck) p b u 0 bt ut (guideTape R) := by
  have step (j : ℕ) : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .startCenter) p b u (-(j : ℤ)) bt ut (guideTape R)) =
      if j = 0 then setupCfg W a base (some .macroCheck) p b u 0 bt ut (guideTape R)
      else setupCfg W a base (some .startCenter) p b u (-(j : ℤ) + 1) bt ut (guideTape R) := by
    have hr : (setupCfg W a base (some .startCenter) p b u (-(j : ℤ)) bt ut (guideTape R)).workTapeSymbols
        (Fin.natAdd W.k (2 : Fin 3)) = guideTape R (-(j : ℤ)) := by
      simp [setupCfg, Cfg.workTapeSymbols]
    change ((obliviousSchedule W a).tm.tr .startCenter _ _).apply _ = _
    simp only [obliviousSchedule, hr, guideTape_origin, neg_eq_zero, Int.natCast_eq_zero]
    split <;> rw [setupCfg_apply] <;> simp_all [setupWrite]
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step, if_pos rfl]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, step, if_neg (by omega)]
    rw [show -((j + 1 : ℕ) : ℤ) + 1 = -(j : ℤ) by omega]
    exact ih

/-- **Complete allocation ledger.** Starting with the copied guide and a unary
budget of `B`, exactly `14B+10` transitions produce the radius-`3B` guide and
position the unary and guide heads for the first macrostep. -/
private lemma setupCfg_allocation (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (n B : ℕ) (hn : n + 1 ≤ B) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .unaryStart) p b (B + 1) 0 bt (unaryTape B) (copyGuide (n + 1)))
      (14 * B + 10) =
      setupCfg W a base (some .macroCheck) p b 1 0 bt (unaryTape B) (guideTape (3 * B)) := by
  have hc := setupCfg_start_center W a base p b 1 bt (unaryTape B) (3 * B) (3 * B + 1)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, neg_add_rev] at hc
  have hc' : (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .startCenter) p b 1 (-(3 * (B : ℤ)) - 1) bt (unaryTape B) (guideTape (3 * B)))
      (3 * B + 2) =
      setupCfg W a base (some .macroCheck) p b 1 0 bt (unaryTape B) (guideTape (3 * B)) := by
    rw [show -(1 : ℤ) + -(3 * (B : ℤ)) = -(3 * (B : ℤ)) - 1 by omega] at hc
    exact hc
  rw [show 14 * B + 10 = (B + 2) + ((3 * B + 2) + ((3 * B + 1) +
      ((3 * B + 2) + ((B + 1) + (3 * B + 2))))) by omega,
    MultiTapeTM.runFrom_add, setupCfg_unary_start, MultiTapeTM.runFrom_add,
    setupCfg_layout_right W a base p b bt n B hn, MultiTapeTM.runFrom_add,
    setupCfg_layout_return, MultiTapeTM.runFrom_add, setupCfg_layout_left W a base p b bt B (by omega),
    MultiTapeTM.runFrom_add]
  have hr := setupCfg_unary_rewind W a base p b (-(3 * (B : ℤ)) - 1) bt (guideTape (3 * B)) B B true
  simp only [unaryRewindPhase, ite_true] at hr
  rw [hr, hc']

/-- The full input-copy schedule includes both virtual boundary cells and the
return to the origin. Its exact cost is `2n+4`; the native input then stays parked. -/
private lemma setupCfg_copy (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (b u : ℤ) (bt ut : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .copyLeft) ⟨1, by omega⟩ b u 0 bt ut (fun _ => none))
      (2 * x.length + 4) =
      setupCfg W a base (some .budgetStart) ⟨x.length + 1, by omega⟩ b u 0 bt ut (copyGuide (x.length + 1)) := by
  have hscan := congrArg (obliviousSchedule W a).tm.step
    (setupCfg_copy_prefix W a base b u bt ut x.length (le_refl _))
  rw [← MultiTapeTM.runFrom_succ_eq_step', setupCfg_copy_end] at hscan
  rw [show 2 * x.length + 4 = 2 + ((x.length + 1) + (x.length + 1)) by omega,
    MultiTapeTM.runFrom_add, setupCfg_copy_left, MultiTapeTM.runFrom_add,
    hscan, setupCfg_copy_return]

/-- The empty binary capture and empty unary budget share the initial sentinel. -/
private lemma clockTape_unary_zero : clockTape [] = unaryTape 0 := by
  funext z
  simp only [clockTape, FinTM.bufferTape_nil, Option.map_none, unaryTape, Int.natCast_zero]
  split_ifs <;> first | rfl | omega

/-- A halted captured clock configuration has the exact setup representation. -/
lemma clockStageCfg_setup (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) (hs : c.state = none) :
    clockStageCfg W a c = setupCfg W a (clockStageCfg W a c) (some .resetStart)
      (clockStageCfg W a c).inputPos (c.output.length + 1) 1 0
      (clockTape c.output) (unaryTape 0) (fun _ => none) := by
  apply Cfg.ext
  · simp [clockStageCfg, setupCfg, hs]
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [clockStageCfg, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [clockStageCfg, setupCfg, clockTape_unary_zero]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [clockStageCfg, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [clockStageCfg, setupCfg]
  · rfl

/-- Changing only the macrostep phase and two heads preserves a completed
setup configuration's explicit tape representation. -/
private lemma macroCfg_setup (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q q' : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g u' g' : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    macroCfg W a (setupCfg W a base q p b u g bt ut gt) q' u' g' =
      setupCfg W a base q' p b u' g' bt ut gt := by
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [macroCfg, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [macroCfg, setupCfg]
  · rfl

/-- The completely allocated setup executes precisely its unary budget and
then halts at the fixed final counter test. -/
lemma setupCfg_finish (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (B : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .macroCheck) p b 1 0 bt (unaryTape B) (guideTape (3 * B)))
      (B * (6 * (3 * B) + 8) + 1) =
      setupCfg W a base none p b (B + 1) 0 bt (unaryTape B) (guideTape (3 * B)) := by
  have h := macroCfg_finish W a
    (setupCfg W a base (some .macroCheck) p b 1 0 bt (unaryTape B) (guideTape (3 * B))) (3 * B) B
    (by simp [setupCfg])
    (fun j hj => by simpa [setupCfg] using unaryTape_unit B j hj)
    (by simpa [setupCfg] using unaryTape_end B)
  simpa only [macroCfg_setup] using h

/-- Initialization connects the arbitrary clock endpoint to the completely
allocated macrostep configuration. The binary counter retains its full width. -/
lemma setupCfg_initializes (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (w : List Bool) (v : ℕ) (hv : budgetValue w = v)
    (hn : x.length + 1 ≤ (a + 1) * (v + 1)) :
    ∃ w', w'.length = w.length ∧
      (obliviousSchedule W a).tm.runFrom
        (setupCfg W a base (some .resetStart) p (w.length + 1) 1 0
          (clockTape w) (unaryTape 0) (fun _ => none))
        ((p.val - 1 + 2) + ((2 * x.length + 4) +
          ((v + 1) * (2 * w.length + (a + 1) + 4) + (14 * ((a + 1) * (v + 1)) + 10)))) =
        setupCfg W a base (some .macroCheck) ⟨x.length + 1, by omega⟩ (w.length + 1) 1 0
          (clockTape w') (unaryTape ((a + 1) * (v + 1))) (guideTape (3 * ((a + 1) * (v + 1)))) := by
  obtain ⟨w', hlen, hcounter⟩ := setupCfg_budget_all W a base ⟨x.length + 1, by omega⟩
    0 (copyGuide (x.length + 1)) v w 0 hv
  refine ⟨w', hlen, ?_⟩
  simp only [Nat.cast_zero, zero_add] at hcounter
  rw [MultiTapeTM.runFrom_add, setupCfg_reset, MultiTapeTM.runFrom_add, setupCfg_copy,
    MultiTapeTM.runFrom_add, hcounter]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    setupCfg_allocation W a base ⟨x.length + 1, by omega⟩ (w.length + 1) (clockTape w')
      x.length ((a + 1) * (v + 1)) hn

end Complexity
