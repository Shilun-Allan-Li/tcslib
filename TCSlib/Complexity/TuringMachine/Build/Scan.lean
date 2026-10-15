/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: constant writers and native-input sweeps (§12.8)

The single-sweep rows of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a) that touch no G1-owned file: two writers
of a fixed word (R8.4, R8.4′) and two sweeps of the native input (R8.5a,
R8.5d). They are alphabet-generic, like the G1 catalog, and they are stated in
the §12.6 framed form: exact time, finish configuration, no earlier exit, and
the trajectory of every head, from an arbitrary configuration.

**Status: proved.** The four framed contracts are proved. The constant writer
and both native-input sweeps instantiate the public catalog trace; the cyclic
advancing writer uses one forward induction.

## Design

* **Two writers.** `Turing.writeConstTM` writes its word and returns the head,
  so it composes under `Turing.seamCompTM` like the R3 sweeps. The advancing
  writer `Turing.writeAdvTM` leaves the head after the word and returns to its
  own start state, which is the round shape of `Turing.counterLoopTM`; it is
  the round of `Turing.expandTM` (R8.6). A seam consumer that calls it once
  uses `Turing.seamReleaseTM`.
* **Tables** are written with the catalog's one-tape actions
  `Turing.tapeAction` and `Turing.inputMoveAction`.
* **The input sweeps** move the native input head and return it to position
  `1`. `Turing.inputCopyTM` moves the destination work head in lockstep with
  it; `Turing.inputFoldTM` moves only the input head, so its work heads stay
  fixed. `Turing.inputCopyTM` reuses the sweep
  alphabet `Turing.SweepPhase` and `Turing.inputFoldTM` the scan alphabet
  `Turing.ScanPhase`, so no phase type is duplicated.
* **The input fold is the validator** of design §12.8a §0: a rich
  space-bounded simulator folds its input through `decodeBool`'s domain first
  and stops on a foreign symbol, because `alphabet_reduction_spaceUsed` bounds
  space over all rich inputs (decision O6).

## Main definitions

* `Turing.WritePhase`, `Turing.writeConstTM` — write a fixed word and return.
* `Turing.writeAdvTM` — write a fixed word and leave the head after it.
* `Turing.inputCopyTM` — copy the native input onto a work tape.
* `Turing.inputFoldTM` — fold the native input with a finite-state update.

## Main results

* `Turing.writeConstTM_run_ofCfg`, `Turing.writeAdvTM_run_ofCfg`,
  `Turing.inputCopyTM_run_ofCfg`, `Turing.inputFoldTM_run_ofCfg` — the framed
  contracts (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape model with a read-only
  input tape; the routines are folklore subroutines of the textbook's
  simulations. §4.1: the space measure that makes input validation necessary
  for the rich simulators.)
-/

namespace Turing

/-- A partially written word, with its arbitrary exterior frame preserved. The three
writing rows share this family; `r` counts written cells, `q` is the control state,
and `p` is the native-input position. -/
private def scanWriteCfg {Symbol S : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (w : List Symbol) (d : Cfg k Symbol S x) (q : S)
    (p : Fin (x.length + 2)) (r : ℕ) : Cfg k Symbol S x :=
  { d with state := some q
           inputPos := p
           workTapes := fun j z =>
             if j = i ∧ d.workTapePos j ≤ z ∧ z < d.workTapePos j + (r : ℤ)
               then FinTM.bufferTape w (z - d.workTapePos j) else d.workTapes j z
           workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) else 0 }

/-- Writing the next symbol and moving right extends the shared written prefix.

**Proof sketch.** Cite the public writing-step equation. On the selected tape,
`catalog_write_take` extends the overwrite interval by one cell; all other tapes
are fixed, and the selected head advances by one. -/
private theorem scan_write_step {Symbol S : Type*} {k : ℕ} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (i : Fin k) (w : List Symbol) (d : Cfg k Symbol S x)
    (q q' : S) (p : Fin (x.length + 2)) (inp : SignType) (r : ℕ) (hr : r < w.length)
    (htr : M.tr q (scanWriteCfg i w d q p r).inputSymbol
        (scanWriteCfg i w d q p r).workTapeSymbols =
      tapeAction i inp (some (some w[r])) .pos q') :
    M.step (scanWriteCfg i w d q p r) =
      scanWriteCfg i w d q' (moveInputPos p inp) (r + 1) := by
  rw [step_of_tapeAction_write M _ i inp _ .pos rfl htr]
  apply Cfg.ext
  case workTapes =>
    funext j
    by_cases hj : j = i
    · subst j
      simpa [scanWriteCfg] using catalog_write_take (d.workTapes i) (d.workTapePos i) w r hr
    · simp [scanWriteCfg, hj]
  case workTapePos =>
    funext j
    by_cases hj : j = i <;>
      simp [scanWriteCfg, hj, Function.update_apply, SignType.cast] <;> omega
  all_goals simp [scanWriteCfg]

/-! ### R8.4 — the constant writer -/

/-- **Phase alphabet of the constant writer** (design §12.8a, R8.4), for a word
of length `n`: writing cell `j`, walking back with `j` cells to go, and the
live exit anchor. -/
inductive WritePhase (n : ℕ) where
  /-- writing cell `j` of the word -/
  | wr (j : Fin (n + 1))
  /-- walking back, `j` cells from the origin -/
  | bk (j : Fin (n + 1))
  /-- the live exit anchor -/
  | done
deriving DecidableEq, Fintype

/-- **R8.4, the constant writer** (design §12.8a). Write the fixed word `w₀` on
tape `i` from its head, moving right, then walk back `|w₀|` cells and enter the
live `done` anchor with the head where it started. The old contents of the
tape are never read. -/
def writeConstTM {Symbol : Type*} (k : ℕ) (i : Fin k) (w₀ : List Symbol) :
    MultiTapeTM k Symbol (WritePhase w₀.length) where
  q₀ := .wr 0
  tr := fun q _ _ =>
    match q with
    | .wr j =>
      if h : (j : ℕ) < w₀.length then
        tapeAction i 0 (some (some w₀[(j : ℕ)])) .pos (.wr ⟨j + 1, by omega⟩)
      else inputMoveAction 0 (.bk ⟨w₀.length, by omega⟩)
    | .bk j =>
      if (j : ℕ) = 0 then inputMoveAction 0 .done
      else tapeAction i 0 none .neg (.bk ⟨j - 1, by omega⟩)
    | .done => inputMoveAction 0 .done

/-- The constant writer after `r` forward steps, with a total finite-state index. -/
private def scanConstF {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (w : List Symbol) (d : Cfg k Symbol (WritePhase w.length) x) (r : ℕ) :
    Cfg k Symbol (WritePhase w.length) x :=
  scanWriteCfg i w d (.wr ⟨min r w.length, by omega⟩) d.inputPos r

/-- The constant writer's return configuration, `r` cells to the right of entry. -/
private def scanConstR {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (w : List Symbol) (d : Cfg k Symbol (WritePhase w.length) x) (r : ℕ) :
    Cfg k Symbol (WritePhase w.length) x :=
  { scanWriteCfg i w d (.bk ⟨min r w.length, by omega⟩) d.inputPos w.length with
      workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) else 0 }

/-- The constant writer's exit, with the entire word written and all heads restored. -/
private def scanConstD {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (w : List Symbol) (d : Cfg k Symbol (WritePhase w.length) x) :
    Cfg k Symbol (WritePhase w.length) x :=
  { d with state := some .done
           workTapes := (scanConstF i w d w.length).workTapes }

/-- The constant writer instantiates the public two-pass trace.

**Proof sketch.** The shared write step supplies the forward equations. A stationary
turn enters the return family; left moves count down to zero; a stationary entry
reaches the fixed exit. The public trace theorem supplies the whole run. -/
private theorem scan_const_trace {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (w : List Symbol) (d : Cfg k Symbol (WritePhase w.length) x)
    (hstate : d.state = some (.wr 0)) (t : ℕ) :
    (writeConstTM k i w).runFrom d t =
      catalogTrace (scanConstF i w d) (scanConstR i w d) (scanConstD i w d) w.length t := by
  have h0 : scanConstF i w d 0 = d := by
    apply Cfg.ext
    case workTapes => funext j z; simp [scanConstF, scanWriteCfg]
    all_goals simp [scanConstF, scanWriteCfg, hstate]
  conv_lhs => rw [← h0]
  apply catalog_trace_run
  · intro r hr
    unfold scanConstF
    simpa only [moveInputPos_zero] using
      scan_write_step (writeConstTM k i w) i w d (.wr ⟨min r w.length, by omega⟩)
        (.wr ⟨min (r + 1) w.length, by omega⟩) d.inputPos 0 r hr (by
          simp only [writeConstTM]
          rw [dif_pos (show min r w.length < w.length by omega)]
          simp only [show min r w.length = r by omega]
          congr 2
          apply Fin.ext
          simp
          omega)
  · rw [step_of_inputMoveAction _ _ 0 rfl
      (q' := .bk ⟨min w.length w.length, by omega⟩) (by
        simp only [writeConstTM]
        rw [dif_neg (show ¬ min w.length w.length < w.length by omega)]
        simp)]
    apply Cfg.ext <;> simp [scanConstF, scanConstR, scanWriteCfg]
  · intro r hr
    rw [step_of_tapeAction_move _ _ i 0 .neg rfl
      (q' := .bk ⟨min r w.length, by omega⟩) (by
        simp only [writeConstTM]
        rw [if_neg (show ¬ min (r + 1) w.length = 0 by omega)]
        congr 2
        apply Fin.ext
        simp
        omega)]
    apply Cfg.ext
    case workTapePos =>
      funext j
      by_cases hj : j = i <;>
        simp [scanConstR, scanWriteCfg, hj, Function.update_apply] <;> omega
    all_goals simp [scanConstR, scanWriteCfg]
  · rw [step_of_inputMoveAction _ _ 0 rfl (q' := .done) (by simp [writeConstTM])]
    apply Cfg.ext <;> simp [scanConstR, scanConstD, scanConstF, scanWriteCfg]
  · rw [step_of_inputMoveAction _ _ 0 rfl (q' := .done) rfl]
    simp [scanConstD]

/-- **R8.4, the constant writer, framed** (design §12.8a). From any
configuration at the writer's start phase, the writer reaches `done` at
exactly `2|w₀| + 2` and not earlier. At that point the interval
`[pos, pos + |w₀|)` of tape `i` holds `w₀`, whatever it held before, and every
other cell, the head positions, the input position and the output are
unchanged. Up to the exit the head of tape `i` stays within
`[pos, pos + |w₀|]`, and every other head is fixed.

**Proof sketch.** Induct on the cells written: `|w₀|` steps write `w₀` moving
right. One stationary step turns into the walk back, `|w₀|` steps return the
head to `pos`, and one stationary step enters `done`. No step reads a work
cell, so the old contents are irrelevant. -/
theorem writeConstTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (w₀ : List Symbol) (d : Cfg k Symbol (WritePhase w₀.length) x)
    (hstate : d.state = some (.wr 0)) :
    (writeConstTM k i w₀).runFrom d (2 * w₀.length + 2) =
        { d with
          state := some .done
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w₀.length : ℤ)
              then FinTM.bufferTape w₀ (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w₀.length + 2, ((writeConstTM k i w₀).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w₀.length + 2 →
        if j = i then
          ((writeConstTM k i w₀).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j) (d.workTapePos j + (w₀.length : ℤ))
        else ((writeConstTM k i w₀).runFrom d t).workTapePos j = d.workTapePos j) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [scan_const_trace i w₀ d hstate]
    simp [catalogTrace, scanConstD, scanConstF, scanWriteCfg,
      show ¬2 * w₀.length + 2 ≤ w₀.length by omega]
  · intro t ht
    rw [scan_const_trace i w₀ d hstate]
    simp only [catalogTrace]
    split_ifs <;> simp [scanConstF, scanConstR, scanConstD, scanWriteCfg] <;> omega
  · intro j t ht
    rw [scan_const_trace i w₀ d hstate]
    simp only [catalogTrace]
    split_ifs <;>
      simp_all [scanConstF, scanConstR, scanConstD, scanWriteCfg, Finset.mem_Icc] <;> omega

/-! ### R8.4′ — the advancing writer -/

/-- **R8.4′, the advancing writer** (design §12.8a). Write the fixed word `w₀`
on tape `i` from its head, moving right, and return to the start state `0` with
the head just after the word. The state `j` is the number of cells written. The
writer is cyclic: started again, it writes `w₀` again after the first copy,
which makes it a round body of `Turing.counterLoopTM` with anchor `0`. -/
def writeAdvTM {Symbol : Type*} (k : ℕ) (i : Fin k) (w₀ : List Symbol) :
    MultiTapeTM k Symbol (Fin (w₀.length + 1)) where
  q₀ := 0
  tr := fun j _ _ =>
    if h : (j : ℕ) < w₀.length then
      tapeAction i 0 (some (some w₀[(j : ℕ)])) .pos ⟨j + 1, by omega⟩
    else inputMoveAction 0 0

/-- The advancing writer after `r` writes; its finite state counts the written cells. -/
private def scanAdvF {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (w : List Symbol) (d : Cfg k Symbol (Fin (w.length + 1)) x) (r : ℕ) :
    Cfg k Symbol (Fin (w.length + 1)) x :=
  scanWriteCfg i w d ⟨min r w.length, by omega⟩ d.inputPos r

/-- Up to the word length, the advancing writer follows the shared write family.

**Proof sketch.** Induct on the number of written cells, invoking `scan_write_step`
at each successor. This is a single forward induction: the cyclic exit is not
stationary, so the two-pass trace theorem does not apply. -/
private theorem scan_adv_run {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (w : List Symbol) (d : Cfg k Symbol (Fin (w.length + 1)) x)
    (hstate : d.state = some 0) :
    ∀ r ≤ w.length, (writeAdvTM k i w).runFrom d r = scanAdvF i w d r := by
  intro r hr
  induction r with
  | zero =>
    apply Cfg.ext
    case workTapes => funext j z; simp [scanAdvF, scanWriteCfg]
    all_goals simp [scanAdvF, scanWriteCfg, hstate]
  | succ r ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold scanAdvF
    simpa only [moveInputPos_zero] using
      scan_write_step (writeAdvTM k i w) i w d ⟨min r w.length, by omega⟩
        ⟨min (r + 1) w.length, by omega⟩ d.inputPos 0 r (by omega) (by
          simp only [writeAdvTM]
          rw [dif_pos (show min r w.length < w.length by omega)]
          simp only [show min r w.length = r by omega]
          congr 1
          apply Fin.ext
          simp
          omega)

/-- **R8.4′, the advancing writer, framed** (design §12.8a). From any
configuration at state `0`, the writer returns to state `0` at exactly
`|w₀| + 1`, and its states strictly between are not `0`. At that point the
interval `[pos, pos + |w₀|)` of tape `i` holds `w₀`, whatever it held before,
the head of tape `i` is at `pos + |w₀|`, and every other cell, every other
head, the input position and the output are unchanged. Up to the return the
head of tape `i` stays within `[pos, pos + |w₀|]`, and every other head is
fixed. These are exactly the round hypotheses of `Turing.counterLoopTM_run_done`
with round time `|w₀| + 1`.

**Proof sketch.** Induct on the cells written: the state after `j ≤ |w₀|` steps
is `j`, which is nonzero for `0 < j`, with `j` cells of `w₀` written and the
head at `pos + j`. The last step is stationary and returns to `0`. No step
reads a work cell. -/
theorem writeAdvTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (w₀ : List Symbol) (d : Cfg k Symbol (Fin (w₀.length + 1)) x)
    (hstate : d.state = some 0) :
    (writeAdvTM k i w₀).runFrom d (w₀.length + 1) =
        { d with
          state := some 0
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w₀.length : ℤ)
              then FinTM.bufferTape w₀ (q - d.workTapePos j)
            else d.workTapes j q
          workTapePos := Function.update d.workTapePos i
            (d.workTapePos i + (w₀.length : ℤ)) } ∧
      (∀ t, 0 < t → t < w₀.length + 1 → ((writeAdvTM k i w₀).runFrom d t).state ≠ some 0) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ w₀.length + 1 →
        if j = i then
          ((writeAdvTM k i w₀).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j) (d.workTapePos j + (w₀.length : ℤ))
        else ((writeAdvTM k i w₀).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hlast : (writeAdvTM k i w₀).runFrom d (w₀.length + 1) =
      { scanAdvF i w₀ d w₀.length with state := some 0 } := by
    rw [MultiTapeTM.runFrom_succ_eq_step', scan_adv_run i w₀ d hstate _ le_rfl]
    rw [step_of_inputMoveAction _ _ 0 rfl (q' := 0) (by
      simp only [writeAdvTM]
      rw [dif_neg (show ¬ min w₀.length w₀.length < w₀.length by omega)])]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hlast]
    apply Cfg.ext
    case workTapePos =>
      funext j
      by_cases hj : j = i
      · subst j; simp [scanAdvF, scanWriteCfg]
      · simp [scanAdvF, scanWriteCfg, hj]
    all_goals simp [scanAdvF, scanWriteCfg]
  · intro t ht0 ht
    rw [scan_adv_run i w₀ d hstate t (by omega)]
    simp only [scanAdvF, scanWriteCfg, ne_eq, Option.some.injEq, Fin.ext_iff, Fin.val_zero]
    omega
  · intro j t ht
    rcases Nat.lt_or_ge t (w₀.length + 1) with h | h
    · rw [scan_adv_run i w₀ d hstate t (by omega)]
      split_ifs with hj <;> simp [scanAdvF, scanWriteCfg, hj, Finset.mem_Icc] <;> omega
    · rw [show t = w₀.length + 1 by omega, hlast]
      split_ifs with hj <;> simp [scanAdvF, scanWriteCfg, hj, Finset.mem_Icc]

/-! ### R8.5a — the input copier -/

/-- **R8.5a, the input copier** (design §12.8a). Copy the native input onto
tape `i` from its head, the two heads moving right in lockstep, then walk both
heads back together, guided by the input tape's left end marker. The phases are
the sweep alphabet's: `sweep` copies, `rewind` returns, and `done` is the live
exit anchor. The destination needs no left delimiter. -/
def inputCopyTM {Symbol : Type*} (k : ℕ) (i : Fin k) : MultiTapeTM k Symbol SweepPhase where
  q₀ := .sweep
  tr := fun q inp _ =>
    match q with
    | .sweep =>
      match inp with
      | some s => tapeAction i 1 (some (some s)) .pos .sweep
      | none => tapeAction i (-1) none .neg .rewind
    | .rewind =>
      match inp with
      | some _ => tapeAction i (-1) none .neg .rewind
      | none => tapeAction i 1 none .pos .done
    | .done => inputMoveAction 0 .done

/-- The copier after `r` forward steps, with the input and destination heads advanced. -/
private def scanCopyF {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (d : Cfg k Symbol SweepPhase x) (r : ℕ) : Cfg k Symbol SweepPhase x :=
  scanWriteCfg i x d .sweep ⟨min r x.length + 1, by omega⟩ r

/-- The copier's return family, indexed by native-input position down to zero. -/
private def scanCopyR {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (d : Cfg k Symbol SweepPhase x) (r : ℕ) : Cfg k Symbol SweepPhase x :=
  { scanWriteCfg i x d .rewind ⟨min r x.length, by omega⟩ x.length with
      workTapePos := fun j => d.workTapePos j + if j = i then (r : ℤ) - 1 else 0 }

/-- The copier's exit restores both heads while retaining the copied input. -/
private def scanCopyD {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (d : Cfg k Symbol SweepPhase x) : Cfg k Symbol SweepPhase x :=
  { d with state := some .done
           workTapes := (scanCopyF i d x.length).workTapes }

/-- The native-input copier instantiates the public two-pass trace.

**Proof sketch.** Interior input reads supply the symbols for the shared write
step. The right marker turns both heads left, interior reads guide the return,
and the left marker moves both heads right into the fixed exit. No destination
delimiter is used. Apply the public trace theorem to these five equations. -/
private theorem scan_copy_trace {Symbol : Type*} {k : ℕ} {x : List Symbol}
    (i : Fin k) (d : Cfg k Symbol SweepPhase x)
    (hstate : d.state = some .sweep) (hin : d.inputPos = 1) (t : ℕ) :
    (inputCopyTM k i).runFrom d t =
      catalogTrace (scanCopyF i d) (scanCopyR i d) (scanCopyD i d) x.length t := by
  have h0 : scanCopyF i d 0 = d := by
    apply Cfg.ext
    case inputPos => rw [hin]; apply Fin.ext; simp [scanCopyF, scanWriteCfg]
    case workTapes => funext j z; simp [scanCopyF, scanWriteCfg]
    all_goals simp [scanCopyF, scanWriteCfg, hstate]
  conv_lhs => rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hs : (scanCopyF i d r).inputSymbol = some x[r] :=
      inputSymbolInner r (by simp [scanCopyF, scanWriteCfg]; omega) hr
    unfold scanCopyF
    rw [scan_write_step (inputCopyTM k i) i x d .sweep .sweep _ 1 r hr
      (by
        change (inputCopyTM k i).tr .sweep (scanCopyF i d r).inputSymbol
          (scanCopyF i d r).workTapeSymbols = _
        simp only [inputCopyTM, hs])]
    congr 1
    rw [← SignType.pos_eq_one, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    simp
    omega
  · have hs : (scanCopyF i d x.length).inputSymbol = none := by
      simp [Cfg.inputSymbol, scanCopyF, scanWriteCfg]
    rw [step_of_tapeAction_move _ _ i (-1) .neg rfl (q' := .rewind)
      (by simp only [inputCopyTM, hs])]
    apply Cfg.ext
    case inputPos =>
      simp only [scanCopyF, scanCopyR, scanWriteCfg]
      apply Fin.ext
      rw [← SignType.neg_eq_neg_one, FinTM.moveInputPos_neg_val]
      simp
    case workTapePos =>
      funext j
      by_cases hj : j = i <;>
        simp [scanCopyF, scanCopyR, scanWriteCfg, hj, Function.update_apply] <;> omega
    all_goals simp [scanCopyF, scanCopyR, scanWriteCfg]
  · intro r hr
    have hs : (scanCopyR i d (r + 1)).inputSymbol = some x[r] :=
      inputSymbolInner r (by simp [scanCopyR, scanWriteCfg]; omega) hr
    rw [step_of_tapeAction_move _ _ i (-1) .neg rfl (q' := .rewind)
      (by simp only [inputCopyTM, hs])]
    apply Cfg.ext
    case inputPos =>
      simp only [scanCopyR, scanWriteCfg]
      apply Fin.ext
      rw [← SignType.neg_eq_neg_one, FinTM.moveInputPos_neg_val]
      simp
      omega
    case workTapePos =>
      funext j
      by_cases hj : j = i <;>
        simp [scanCopyR, scanWriteCfg, hj, Function.update_apply] <;> omega
    all_goals simp [scanCopyR, scanWriteCfg]
  · have hs : (scanCopyR i d 0).inputSymbol = none := by
      simp [Cfg.inputSymbol, scanCopyR, scanWriteCfg]
    rw [step_of_tapeAction_move _ _ i 1 .pos rfl (q' := .done)
      (by simp only [inputCopyTM, hs])]
    apply Cfg.ext
    case inputPos =>
      simp only [scanCopyR, scanCopyD, scanWriteCfg, hin]
      rw [← SignType.pos_eq_one, moveInputPos_pos_of_ne_right _ (by simp)]
      apply Fin.ext
      simp
    case workTapePos =>
      funext j
      by_cases hj : j = i <;>
        simp [scanCopyR, scanCopyD, scanWriteCfg, hj, Function.update_apply]
    all_goals simp [scanCopyR, scanCopyD, scanCopyF, scanWriteCfg]
  · rw [step_of_inputMoveAction _ _ 0 rfl (q' := .done) rfl]
    simp [scanCopyD]

/-- **R8.5a, the input copier, framed** (design §12.8a). From any configuration
in the copy phase with the input head at position `1`, the copier reaches
`done` at exactly `2|x| + 2` and not earlier, where `x` is the native input. At
that point the interval `[pos, pos + |x|)` of tape `i` holds `x`, whatever it
held before, and every other cell, every head, the input position and the
output are unchanged. Up to the exit the head of tape `i` stays within
`[pos - 1, pos + |x|]`, and every other head is fixed.

**Proof sketch.** Induct on the input cells: `|x|` lockstep steps copy `x`,
and the input's right end marker turns both heads left. The return takes `|x|`
lockstep steps over the input, and the left end marker supplies the entry step,
which puts the input head back at `1` and the work head back at `pos`. -/
theorem inputCopyTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (d : Cfg k Symbol SweepPhase x) (hstate : d.state = some .sweep) (hin : d.inputPos = 1) :
    (inputCopyTM k i).runFrom d (2 * x.length + 2) =
        { d with
          state := some .done
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (x.length : ℤ)
              then FinTM.bufferTape x (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * x.length + 2, ((inputCopyTM k i).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * x.length + 2 →
        if j = i then
          ((inputCopyTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (x.length : ℤ))
        else ((inputCopyTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [scan_copy_trace i d hstate hin]
    simp [catalogTrace, scanCopyD, scanCopyF, scanWriteCfg,
      show ¬2 * x.length + 2 ≤ x.length by omega]
  · intro t ht
    rw [scan_copy_trace i d hstate hin]
    simp only [catalogTrace]
    split_ifs <;> simp [scanCopyF, scanCopyR, scanCopyD, scanWriteCfg] <;> omega
  · intro j t ht
    rw [scan_copy_trace i d hstate hin]
    simp only [catalogTrace]
    split_ifs <;>
      simp_all [scanCopyF, scanCopyR, scanCopyD, scanWriteCfg, Finset.mem_Icc] <;> omega

/-! ### R8.5d — the input fold -/

/-- **R8.5d, the input fold** (design §12.8a). Read the native input left to
right, updating a finite state by `δ` from `a₀`, then walk the input head back
and enter the live anchor `done a` with the final state `a` as the verdict.
No work tape is touched. With `δ` testing membership in the image of an
embedding, it is the input validator of design §12.8a §0. -/
def inputFoldTM {Γ : Type*} {A : Type} (k : ℕ) (δ : A → Γ → A) (a₀ : A) :
    MultiTapeTM k Γ (ScanPhase A) where
  q₀ := .fwd a₀
  tr := fun q inp _ =>
    match q with
    | .fwd a =>
      match inp with
      | some γ => inputMoveAction 1 (.fwd (δ a γ))
      | none => inputMoveAction (-1) (.bwd a)
    | .bwd a =>
      match inp with
      | some _ => inputMoveAction (-1) (.bwd a)
      | none => inputMoveAction 1 (.done a)
    | .done a => inputMoveAction 0 (.done a)

/-- The native fold's forward accumulator and input position after `r` reads. -/
private def scanFoldF {Γ : Type*} {A : Type} {k : ℕ} {x : List Γ}
    (δ : A → Γ → A) (a₀ : A) (d : Cfg k Γ (ScanPhase A) x) (r : ℕ) :
    Cfg k Γ (ScanPhase A) x :=
  { d with state := some (.fwd ((x.take r).foldl δ a₀))
           inputPos := ⟨min r x.length + 1, by omega⟩ }

/-- The native fold's return keeps the completed accumulator and counts input positions down. -/
private def scanFoldR {Γ : Type*} {A : Type} {k : ℕ} {x : List Γ}
    (δ : A → Γ → A) (a₀ : A) (d : Cfg k Γ (ScanPhase A) x) (r : ℕ) :
    Cfg k Γ (ScanPhase A) x :=
  { d with state := some (.bwd (x.foldl δ a₀))
           inputPos := ⟨min r x.length, by omega⟩ }

/-- The native fold is an instance of the public two-pass trace, with untouched work tapes.

**Proof sketch.** Interior input reads extend the prefix fold by one symbol. The
right marker changes to the backward phase without changing the final accumulator.
The return passes over the input and enters the fixed verdict at its left marker.
All five equations cite the public input-only step lemma. -/
private theorem scan_fold_trace {Γ : Type*} {A : Type} {k : ℕ} {x : List Γ}
    (δ : A → Γ → A) (a₀ : A) (d : Cfg k Γ (ScanPhase A) x)
    (hstate : d.state = some (.fwd a₀)) (hin : d.inputPos = 1) (t : ℕ) :
    (inputFoldTM k δ a₀).runFrom d t =
      catalogTrace (scanFoldF δ a₀ d) (scanFoldR δ a₀ d)
        { d with state := some (.done (x.foldl δ a₀)) } x.length t := by
  have h0 : scanFoldF δ a₀ d 0 = d := by
    apply Cfg.ext <;> simp [scanFoldF, hstate, hin]
  conv_lhs => rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hs : (scanFoldF δ a₀ d r).inputSymbol = some x[r] :=
      inputSymbolInner r (by simp [scanFoldF]; omega) hr
    rw [step_of_inputMoveAction _ _ 1 rfl
      (q' := .fwd (δ ((x.take r).foldl δ a₀) x[r])) (by simp only [inputFoldTM, hs])]
    apply Cfg.ext
    case state =>
      simp only [scanFoldF]
      rw [List.take_succ, List.getElem?_eq_getElem hr, List.foldl_append]
      rfl
    case inputPos =>
      simp only [scanFoldF]
      rw [← SignType.pos_eq_one, moveInputPos_pos_of_ne_right _ (by simp; omega)]
      simp
      omega
    all_goals simp [scanFoldF]
  · have hs : (scanFoldF δ a₀ d x.length).inputSymbol = none := by
      simp [Cfg.inputSymbol, scanFoldF]
    rw [step_of_inputMoveAction _ _ (-1) rfl
      (q' := .bwd ((x.take x.length).foldl δ a₀)) (by simp only [inputFoldTM, hs])]
    apply Cfg.ext
    case inputPos =>
      simp only [scanFoldF, scanFoldR]
      apply Fin.ext
      rw [← SignType.neg_eq_neg_one, FinTM.moveInputPos_neg_val]
      simp
    all_goals simp [scanFoldF, scanFoldR]
  · intro r hr
    have hs : (scanFoldR δ a₀ d (r + 1)).inputSymbol = some x[r] :=
      inputSymbolInner r (by simp [scanFoldR]; omega) hr
    rw [step_of_inputMoveAction _ _ (-1) rfl
      (q' := .bwd (x.foldl δ a₀)) (by simp only [inputFoldTM, hs])]
    apply Cfg.ext
    case inputPos =>
      simp only [scanFoldR]
      apply Fin.ext
      rw [← SignType.neg_eq_neg_one, FinTM.moveInputPos_neg_val]
      simp
      omega
    all_goals simp [scanFoldR]
  · have hs : (scanFoldR δ a₀ d 0).inputSymbol = none := by
      simp [Cfg.inputSymbol, scanFoldR]
    rw [step_of_inputMoveAction _ _ 1 rfl
      (q' := .done (x.foldl δ a₀)) (by simp only [inputFoldTM, hs])]
    apply Cfg.ext
    case inputPos =>
      simp only [scanFoldR, hin]
      rw [← SignType.pos_eq_one, moveInputPos_pos_of_ne_right _ (by simp)]
      apply Fin.ext
      simp
    all_goals simp [scanFoldR]
  · rw [step_of_inputMoveAction _ _ 0 rfl (q' := .done (x.foldl δ a₀)) rfl]
    simp

/-- **R8.5d, the input fold, framed** (design §12.8a). From any configuration
in the forward phase at `a₀` with the input head at position `1`, the fold
reaches `done (x.foldl δ a₀)` at exactly `2|x| + 2`, where `x` is the native
input, and no `done` anchor earlier. Nothing else changes: the finish is the
start configuration with only the control state replaced, so the input head is
back at `1`. Up to the exit no work head moves.

**Proof sketch.** Induct on the input cells: after `j ≤ |x|` forward steps the
state is the fold of the first `j` symbols and the input head is at `j + 1`.
The right end marker turns the head, `|x|` steps return it, and the left end
marker supplies the entry step. -/
theorem inputFoldTM_run_ofCfg {Γ : Type*} {A : Type} {k : ℕ} {x : List Γ}
    (δ : A → Γ → A) (a₀ : A) (d : Cfg k Γ (ScanPhase A) x)
    (hstate : d.state = some (.fwd a₀)) (hin : d.inputPos = 1) :
    (inputFoldTM k δ a₀).runFrom d (2 * x.length + 2) =
        { d with state := some (.done (x.foldl δ a₀)) } ∧
      (∀ t < 2 * x.length + 2, ∀ a,
        ((inputFoldTM k δ a₀).runFrom d t).state ≠ some (.done a)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * x.length + 2 →
        ((inputFoldTM k δ a₀).runFrom d t).workTapePos j = d.workTapePos j) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [scan_fold_trace δ a₀ d hstate hin]
    simp [catalogTrace, show ¬2 * x.length + 2 ≤ x.length by omega]
  · intro t ht a
    rw [scan_fold_trace δ a₀ d hstate hin]
    simp only [catalogTrace]
    split_ifs <;> simp [scanFoldF, scanFoldR] <;> omega
  · intro j t _
    rw [scan_fold_trace δ a₀ d hstate hin]
    simp only [catalogTrace]
    split_ifs <;> simp [scanFoldF, scanFoldR]

end Turing
