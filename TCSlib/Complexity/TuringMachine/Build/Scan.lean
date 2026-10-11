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

**Status: statements.** The four machines and the writers' phase alphabet are
real definitions. Every contract is sorried with a proof sketch, pending the
§12.8 fill.

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
  contracts (statements).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape model with a read-only
  input tape; the routines are folklore subroutines of the textbook's
  simulations. §4.1: the space measure that makes input validation necessary
  for the rich simulators.)
-/

namespace Turing

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Turing
