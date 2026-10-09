/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: catalog promotions and space annotations (R3)

The R3 increment of the machine-construction library
(`machine-library-design.md` §12): the remaining audited A-chain tape
routines promoted as public machines with exact time **and** space costs,
plus the space retro-annotation of the existing catalog and control
surface. Per frozen decision 12.2 this lives in a **new** file — the new
rows and the space lemmas for the old rows both — keeping
`Build/Primitives.lean` byte-identical; the later refactor toward a
per-theme layout is a recorded backlog item.

**Status: statement skeleton (§12 statement phase).** The five routine
machines and their two phase alphabets are real definitions (TM1-style
labelled control, the catalog's house idiom); every contract is sorried,
each with a proof sketch naming its fill obligations.

## Part 1 — new promotions (seam routines)

Configuration-level routines at the `Turing.Cfg.ofWords` seam of
`TCSlib.Complexity.TuringMachine.Build.Convention`, entering at their
start anchor with heads at the origin and exiting at a **live** anchor
(first-return cut included in each contract), so they compose under
`Turing.seamCompTM`. These are D6-style promotions of the audited 4A
privates — the A3 chain proved `3|w| + 3` copy and `2|w| + 2` clear,
matching the external prior art's catalog to within one step
(independent convergence, 2026-10-06 survey; [Bon26], the
transfer/clear/copy routine catalog):

* `Turing.transferTM` — move a word from tape `src` to tape `dst`
  (source erased), within `3|w| + 3`.
* `Turing.copyTM` — copy a word from tape `src` to tape `dst` (source
  kept), within `3|w| + 3`.
* `Turing.clearTM` — blank the word on one tape, within `2|w| + 2`.
* `Turing.compareTM` — word equality of two tapes, verdict in the exit
  anchor, tapes restored, within `2·min(|u|,|v|) + 2`.
* `Turing.incrementTM` — in-place little-endian fixed-width increment
  (`Turing.incFixed`), success/overflow in the exit anchor, within
  `2|w| + 2`; on overflow the word wraps to all-`false`.

Each routine carries per-tape space statements
(`Turing.MultiTapeTM.spaceUsedByTape`): the touched tapes visit at most
the word interval plus the two boundary blanks, and every other tape
stays at its origin singleton.

## Part 2 — space retro-annotation

Per frozen decision 12.3, the existing catalog rows (P1–P15 as realized)
and the control combinators W1–W3 and L receive `spaceUsed` theorems in
this increment, with no signature changes and no edits to the home files:
each annotation restates the audited row's existential contract joined
with a space clause on the same witness, so the audited statement surface
is untouched (additive growth). The emitter combinators (E1/E2/E3′/E4′ —
`exists_emitLoopTM`, `emit_run`/`exists_emitCallTM`, the stream rows
P16–P18, `splitSolveWith`) stay lazy until a space consumer appears.

## Main definitions

* `Turing.SweepPhase`, `Turing.FlagPhase` — the two phase alphabets.
* `Turing.transferTM`, `Turing.copyTM`, `Turing.clearTM`,
  `Turing.compareTM`, `Turing.incrementTM`.

## Main results

All sorried (statement phase): the five routines' run and per-tape space
contracts (`*_run`, `*_spaceUsedByTape`); the catalog space rows
`Turing.FinTM.computesFunInTime_*_spaceUsed` (P1–P15 as realized,
including the threaded-map row with its payload space hypothesis); and
the control-layer rows `Turing.capture_visitedByTapeHead` (W1),
`Turing.FinTM.redirectTM_spaceUsedByTape` (W2),
`Turing.FinTM.computesFunInTime_cond_spaceUsed` (W3), and
`Turing.FinTM.exists_loopTM_spaceUsed` (L).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: the routines are the
  folklore tape subroutines of the textbook's simulation arguments;
  Definition 4.1: the visited-cells space measure the annotations use.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the transfer/clear/copy/compare routine catalog
  and its exact-cost discipline.
-/

namespace Turing

/-- Phase alphabet of the sweep-shaped routines (`Turing.transferTM`,
`Turing.copyTM`, `Turing.clearTM`): a forward pass over the stored word,
a return pass to the origin, and the live exit anchor. -/
inductive SweepPhase where
  /-- the forward pass over the stored word -/
  | sweep
  /-- the return pass back to the origin -/
  | rewind
  /-- the live exit anchor -/
  | done
deriving DecidableEq, Fintype

/-- Phase alphabet of the verdict-bearing routines (`Turing.compareTM`,
`Turing.incrementTM`): a forward working pass, a return pass carrying the
verdict, and a pair of live exit anchors indexed by the verdict. -/
inductive FlagPhase where
  /-- the forward working pass -/
  | run
  /-- the return pass, carrying the verdict -/
  | rewind (flag : Bool)
  /-- the live exit anchors, one per verdict -/
  | done (flag : Bool)
deriving DecidableEq, Fintype

variable {k : ℕ} {x : List Bool}

/-- **R3, transfer** (design §12; [Bon26]). Move the word stored on tape
`src` to tape `dst`: a forward pass copies cell by cell (both heads in
lockstep), the turn at the source's right blank starts the return pass,
which erases the source on the way back, and the overshoot to the left
blank steps right into the live `done` anchor with both heads at the
origin. -/
def transferTM (k : ℕ) (src dst : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some b), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some _ =>
        ⟨0, fun j => if j = src then (some none, SignType.neg)
            else if j = dst then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, copy** (design §12; [Bon26]; the A3 chain's `3|w| + 3` row).
Copy the word stored on tape `src` onto tape `dst`, keeping the source:
the same two-pass sweep as `Turing.transferTM` without the erasure on the
return pass. -/
def copyTM (k : ℕ) (src dst : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some b), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some _ =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, clear** (design §12; [Bon26]; P12's engine, the A3 chain's
`2|w| + 2` row, and the frozen §3 scratch discipline's supporting
primitive). Blank the word on tape `i`: a forward pass to the right blank,
then a return pass erasing each cell, with the left-blank overshoot
stepping right into the live `done` anchor at the origin. -/
def clearTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
    | .rewind =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (some none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, compare** (design §12; [Bon26]; the 4A chain's `clCmp*` shape).
Test the words on tapes `fst` and `snd` for equality, read-only: a
lockstep forward scan compares cell by cell — the first mismatch (a
differing pair, or one word ending early) selects the `false` verdict, a
simultaneous double blank selects `true` — then a return pass guided by
`fst`'s intact content carries the verdict to the live `done` anchor with
both heads at the origin and both words untouched. -/
def compareTM (k : ℕ) (fst snd : Fin k) : MultiTapeTM k Bool FlagPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w fst, w snd with
      | some a, some b =>
        if a = b then
          ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.pos)
              else (none, 0), none, some .run⟩
        else
          ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
              else (none, 0), none, some (.rewind false)⟩
      | none, none =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind true)⟩
      | _, _ =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind false)⟩
    | .rewind v =>
      match w fst with
      | some _ =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind v)⟩
      | none =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.pos)
            else (none, 0), none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩

/-- **R3, increment** (design §12; [Bon26]; the enumerator's
`enumCarryTM` discipline in place, cf. the string-function row
`Turing.FinTM.computesFunInTime_incFixed`). In-place little-endian
fixed-width binary increment on tape `i`: the carry pass flips `true`
cells to `false` moving right; the first `false` flips to `true` and
selects the success verdict; running off the width (all `true`) selects
the overflow verdict, leaving the wrapped all-`false` word — the
enumerator's counter convention. The return pass carries the verdict to
the live `done` anchor at the origin. -/
def incrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w i with
      | some true =>
        ⟨0, fun j => if j = i then (some (some false), SignType.pos)
            else (none, 0), none, some .run⟩
      | some false =>
        ⟨0, fun j => if j = i then (some (some true), SignType.neg)
            else (none, 0), none, some (.rewind true)⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some (.rewind false)⟩
    | .rewind v =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some (.rewind v)⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩

/-- Configuration at a scan position, with explicit words and head positions. -/
private def catalogCfg {S : Type*} (q : S) (w : Fin k → List Bool)
    (heads : Fin k → ℤ) : Cfg k Bool S x :=
  { Cfg.ofWords q w with workTapePos := heads }

/-- The chronological trace of a forward scan, left turn, return, and entry.
The return index is the number of nonblank cells still to erase or cross. -/
private def catalogTrace {S : Type*} (F R : ℕ → Cfg k Bool S x)
    (D : Cfg k Bool S x) (L t : ℕ) : Cfg k Bool S x :=
  if t ≤ L then F t else if t ≤ 2 * L + 1 then R (2 * L + 1 - t) else D

/-- Local transition equations determine the complete trace, including all
stationary steps after the exit. **Proof sketch.** Induct on elapsed time;
split at the forward endpoint, return endpoint, and stationary tail. -/
private lemma catalog_trace_run {S : Type*} (M : MultiTapeTM k Bool S)
    (F R : ℕ → Cfg k Bool S x) (D : Cfg k Bool S x) (L : ℕ)
    (hF : ∀ r < L, M.step (F r) = F (r + 1))
    (hturn : M.step (F L) = R L)
    (hR : ∀ r < L, M.step (R (r + 1)) = R r)
    (hentry : M.step (R 0) = D) (hD : M.step D = D) (t : ℕ) :
    M.runFrom (F 0) t = catalogTrace F R D L t := by
  induction t with
  | zero => simp [catalogTrace]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    by_cases h₁ : t < L
    · simpa [catalogTrace, show t ≤ L by omega, show t + 1 ≤ L by omega]
        using hF t h₁
    · by_cases h₂ : t = L
      · subst t
        simpa [catalogTrace, show ¬L + 1 ≤ L by omega,
          show L + 1 ≤ 2 * L + 1 by omega, show 2 * L + 1 - (L + 1) = L by omega]
          using hturn
      · by_cases h₃ : t < 2 * L + 1
        · have he : 2 * L + 1 - t = (2 * L - t) + 1 := by omega
          simpa [catalogTrace, show ¬t ≤ L by omega, show ¬t + 1 ≤ L by omega,
            show t ≤ 2 * L + 1 by omega, show t + 1 ≤ 2 * L + 1 by omega,
            he, show 2 * L + 1 - (t + 1) = 2 * L - t by omega]
            using hR (2 * L - t) (by omega)
        · by_cases h₄ : t = 2 * L + 1
          · subst t
            simpa [catalogTrace, show ¬2 * L + 1 ≤ L by omega,
              show ¬2 * L + 1 + 1 ≤ L by omega] using hentry
          · simpa [catalogTrace, show ¬t ≤ L by omega,
              show ¬t + 1 ≤ L by omega, show ¬t ≤ 2 * L + 1 by omega,
              show ¬t + 1 ≤ 2 * L + 1 by omega] using hD

/-- A head confined to the inclusive interval from minus one to `L` visits
at most `L+2` cells. -/
private lemma catalog_space_bound {S : Type*} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (L t : ℕ) (i : Fin k)
    (h : ∀ u, -1 ≤ (M.runFrom c u).workTapePos i ∧
      (M.runFrom c u).workTapePos i ≤ (L : ℤ)) :
    M.spaceUsedByTape c t i ≤ L + 2 := by
  have hs : M.visitedByTapeHead c t i ⊆ Finset.Icc (-1 : ℤ) (L : ℤ) := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_Icc.mpr (h u)
  exact (Finset.card_le_card hs).trans (by rw [Int.card_Icc]; omega)

/-- A head stationary at zero has exactly its origin singleton as visited set. -/
private lemma catalog_space_one {S : Type*} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (t : ℕ) (i : Fin k)
    (h : ∀ u, (M.runFrom c u).workTapePos i = 0) :
    M.spaceUsedByTape c t i = 1 := by
  simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead, h]
  rw [Finset.image_const Finset.nonempty_range_add_one]
  rfl

/-- Erasing the last cell of a prefix shortens that prefix by one.
**Proof sketch.** Read the last cell, earlier cells, and outside cells separately. -/
private lemma catalog_erase_take (w : List Bool) (r : ℕ) (hr : r < w.length) :
    Function.update (FinTM.bufferTape (w.take (r + 1))) (r : ℤ) none =
      FinTM.bufferTape (w.take r) := by
  funext z
  by_cases hz : z = (r : ℤ)
  · subst z
    simp [FinTM.bufferTape, List.getElem?_eq_none]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · simp only [FinTM.bufferTape, if_pos h0]
      by_cases hzr : z.toNat < r
      · simp [List.getElem?_take, hzr, show z.toNat < r + 1 by omega]
      · have hzr' : r + 1 ≤ z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by simp; omega)]
    · simp [FinTM.bufferTape, h0]

/-- Appending the next original bit extends a copied prefix by one. -/
private lemma catalog_write_take (w : List Bool) (r : ℕ) (hr : r < w.length) :
    Function.update (FinTM.bufferTape (w.take r)) (r : ℤ) (some w[r]) =
      FinTM.bufferTape (w.take (r + 1)) := by
  rw [List.take_succ_eq_append_getElem hr]
  simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hr)] using
    (FinTM.bufferTape_append (w.take r) w[r]).symm

/-- Clear's forward phase has intact words; the return phase retains exactly
the unerased prefix below and at the head. -/
private def catalogClearF (i : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .sweep w (fun j => if j = i then (r : ℤ) else 0)

/-- Clear's return index counts the remaining unerased cells. -/
private def catalogClearR (i : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update w i ((w i).take r))
    (fun j => if j = i then (r : ℤ) - 1 else 0)

/-- Clear's exact phase invariant. **Proof sketch.** During the scan the
word is intact. The turn reads its right blank. Each return transition erases
just the last remaining cell; the final left blank makes the right-entry. -/
private lemma catalog_clear_trace (i : Fin k) (w : Fin k → List Bool) (t : ℕ) :
    (clearTM k i).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogClearF i w) (catalogClearR i w)
        (Cfg.ofWords .done (Function.update w i [])) (w i).length t := by
  have h0 : catalogClearF (x := x) i w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogClearF, catalogCfg, Cfg.ofWords]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hs : (catalogClearF (x := x) i w r).workTapeSymbols i = some (w i)[r] := by
      simp [catalogClearF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        FinTM.bufferTape_nat, List.getElem?_eq_getElem hr]
    change ((clearTM k i).tr .sweep _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · have hs : (catalogClearF (x := x) i w (w i).length).workTapeSymbols i = none := by
      simp [catalogClearF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
    change ((clearTM k i).tr .sweep _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i <;> simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogClearR (x := x) i w (r + 1)).workTapeSymbols i =
        some (w i)[r] := by
      simp [catalogClearR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show (r + 1 : ℕ) - (1 : ℤ) = (r : ℤ) by omega,
        List.getElem?_take, List.getElem?_eq_getElem hr]
    change ((clearTM k i).tr .rewind _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i
      · subst j
        simpa [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using
          catalog_erase_take (w i) r hr
      · simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, clearTM, catalogClearR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, clearTM, Cfg.ofWords, Action.apply]

/-- Copy and transfer share the forward phase: the destination holds the copied
prefix and the source remains intact, with both heads at its end. -/
private def catalogCopyF (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .sweep (Function.update w dst ((w src).take r))
    (fun j => if j = src ∨ j = dst then (r : ℤ) else 0)

/-- During copy's return the words are complete and unchanged. -/
private def catalogCopyR (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update w dst (w src))
    (fun j => if j = src ∨ j = dst then (r : ℤ) - 1 else 0)

/-- During transfer's return the source retains exactly the unerased prefix. -/
private def catalogTransferR (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update (Function.update w src ((w src).take r)) dst (w src))
    (fun j => if j = src ∨ j = dst then (r : ℤ) - 1 else 0)

/-- The common forward transition copies exactly the next source bit. -/
private lemma catalog_copy_forward (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (r : ℕ) (hr : r < (w src).length) :
    (copyTM k src dst).step (catalogCopyF (x := x) src dst w r) =
      catalogCopyF src dst w (r + 1) := by
  have hs : (catalogCopyF (x := x) src dst w r).workTapeSymbols src =
      some (w src)[r] := by
    simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
      List.getElem?_eq_getElem hr]
  change ((copyTM k src dst).tr .sweep _ _).apply _ = _
  simp only [copyTM, hs]
  apply Cfg.ext <;> simp [Action.apply, catalogCopyF, catalogCfg, Cfg.ofWords]
  · funext j
    by_cases hj : j = dst
    · subst j
      simpa using catalog_write_take (w src) r hr
    · by_cases hs : j = src <;> simp [hj, hs, hne, Ne.symm hne]
  · funext j
    by_cases hd : j = dst <;> by_cases hs : j = src <;>
      simp [hd, hs, hne, SignType.cast] <;> omega

/-- Copy's exact phase invariant, including the stationary exit. -/
private lemma catalog_copy_trace (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (copyTM k src dst).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogCopyF src dst w) (catalogCopyR src dst w)
        (Cfg.ofWords .done (Function.update w dst (w src))) (w src).length t := by
  have h0 : catalogCopyF (x := x) src dst w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogCopyF, catalogCfg, Cfg.ofWords]
    funext j
    by_cases hj : j = dst
    · subst j; simp [hdst]
    · simp [hj]
  rw [← h0]
  apply catalog_trace_run
  · exact catalog_copy_forward src dst hne w
  · have hs : (catalogCopyF (x := x) src dst w (w src).length).workTapeSymbols src =
        none := by
      simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne]
    change ((copyTM k src dst).tr .sweep _ _).apply _ = _
    simp only [copyTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogCopyR (x := x) src dst w (r + 1)).workTapeSymbols src =
        some (w src)[r] := by
      simp [catalogCopyR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_eq_getElem hr]
    change ((copyTM k src dst).tr .rewind _ _).apply _ = _
    simp only [copyTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogCopyR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, copyTM, catalogCopyR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, hne, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, copyTM, Cfg.ofWords, Action.apply]

/-- Transfer's exact phase invariant. The forward transitions are copy's;
on return, erasure is behind the head, leaving every cell still to read intact. -/
private lemma catalog_transfer_trace (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (transferTM k src dst).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogCopyF src dst w) (catalogTransferR src dst w)
        (Cfg.ofWords .done (Function.update (Function.update w src []) dst (w src)))
        (w src).length t := by
  have h0 : catalogCopyF (x := x) src dst w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogCopyF, catalogCfg, Cfg.ofWords]
    funext j
    by_cases hj : j = dst
    · subst j; simp [hdst]
    · simp [hj]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    exact catalog_copy_forward src dst hne w r hr
  · have hs : (catalogCopyF (x := x) src dst w (w src).length).workTapeSymbols src =
        none := by
      simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne]
    change ((transferTM k src dst).tr .sweep _ _).apply _ = _
    simp only [transferTM, hs]
    apply Cfg.ext <;>
      simp [Action.apply, catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hd : j = dst <;> by_cases hs : j = src <;> simp [hd, hs]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogTransferR (x := x) src dst w (r + 1)).workTapeSymbols src =
        some (w src)[r] := by
      simp [catalogTransferR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_take, List.getElem?_eq_getElem hr]
    change ((transferTM k src dst).tr .rewind _ _).apply _ = _
    simp only [transferTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogTransferR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hs : j = src
      · subst j
        simpa [hne, show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using
          catalog_erase_take (w src) r hr
      · by_cases hd : j = dst
        · subst j; simp [hne, Ne.symm hne]
        · simp [hs, hd]
    · funext j
      by_cases hs : j = src <;> by_cases hd : j = dst <;>
        simp [hs, hd, hne, Ne.symm hne, SignType.cast] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, transferTM, catalogTransferR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, hne, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, transferTM, Cfg.ofWords, Action.apply]

/-- The first unequal or terminating cells occur after a common nonblank
prefix, and equality at those terminating cells is precisely word equality.
**Proof sketch.** Remove equal leading bits recursively; unequal bits or either
empty list stop immediately. This also covers aliased physical tape indices. -/
private lemma catalog_compare_stop (u v : List Bool) :
    ∃ d ≤ min u.length v.length,
      (∀ r < d, ∃ b, u[r]? = some b ∧ v[r]? = some b) ∧
      (¬∃ b, u[d]? = some b ∧ v[d]? = some b) ∧
      (u[d]? = v[d]? ↔ u = v) := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
    | cons b v => exact ⟨0, by simp, by simp, by simp, by simp⟩
  | cons a u ih =>
    cases v with
    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
    | cons b v =>
      by_cases hab : a = b
      · subst b
        obtain ⟨d, hd, hp, hs, he⟩ := ih v
        refine ⟨d + 1, by simpa using hd, ?_, ?_, ?_⟩
        · intro r hr
          cases r with
          | zero => exact ⟨a, rfl, rfl⟩
          | succ r => simpa using hp r (by omega)
        · simpa using hs
        · simpa using he
      · refine ⟨0, by simp, by simp, ?_, ?_⟩
        · simpa [eq_comm] using hab
        · simp [hab]

/-- Comparison's forward configuration retains every word and advances the
selected physical heads once each, including when the two indices coincide. -/
private def catalogCompareF (fst snd : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool FlagPhase x :=
  catalogCfg .run w (fun j => if j = fst ∨ j = snd then (r : ℤ) else 0)

/-- Comparison's return configuration carries the verdict without changing words. -/
private def catalogCompareR (fst snd : Fin k) (w : Fin k → List Bool)
    (v : Bool) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg (.rewind v) w
    (fun j => if j = fst ∨ j = snd then (r : ℤ) - 1 else 0)

/-- Comparison's exact configuration invariant, at a first differing or blank
position. **Proof sketch.** The common-prefix condition supplies every forward
read and every first-tape return read. The stopping condition determines the
turn and verdict. The heads then return from `d-1` through `-1` to zero. -/
private lemma catalog_compare_trace (fst snd : Fin k) (w : Fin k → List Bool)
    (d : ℕ) (hd : d ≤ min (w fst).length (w snd).length)
    (hp : ∀ r < d, ∃ b, (w fst)[r]? = some b ∧ (w snd)[r]? = some b)
    (hs : ¬∃ b, (w fst)[d]? = some b ∧ (w snd)[d]? = some b)
    (he : ((w fst)[d]? = (w snd)[d]?) ↔ w fst = w snd) (t : ℕ) :
    (compareTM k fst snd).runFrom (Cfg.ofWords (input := x) .run w) t =
      catalogTrace (catalogCompareF fst snd w)
        (catalogCompareR fst snd w (decide (w fst = w snd)))
        (Cfg.ofWords (.done (decide (w fst = w snd))) w) d t := by
  have h0 : catalogCompareF (x := x) fst snd w 0 = Cfg.ofWords .run w := by
    apply Cfg.ext <;> simp [catalogCompareF, catalogCfg, Cfg.ofWords]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    obtain ⟨b, hf, hg⟩ := hp r hr
    have hsf : (catalogCompareF (x := x) fst snd w r).workTapeSymbols fst = some b := by
      simpa [catalogCompareF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols] using hf
    have hsg : (catalogCompareF (x := x) fst snd w r).workTapeSymbols snd = some b := by
      simpa [catalogCompareF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols] using hg
    change ((compareTM k fst snd).tr .run _ _).apply _ = _
    simp only [compareTM, hsf, hsg, ↓reduceIte]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareF, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · have hread : (catalogCompareF (x := x) fst snd w d).workTapeSymbols =
        fun j => FinTM.bufferTape (w j) (if j = fst ∨ j = snd then (d : ℤ) else 0) := rfl
    have ht : (compareTM k fst snd).tr .run
        (catalogCompareF (x := x) fst snd w d).inputSymbol
        (catalogCompareF (x := x) fst snd w d).workTapeSymbols =
        ⟨0, (fun j => if j = fst ∨ j = snd then (none, SignType.neg) else (none, 0)),
          none, some (.rewind (decide (w fst = w snd)))⟩ := by
      simp only [compareTM, hread, if_pos (Or.inl rfl : fst = fst ∨ fst = snd),
        if_pos (Or.inr rfl : snd = fst ∨ snd = snd), FinTM.bufferTape_nat]
      cases hf : (w fst)[d]? with
      | none =>
        cases hg : (w snd)[d]? with
        | none =>
          have heq : w fst = w snd := he.mp (by rw [hf, hg])
          simp [hf, hg, heq]
        | some b =>
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            simp only [hf, hg, reduceCtorEq] at h'
          simp [hf, hg, hneq]
      | some a =>
        cases hg : (w snd)[d]? with
        | none =>
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            simp only [hf, hg, reduceCtorEq] at h'
          simp [hf, hg, hneq]
        | some b =>
          have hab : a ≠ b := by
            intro h
            subst b
            exact hs ⟨a, hf, hg⟩
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            exact hab (by simpa only [hf, hg, Option.some.injEq] using h')
          simp [hf, hg, hab, hneq]
    change ((compareTM k fst snd).tr .run _ _).apply _ = _
    rw [ht]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    obtain ⟨b, hf, _⟩ := hp r hr
    have hread : (catalogCompareR (x := x) fst snd w (decide (w fst = w snd))
        (r + 1)).workTapeSymbols fst = some b := by
      simpa [catalogCompareR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using hf
    change ((compareTM k fst snd).tr (.rewind _) _ _).apply _ = _
    simp only [compareTM, hread]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, compareTM, catalogCompareR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, compareTM, Cfg.ofWords, Action.apply]

/-- A word consists of its leading true bits followed by either a first false
bit and its tail, or no remaining bits. -/
private lemma catalog_increment_split (w : List Bool) :
    ∃ p : ℕ, ∃ tail : Option (List Bool),
      w = List.replicate p true ++ tail.elim [] (false :: ·) := by
  induction w with
  | nil => exact ⟨0, none, rfl⟩
  | cons b w ih =>
    cases b with
    | false => exact ⟨0, some w, rfl⟩
    | true =>
      obtain ⟨p, tail, hw⟩ := ih
      exact ⟨p + 1, tail, by simp [List.replicate_succ, hw]⟩

/-- Fixed-width increment flips the leading true prefix and the first false;
an absent first false gives overflow. -/
private lemma catalog_increment_value (p : ℕ) (tail : Option (List Bool)) :
    incFixed (List.replicate p true ++ tail.elim [] (false :: ·)) =
      tail.map (fun v => List.replicate p false ++ true :: v) := by
  induction p with
  | zero => cases tail <;> rfl
  | succ p ih =>
    simp only [List.replicate_succ, List.cons_append, incFixed, ih]
    cases tail <;> rfl

/-- Changing the cell immediately after a prefix changes exactly that bit.
**Proof sketch.** At the selected cell use list indexing at the prefix length;
elsewhere, the suffix and prefix lookups are unchanged. -/
private lemma catalog_write_middle (pre rest : List Bool) (a b : Bool) :
    Function.update (FinTM.bufferTape (pre ++ a :: rest)) (pre.length : ℤ) (some b) =
      FinTM.bufferTape (pre ++ b :: rest) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · simp only [FinTM.bufferTape, if_pos h0, List.getElem?_append]
      by_cases hlt : z.toNat < pre.length
      · simp [hlt]
      · have he : z.toNat - pre.length = (z.toNat - pre.length - 1) + 1 := by omega
        simp only [if_neg hlt]
        rw [he]
        rfl
    · simp [FinTM.bufferTape, h0]

/-- Increment's carry configuration: the first `r` bits have been reset, the
remaining true prefix and stopping suffix are intact, and the head is at `r`. -/
private def catalogIncF (i : Fin k) (w : Fin k → List Bool) (p : ℕ)
    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg .run (Function.update w i
    (List.replicate r false ++ List.replicate (p - r) true ++ tail.elim [] (false :: ·)))
    (fun j => if j = i then (r : ℤ) else 0)

/-- Increment's return configuration holds the complete updated or wrapped
word and carries the success bit, with the head immediately before cell `r`. -/
private def catalogIncR (i : Fin k) (w : Fin k → List Bool) (p : ℕ)
    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg (.rewind tail.isSome)
    (Function.update w i (List.replicate p false ++ tail.elim [] (true :: ·)))
    (fun j => if j = i then (r : ℤ) - 1 else 0)

/-- Increment's exact phase invariant. **Proof sketch.** Each carry step resets
one true bit; the first false is changed on the left-turn itself, so cell `p+1`
is not visited. With no false, the right blank turns without writing. Both cases
return over the reset prefix and enter the live exit after exactly `2p+2` steps. -/
private lemma catalog_increment_trace (i : Fin k) (w : Fin k → List Bool)
    (p : ℕ) (tail : Option (List Bool))
    (hw : w i = List.replicate p true ++ tail.elim [] (false :: ·)) (t : ℕ) :
    (incrementTM k i).runFrom (Cfg.ofWords (input := x) .run w) t =
      catalogTrace (catalogIncF i w p tail) (catalogIncR i w p tail)
        (Cfg.ofWords (.done tail.isSome)
          (Function.update w i (List.replicate p false ++ tail.elim [] (true :: ·)))) p t := by
  have h0 : catalogIncF (x := x) i w p tail 0 = Cfg.ofWords .run w := by
    apply Cfg.ext <;> simp [catalogIncF, catalogCfg, Cfg.ofWords, ← hw]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hpr : p - r = (p - (r + 1)) + 1 := by omega
    have hs : (catalogIncF (x := x) i w p tail r).workTapeSymbols i = some true := by
      simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        hpr, List.replicate_succ, List.append_assoc]
    change ((incrementTM k i).tr .run _ _).apply _ = _
    simp only [incrementTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i
      · subst j
        have hh := catalog_write_middle (List.replicate r false)
          (List.replicate (p - (r + 1)) true ++ tail.elim [] (false :: ·)) true false
        simp only [ite_true, Function.update_self]
        rw [hpr, List.replicate_succ, List.cons_append]
        simpa only [List.length_replicate, List.replicate_succ',
          List.append_assoc, List.singleton_append] using hh
      · simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · cases tail with
    | none =>
      have hs : (catalogIncF (x := x) i w p none p).workTapeSymbols i = none := by
        simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
      change ((incrementTM k i).tr .run _ _).apply _ = _
      simp only [incrementTM, hs]
      apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      all_goals
        funext j
        split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
    | some v =>
      have hs : (catalogIncF (x := x) i w p (some v) p).workTapeSymbols i = some false := by
        simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
      change ((incrementTM k i).tr .run _ _).apply _ = _
      simp only [incrementTM, hs]
      apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      · funext j
        by_cases hj : j = i
        · subst j
          simpa using catalog_write_middle (List.replicate p false) v false true
        · simp [hj]
      · funext j
        split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogIncR (x := x) i w p tail (r + 1)).workTapeSymbols i = some false := by
      simp [catalogIncR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_append, hr]
    change ((incrementTM k i).tr (.rewind _) _ _).apply _ = _
    simp only [incrementTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogIncR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, incrementTM, catalogIncR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, incrementTM, Cfg.ofWords, Action.apply]

/-- **Transfer, the run contract** (spec, fill pending — design §12 R3;
[Bon26]). From the seam with word `w src` on the source and a blank
destination, the routine reaches — within `3|w src| + 3` steps and
without visiting the exit anchor earlier — the seam whose source is blank
and whose destination holds the word, everything else untouched.

**Proof sketch.** Two phase invariants. *Sweep*, time `p ≤ |w|`: heads of
`src`/`dst` at `p`, `dst` holding the copied prefix, `src` intact; the
turn at the right blank enters *rewind*. *Rewind*, positions `|w| - 1`
down to `-1`: `src` erased above the head, `dst` complete; the left-blank
overshoot steps right into `done` at the origin at time `2|w| + 2`
(` ≤ 3|w| + 3`). The cut holds because `done` only appears after the
overshoot. -/
theorem transferTM_run (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) :
    ∃ T ≤ 3 * (w src).length + 3,
      (∀ t < T, ((transferTM k src dst).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (transferTM k src dst).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done
          (Function.update (Function.update w src []) dst (w src)) := by
  refine ⟨2 * (w src).length + 2, by omega, ?_, ?_⟩
  · intro t ht
    rw [catalog_transfer_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_transfer_trace src dst hne w hdst]
    simp [catalogTrace, show ¬2 * (w src).length + 2 ≤ (w src).length by omega]

/-- **Transfer, per-tape space** (spec, fill pending — design §12 R3).
The two touched tapes visit at most the word interval plus the two
boundary blanks — `|w src| + 2` cells, from the `-1` overshoot to the
right blank at `|w src|` — and every other tape never leaves its origin.

**Proof sketch.** Head-movement count of the phases: both touched heads
walk `0 → |w src| → -1 → 0` in unit steps, so their trajectories lie in
`[-1, |w src|]` (`Finset.Icc`, cardinality `|w src| + 2`); all other
action components are `(none, 0)`, so those trajectories are constant and
the visited set is the origin singleton. -/
theorem transferTM_spaceUsedByTape (k : ℕ) (src dst : Fin k)
    (hne : src ≠ dst) (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (transferTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t src
      ≤ (w src).length + 2 ∧
    (transferTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t dst
      ≤ (w src).length + 2 ∧
    ∀ j : Fin k, j ≠ src → j ≠ dst →
      (transferTM k src dst).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  have hb (j : Fin k) : (transferTM k src dst).spaceUsedByTape
      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_transfer_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨hb src, hb dst, ?_⟩
  intro j hs hd
  apply catalog_space_one
  intro u
  rw [catalog_transfer_trace src dst hne w hdst]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords, hs, hd]

/-- **Copy, the run contract** (spec, fill pending — design §12 R3;
[Bon26]; the A3 `3|w| + 3` row). From the seam with word `w src` on the
source and a blank destination, the routine reaches — within
`3|w src| + 3` steps and without visiting the exit anchor earlier — the
seam where both tapes hold the word.

**Proof sketch.** As `transferTM_run` without the erasure clause: sweep
copies the prefix in lockstep, rewind returns both heads guided by the
intact source, the overshoot enters `done` at time `2|w| + 2`. -/
theorem copyTM_run (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) :
    ∃ T ≤ 3 * (w src).length + 3,
      (∀ t < T, ((copyTM k src dst).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (copyTM k src dst).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done (Function.update w dst (w src)) := by
  refine ⟨2 * (w src).length + 2, by omega, ?_, ?_⟩
  · intro t ht
    rw [catalog_copy_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_copy_trace src dst hne w hdst]
    simp [catalogTrace, show ¬2 * (w src).length + 2 ≤ (w src).length by omega]

/-- **Copy, per-tape space** (spec, fill pending — design §12 R3). As the
transfer routine: the two touched tapes visit at most `|w src| + 2` cells
(the word interval plus both boundary blanks), every other tape exactly
its origin singleton.

**Proof sketch.** Identical head-movement count to
`transferTM_spaceUsedByTape`: both touched heads walk
`0 → |w src| → -1 → 0`; all other tapes receive `(none, 0)` throughout. -/
theorem copyTM_spaceUsedByTape (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (copyTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t src
      ≤ (w src).length + 2 ∧
    (copyTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t dst
      ≤ (w src).length + 2 ∧
    ∀ j : Fin k, j ≠ src → j ≠ dst →
      (copyTM k src dst).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  have hb (j : Fin k) : (copyTM k src dst).spaceUsedByTape
      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_copy_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨hb src, hb dst, ?_⟩
  intro j hs hd
  apply catalog_space_one
  intro u
  rw [catalog_copy_trace src dst hne w hdst]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords, hs, hd]

/-- **Clear, the run contract** (spec, fill pending — design §12 R3;
[Bon26]; the A3 `2|w| + 2` row, P12's engine). From the seam with word
`w i` on tape `i`, the routine reaches — within `2|w i| + 2` steps and
without visiting the exit anchor earlier — the seam with tape `i` blank,
everything else untouched.

**Proof sketch.** Sweep walks right over the intact word to the right
blank (`|w i| + 1` steps including the turn), rewind erases on the way
back and overshoots to `-1`, the final step enters `done` at the origin:
exactly `2|w i| + 2` steps, matching the stated budget on the nose. -/
theorem clearTM_run (k : ℕ) (i : Fin k) (w : Fin k → List Bool) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ((clearTM k i).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (clearTM k i).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done (Function.update w i []) := by
  refine ⟨2 * (w i).length + 2, le_rfl, ?_, ?_⟩
  · intro t ht
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_clear_trace]
    simp [catalogTrace, show ¬2 * (w i).length + 2 ≤ (w i).length by omega]

/-- **Clear, per-tape space** (spec, fill pending — design §12 R3). Tape
`i` visits at most `|w i| + 2` cells (the word interval plus both
boundary blanks); every other tape exactly its origin singleton.

**Proof sketch.** The single touched head walks `0 → |w i| → -1 → 0` in
unit steps, so its trajectory lies in `[-1, |w i|]`; every other tape's
action is `(none, 0)` in every phase. -/
theorem clearTM_spaceUsedByTape (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (clearTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t i
      ≤ (w i).length + 2 ∧
    ∀ j : Fin k, j ≠ i →
      (clearTM k i).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  constructor
  · apply catalog_space_bound
    intro u
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords] <;> omega
  · intro j hj
    apply catalog_space_one
    intro u
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords, hj]

/-- **Compare, the run contract** (spec, fill pending — design §12 R3;
[Bon26]). From the seam, the routine reaches — within
`2·min(|w fst|, |w snd|) + 2` steps and without visiting either exit
anchor earlier — the seam carrying the equality verdict
`decide (w fst = w snd)` in its anchor, with every tape (the compared two
included) byte-identical to the entry.

**Proof sketch.** The lockstep scan maintains "prefixes below the heads
agree"; it ends at the first disagreeing position or the double blank,
at depth at most `min + 1`. List equality is exactly "no disagreement
and simultaneous blank". The return pass is guided by `fst`'s intact
content — sound because the scan depth never exceeds `|w fst| + 1`, so
the first blank met moving left is the `-1` overshoot. Both passes have
the same length, giving `2·min + 2` worst case. -/
theorem compareTM_run (k : ℕ) (fst snd : Fin k) (w : Fin k → List Bool) :
    ∃ T ≤ 2 * min (w fst).length (w snd).length + 2,
      (∀ t < T, ∀ v : Bool, ((compareTM k fst snd).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done v)) ∧
      (compareTM k fst snd).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done (decide (w fst = w snd))) w := by
  obtain ⟨d, hd, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
  refine ⟨2 * d + 2, by omega, ?_, ?_⟩
  · intro t ht v
    rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp [catalogTrace, show ¬2 * d + 2 ≤ d by omega]

/-- **Compare, per-tape space** (spec, fill pending — design §12 R3). The
two compared tapes visit at most `min(|w fst|, |w snd|) + 2` cells (the
scanned interval plus both boundary cells); every other tape exactly its
origin singleton.

**Proof sketch.** Exact position counting, uniformly over mismatches,
equal words, and unequal lengths (round-1 finding 6 — the earlier
`[-1, min + 1]` interval argument did not cover equal inputs): with `d`
the first differing position or the first position where a word ends
(`d ≤ min`), the scan turns at `d`, the return pass overshoots to `-1`,
and both touched trajectories are exactly the integers of `[-1, d]` —
`d + 2 ≤ min + 2` visited cells in every case, aliased indices included;
untouched tapes receive `(none, 0)` throughout. -/
theorem compareTM_spaceUsedByTape (k : ℕ) (fst snd : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (compareTM k fst snd).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t fst
      ≤ min (w fst).length (w snd).length + 2 ∧
    (compareTM k fst snd).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t snd
      ≤ min (w fst).length (w snd).length + 2 ∧
    ∀ j : Fin k, j ≠ fst → j ≠ snd →
      (compareTM k fst snd).spaceUsedByTape
          (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
  obtain ⟨d, hd, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
  have hb (j : Fin k) : (compareTM k fst snd).spaceUsedByTape
      (Cfg.ofWords (input := x) .run w) t j ≤ d + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨(hb fst).trans (by omega), (hb snd).trans (by omega), ?_⟩
  intro j hf hg
  apply catalog_space_one
  intro u
  rw [catalog_compare_trace fst snd w d hd hp hs he]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords, hf, hg]

/-- **Increment, the success contract** (spec, fill pending — design §12
R3). If the word on tape `i` has a successor at its width
(`Turing.incFixed (w i) = some v`), the routine reaches — within
`2|w i| + 2` steps and without visiting either exit anchor earlier — the
seam carrying the success verdict and the incremented word `v` in place.

**Proof sketch.** The carry pass flips the maximal `true`-prefix to
`false` and the first `false` to `true`, which is exactly
`Turing.incFixed`'s recursion. With `p` the first `false` position, the
machine takes `p` carry steps, one left-turn/write step, `p` rewind
steps, and one right-entry step — **exactly `2p + 2 ≤ 2|w i|` steps**,
visited interval `[-1, p]`; it never visits `p + 1` on success, and
`[false]` returns in two steps (round-1 finding 7 corrected the earlier
mixed count). The looser public `2|w i| + 2` is deliberate slack. -/
theorem incrementTM_run_succ (k : ℕ) (i : Fin k) (w : Fin k → List Bool)
    (v : List Bool) (hv : incFixed (w i) = some v) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ∀ b : Bool, ((incrementTM k i).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done b)) ∧
      (incrementTM k i).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done true) (Function.update w i v) := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  rw [hw, catalog_increment_value] at hv
  cases tail with
  | none => simp at hv
  | some tail =>
    have hv' : v = List.replicate p false ++ true :: tail := by simpa using hv.symm
    have hp : p < (w i).length := by simp [hw]
    refine ⟨2 * p + 2, by omega, ?_, ?_⟩
    · intro t ht b
      rw [catalog_increment_trace i w p (some tail) hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      omega
    · rw [catalog_increment_trace i w p (some tail) hw]
      simp [catalogTrace, show ¬2 * p + 2 ≤ p by omega, hv']

/-- **Increment, the overflow contract** (spec, fill pending — design §12
R3). If the word on tape `i` is all `true` (`Turing.incFixed (w i) =
none`), the routine reaches — within `2|w i| + 2` steps and without
visiting either exit anchor earlier — the seam carrying the overflow
verdict and the wrapped all-`false` word, the enumerator's counter
convention.

**Proof sketch.** The carry pass flips every cell and falls off the width
at the right blank (`|w i| + 1` steps), the return pass over the written
`false` word overshoots to `-1` and enters `done false` at the origin:
exactly `2|w i| + 2` steps. -/
theorem incrementTM_run_overflow (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (hv : incFixed (w i) = none) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ∀ b : Bool, ((incrementTM k i).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done b)) ∧
      (incrementTM k i).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done false)
          (Function.update w i (List.replicate (w i).length false)) := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  rw [hw, catalog_increment_value] at hv
  cases tail with
  | some tail => simp at hv
  | none =>
    have hp : (w i).length = p := by simp [hw]
    refine ⟨2 * p + 2, by omega, ?_, ?_⟩
    · intro t ht b
      rw [catalog_increment_trace i w p none hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      omega
    · rw [catalog_increment_trace i w p none hw]
      simp [catalogTrace, show ¬2 * p + 2 ≤ p by omega, hp]

/-- **Increment, per-tape space** (spec, fill pending — design §12 R3).
Tape `i` visits at most `|w i| + 2` cells; every other tape exactly its
origin singleton.

**Proof sketch.** The carry head walks right to at most the right blank
at `|w i|`, back to the `-1` overshoot, and home: trajectory inside
`[-1, |w i|]`; other tapes receive `(none, 0)` in every phase. -/
theorem incrementTM_spaceUsedByTape (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (incrementTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t i
      ≤ (w i).length + 2 ∧
    ∀ j : Fin k, j ≠ i →
      (incrementTM k i).spaceUsedByTape
          (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  have hp : p ≤ (w i).length := by simp [hw]
  constructor
  · have hb : (incrementTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) .run w) t i ≤ p + 2 := by
      apply catalog_space_bound
      intro u
      rw [catalog_increment_trace i w p tail hw]
      simp only [catalogTrace]
      split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords] <;> omega
    omega
  · intro j hj
    apply catalog_space_one
    intro u
    rw [catalog_increment_trace i w p tail hw]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords, hj]

/-- **W1 space row** (spec, fill pending — design §12 R3, decision 12.3).
Under the hypotheses of `Turing.capture_run`, the host's source-bank
tapes visit exactly the source's cells — per-tape, on the nose — and the
capture tape's space usage is bounded by the output recorded in the
window plus one.

**Proof sketch.** `Turing.capture_run` makes the host trajectory on tape
`i.castSucc` pointwise equal to the source's on tape `i`, so the visited
images and their cardinalities agree. The capture head sits at
`|pre ++ output-so-far|`, which is nondecreasing (one cell per recorded
emission, `Turing.MultiTapeTM.output_prefix`), so its visited set is an
integer interval of length the output growth plus one. -/
theorem capture_visitedByTapeHead {k : ℕ} {S H : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      host.tr (emb s) inp w =
        captureAction emb ret (tm.tr s inp fun i => w i.castSucc))
    (pre out₀ : List Bool) (c₀ : Cfg k Bool S x) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    (∀ i : Fin k,
      host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc
        = tm.visitedByTapeHead c₀ t i ∧
      host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t i.castSucc
        = tm.spaceUsedByTape c₀ t i) ∧
    host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t (Fin.last k)
      ≤ (tm.runFrom c₀ t).output.length - c₀.output.length + 1 := by
  have hr (u : ℕ) (hu : u ≤ t) :=
    capture_run tm host emb ret hagree pre out₀ c₀ u
      (fun v hv => hlive v (by omega))
  constructor
  · intro i
    have he : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc =
        tm.visitedByTapeHead c₀ t i := by
      unfold MultiTapeTM.visitedByTapeHead
      apply Finset.image_congr
      intro u hu
      dsimp only
      rw [hr u (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hu))]
      simp [captureCfg, i.isLt]
    exact ⟨he, congrArg Finset.card he⟩
  · have hmono {u v : ℕ} (huv : u ≤ v) :
        (tm.runFrom c₀ u).output.length ≤ (tm.runFrom c₀ v).output.length :=
      (tm.output_prefix c₀ huv).length_le
    have hbound : c₀.output.length ≤ (tm.runFrom c₀ t).output.length :=
      hmono (Nat.zero_le t)
    have hsub : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t (Fin.last k) ⊆
        Finset.Icc ((pre.length + c₀.output.length : ℕ) : ℤ)
          ((pre.length + (tm.runFrom c₀ t).output.length : ℕ) : ℤ) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      have hut : u ≤ t := by have := Finset.mem_range.mp hu; omega
      rw [hr u hut]
      simp only [captureCfg, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
        List.length_append, Finset.mem_Icc]
      have hlo := hmono (Nat.zero_le u)
      have hhi := hmono hut
      simp only [MultiTapeTM.runFrom_zero] at hlo
      constructor <;> omega
    exact (Finset.card_le_card hsub).trans (by
      rw [Int.card_Icc]
      omega)

end Turing

namespace Turing.FinTM

/- F2 local witness copies from Composition.lean and Build/Primitives.lean.
Their transition tables and time proofs are unchanged except for the f2_ prefix;
local copies keep the frozen source modules and their private interfaces intact. -/

/-- The one-state copy machine: emits each input bit moving right, and halts on the
boundary blank. -/
private def f2_idTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some b => ⟨SignType.pos, fun i => i.elim0, some b, some ()⟩
        | none => ⟨SignType.zero, fun i => i.elim0, none, none⟩ }

/-- Run invariant of the copy machine: after `t ≤ n` steps it is live, its input head
sits at position `t + 1`, and it has emitted exactly the first `t` input bits. -/
private lemma f2_idTM_run (x : List Bool) : ∀ t, t ≤ x.length →
    (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).state = some () ∧
    (((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).inputPos : ℕ) = t + 1) ∧
    (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).output = x.take t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hpos, hout⟩ := ih (Nat.le_of_succ_le ht)
    have hrun1 : f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) (t + 1) =
        (f2_idTM.tm.tr () (some (x[t]'(by omega)))
          ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).workTapeSymbols)).apply
          (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun1]
      simp [f2_idTM, Action.apply]
    · rw [hrun1]
      simp only [f2_idTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hrun1]
      simp only [f2_idTM, Action.apply]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- The zero-work-tape machine whose states form the emission chain for `w`. -/
private def f2_constTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm := { q₀ := 0, tr := fun i _ _ => emitAction w id i }

/-- Emit the fixed prefix, then copy the input verbatim. No work tape is needed;
the last finite state is the copy state. -/
private def f2_catalogPrefixTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        if h : q.val < w.length then
          ⟨0, fun i => i.elim0, some w[q.val], some ⟨q.val + 1, by omega⟩⟩
        else match inp with
          | some b => ⟨1, fun i => i.elim0, some b, some q⟩
          | none => ⟨0, fun i => i.elim0, none, none⟩ }

/-- A prefixing-machine configuration with the vacuous work fields suppressed. -/
private def f2_catalogPrefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma f2_catalogPrefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (f2_catalogPrefixTM w).tm.runFrom ((f2_catalogPrefixTM w).tm.initCfg x) i =
      f2_catalogPrefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [f2_catalogPrefixCfg, f2_catalogPrefixTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, f2_catalogPrefixCfg, f2_catalogPrefixTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma f2_catalogPrefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (f2_catalogPrefixTM w).tm.runFrom
      (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [f2_catalogPrefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [f2_catalogPrefixCfg]; omega) (by omega)
    change ((f2_catalogPrefixTM w).tm.tr ⟨w.length, by omega⟩
      (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [f2_catalogPrefixTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, f2_catalogPrefixCfg]
    apply Cfg.ext_zero_tapes
    · rfl
    · change moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.append_assoc]

/-- Prefixing computes `w ++ x` in exactly the bound `|w| + |x| + 1`,
including the final blank-reading halting step.

**Proof sketch.** Concatenate the fixed-word emission run and the input-copy
run; the input head then scans the right boundary, so one final step halts
without emitting anything further. This also covers empty prefix and input. -/
private lemma f2_catalogPrefixTM_computes (w : List Bool) :
    (f2_catalogPrefixTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, f2_catalogPrefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_catalogPrefixTM_copy w x x.length (Nat.le_refl _)]
  simp [f2_catalogPrefixTM, f2_catalogPrefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]


/-- A zero-work-tape configuration indexed by the number of input bits passed. -/
private def f2_scanCfg {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨q, ⟨i + 1, by omega⟩, fun j => j.elim0, fun j => j.elim0, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma f2_scanCfg_read {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    (f2_scanCfg x q i hi out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [f2_scanCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [f2_scanCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- A copy state emits the next `j` input bits after an arbitrary output prefix.
**Proof sketch.** Induct on the number of copied cells; each transition appends
the scanned bit and moves right. The indexed configuration keeps the boundary
case separate from the actual bit-reading steps. -/
private lemma f2_scanCopy_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) : ∀ j (hj : j ≤ x.length),
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) out) j =
      f2_scanCfg x (some q) j hj (out ++ x.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [f2_scanCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change (tm.tr q (f2_scanCfg x (some q) j (by omega) (out ++ x.take j)).inputSymbol
      _).apply _ = _
    rw [htr, f2_scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · simp only [Action.apply, f2_scanCfg, Option.toList_some, List.take_succ,
        List.getElem?_eq_getElem (by omega : j < x.length), List.append_assoc]

/-- After copying the entire input, the right-blank transition halts silently. -/
private lemma f2_scanCopy_finish {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) :
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) out) (x.length + 1) =
      f2_scanCfg x none x.length (by omega) (out ++ x) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_scanCopy_run tm q htr x out _ (by omega)]
  unfold MultiTapeTM.step
  change (tm.tr q (f2_scanCfg x (some q) x.length (by omega)
    (out ++ x.take x.length)).inputSymbol _).apply _ = _
  rw [htr, f2_scanCfg_read]
  apply Cfg.ext_zero_tapes <;> simp [Action.apply, f2_scanCfg]

/-- Duplicate the input into the self-delimiting pair: double on the first
pass, rewind silently after emitting the separator's first bit, then emit its
second bit and copy. Every input is legal, so no validation buffer is needed. -/
private def f2_pairDupTM : FinTM Bool where
  k := 0
  State := Fin 5
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some b => ⟨0, fun j => j.elim0, some b, some 1⟩
          | none => ⟨.neg, fun j => j.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun j => j.elim0, inp, some 0⟩
        | 2 => match inp with
          | some _ => controlAction .neg (some 2)
          | none => controlAction .pos (some 3)
        | 3 => ⟨0, fun j => j.elim0, some true, some 4⟩
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 4⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Every two first-pass transitions emit one doubled input bit.
**Proof sketch.** The first transition emits while staying at the scanned
cell, and the second emits that same bit and advances. Induction concatenates
these two-step blocks, leaving the right blank for the separator transition. -/
private lemma f2_pairDup_double (x : List Bool) : ∀ j (hj : j ≤ x.length),
    f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x) (2 * j) =
      f2_scanCfg x (some (0 : Fin 5)) j hj ((x.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext_zero_tapes <;> simp [f2_scanCfg, f2_pairDupTM]
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread := f2_scanCfg_read x (some (0 : Fin 5)) j (by omega)
      ((x.take j).flatMap fun b => [b, b])
    rw [List.getElem?_eq_getElem (by omega)] at hread
    have hfirst : f2_pairDupTM.tm.step
        (f2_scanCfg x (some (0 : Fin 5)) j (by omega) ((x.take j).flatMap fun b => [b, b])) =
        f2_scanCfg x (some (1 : Fin 5)) j (by omega)
          (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change (f2_pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
      rw [hread]
      apply Cfg.ext_zero_tapes <;> simp [f2_pairDupTM, Action.apply, f2_scanCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change (f2_pairDupTM.tm.tr (1 : Fin 5) _ _).apply _ = _
    rw [f2_scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · change (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) ++
        [x[j]'(by omega)] = (x.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < x.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- The two passes and rewind take exactly `4|x|+4` transitions.
**Proof sketch.** Doubling costs `2|x|`, emitting the first separator bit
costs one, rewind and dispatch cost `|x|+1`, the second separator bit costs
one, and copying with its final blank test costs `|x|+1`. -/
private lemma f2_pairDup_computes (x : List Bool) :
    f2_pairDupTM.ComputesInTime x (pairEncode x x) (4 * (x.length + 1)) := by
  let pre := x.flatMap fun b => [b, b]
  let c : Cfg 0 Bool (Fin 5) x :=
    ⟨some 2, ⟨x.length, by omega⟩, fun j => j.elim0, fun j => j.elim0, pre ++ [false]⟩
  have hsep : f2_pairDupTM.tm.step (f2_scanCfg x (some (0 : Fin 5)) x.length (by omega) pre) = c := by
    unfold MultiTapeTM.step
    change (f2_pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    rw [f2_scanCfg_read]
    apply Cfg.ext_zero_tapes
    · simp [f2_pairDupTM, c]
    · simpa [f2_pairDupTM, Action.apply, f2_scanCfg, c] using
        moveInputPos_neg_of_ne_left (⟨x.length + 1, by omega⟩ : Fin (x.length + 2))
          (by simp [Fin.ext_iff])
    · simp [f2_pairDupTM, Action.apply, f2_scanCfg, c]
  have hr := rewind_scan f2_pairDupTM.tm (2 : Fin 5) (some (3 : Fin 5)) (fun _ _ => rfl) c rfl (by simp [c])
  have hemit : f2_pairDupTM.tm.step {c with state := some (3 : Fin 5), inputPos := 1} =
      f2_scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    apply Cfg.ext_zero_tapes <;>
      simp [MultiTapeTM.step, f2_pairDupTM, c, f2_scanCfg, Action.apply, List.append_assoc]
  have h1 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x) (2 * x.length + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_pairDup_double x x.length (by omega)]
    simpa only [List.take_length] using hsep
  have h2 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1)) =
      {c with state := some (3 : Fin 5), inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, h1]
    exact hr
  have h3 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1) + 1) =
      f2_scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', h2, hemit]
  apply (computesInTime_iff _ _ _ _).mpr
  rw [show 4 * (x.length + 1) = (2 * x.length + 1 + (x.length + 1) + 1) +
    (x.length + 1) by omega, MultiTapeTM.runFrom_add, h3,
    f2_scanCopy_finish f2_pairDupTM.tm (4 : Fin 5) (fun _ _ => rfl)]
  exact ⟨rfl, rfl⟩

/-- Copy a suffix from an already-positioned input head, preserving prior output.
**Proof sketch.** Induct on the suffix. A nonempty suffix emits its first bit
and shifts the prefix/suffix boundary by one. The empty suffix reads the right
blank and halts without another emission. -/
private lemma f2_scanCopy_suffix {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x rest : List Bool) : ∀ pre out (hx : x = pre ++ rest),
    tm.runFrom (f2_scanCfg x (some q) pre.length (by simp [hx]) out) (rest.length + 1) =
      f2_scanCfg x none x.length (by omega) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    subst x
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [htr, f2_scanCfg_read]
    apply Cfg.ext_zero_tapes <;> simp [Action.apply, f2_scanCfg]
  | cons b rest ih =>
    intro pre out hx
    have hlen : pre.length < x.length := by simp [hx]
    have hread : x[pre.length]? = some b := by simp [hx]
    have hs : tm.step (f2_scanCfg x (some q) pre.length (by omega) out) =
        f2_scanCfg x (some q) (pre ++ [b]).length (by simp [hx]) (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (tm.tr q _ _).apply _ = _
      rw [htr, f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [f2_scanCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by omega⟩ : Fin (x.length + 2)) (by simp; omega)
      · rfl
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- A true-prefix scan either remains silent or emits one false per true.
**Proof sketch.** Induct on the prefix length. Taking a shorter prefix gives
the induction hypothesis, and the last entry of the longer prefix identifies
the symbol read by the next transition. -/
private lemma f2_scanTrues_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (emit : Bool)
    (htr : ∀ work, tm.tr q (some true) work =
      ⟨.pos, fun j => j.elim0, if emit then some false else none, some q⟩)
    (x : List Bool) : ∀ j (hj : j ≤ x.length),
    x.take j = List.replicate j true →
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) []) j =
      f2_scanCfg x (some q) j hj (if emit then List.replicate j false else []) := by
  intro j
  induction j with
  | zero => intro hj hp; cases emit <;> rfl
  | succ j ih =>
    intro hj hp
    have hshort : x.take j = List.replicate j true := by
      have h := congrArg (List.take j) hp
      simpa only [List.take_take, List.take_replicate, Nat.min_eq_left (by omega : j ≤ j + 1)] using h
    have hb : x[j]? = some true := by
      have h := congrArg (fun w : List Bool => w[j]?) hp
      simpa [List.getElem?_take, Nat.lt_succ_self] using h
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega) hshort]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [f2_scanCfg_read, hb, htr]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · cases emit <;> simp [Action.apply, f2_scanCfg, List.replicate_succ']

/-- Either every input bit is true (overflow), or its first false splits off
the carry prefix and determines the exact incremented word. -/
private lemma f2_incFixed_cases (x : List Bool) :
    (x = List.replicate x.length true ∧ incFixed x = none) ∨
      ∃ j rest, x = List.replicate j true ++ false :: rest ∧
        incFixed x = some (List.replicate j false ++ true :: rest) := by
  induction x with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons b x ih =>
    cases b with
    | false => exact Or.inr ⟨0, x, rfl, rfl⟩
    | true =>
      rcases ih with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
      · exact Or.inl ⟨by simpa only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and] using hx, by simp [incFixed, hinc]⟩
      · exact Or.inr ⟨j + 1, rest, by simp [hx, List.replicate_succ],
          by simp [incFixed, hinc, List.replicate_succ]⟩

/-- Detect a nonoverflowing word silently, rewind, then perform the carry
while emitting. This is the enumerator's carry discipline adapted to native
input and append-only output; unlike the in-place harvest, it validates first. -/
private def f2_incFixedTM : FinTM Bool where
  k := 0
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, none, some 0⟩
          | some false => controlAction .neg (some 1)
          | none => controlAction 0 none
        | 1 => match inp with
          | some _ => controlAction .neg (some 1)
          | none => controlAction .pos (some 2)
        | 2 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, some false, some 2⟩
          | some false => ⟨.pos, fun j => j.elim0, some true, some 3⟩
          | none => controlAction 0 none
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 3⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Fixed-width increment is computed within `3(|x|+1)` steps, with no output
on overflow, including the empty word.
**Proof sketch.** The all-true case scans and halts silently. Otherwise let
`j` be the first false's index. Detection plus rewind costs `2j+2`; carry
emission and suffix copy cost `|x|+1`. Since `j < |x|`, the advertised
linear envelope covers the whole run. -/
private lemma f2_incFixed_computes (x : List Bool) :
    f2_incFixedTM.ComputesInTime x ((incFixed x).getD []) (3 * (x.length + 1)) := by
  rcases f2_incFixed_cases x with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
  · have hr := f2_scanTrues_run f2_incFixedTM.tm (0 : Fin 4) false (fun _ => rfl)
      x x.length (by omega) (by simpa using hx)
    have hh : f2_incFixedTM.ComputesInTime x [] (x.length + 1) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_succ_eq_step', show f2_incFixedTM.tm.initCfg x =
        f2_scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [f2_incFixedTM, f2_scanCfg], hr]
      unfold MultiTapeTM.step
      change ((f2_incFixedTM.tm.tr (0 : Fin 4) _ _).apply _).state = none ∧ _
      rw [f2_scanCfg_read]
      simp [f2_incFixedTM, controlAction, Action.apply, f2_scanCfg]
    simpa only [hinc, Option.getD_none] using hh.mono (by omega)
  · have hj : j < x.length := by simp [hx]
    have hpre : x.take j = List.replicate j true := by simp [hx]
    have hread : x[j]? = some false := by simp [hx]
    let c : Cfg 0 Bool (Fin 4) x :=
      ⟨some 1, ⟨j, by omega⟩, fun i => i.elim0, fun i => i.elim0, []⟩
    have hdet : f2_incFixedTM.tm.runFrom (f2_incFixedTM.tm.initCfg x) (j + 1) = c := by
      rw [MultiTapeTM.runFrom_succ_eq_step', show f2_incFixedTM.tm.initCfg x =
        f2_scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [f2_incFixedTM, f2_scanCfg],
        f2_scanTrues_run f2_incFixedTM.tm (0 : Fin 4) false (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (f2_incFixedTM.tm.tr (0 : Fin 4) _ _).apply _ = _
      rw [f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [f2_incFixedTM, controlAction, Action.apply, f2_scanCfg, c] using
          moveInputPos_neg_of_ne_left (⟨j + 1, by omega⟩ : Fin (x.length + 2))
            (by simp [Fin.ext_iff])
      · rfl
    have hrew : f2_incFixedTM.tm.runFrom (f2_incFixedTM.tm.initCfg x) (j + 1 + (j + 1)) =
        f2_scanCfg x (some (2 : Fin 4)) 0 (by omega) [] := by
      rw [MultiTapeTM.runFrom_add, hdet]
      exact rewind_scan f2_incFixedTM.tm (1 : Fin 4) (some (2 : Fin 4))
        (fun _ _ => rfl) c rfl (by simp [c]; omega)
    have hemit : f2_incFixedTM.tm.runFrom (f2_scanCfg x (some (2 : Fin 4)) 0 (by omega) [])
        (j + 1) = f2_scanCfg x (some (3 : Fin 4)) (j + 1) (by omega)
          (List.replicate j false ++ [true]) := by
      rw [MultiTapeTM.runFrom_succ_eq_step',
        f2_scanTrues_run f2_incFixedTM.tm (2 : Fin 4) true (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (f2_incFixedTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      rw [f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
      · rfl
    have hcopy := f2_scanCopy_suffix f2_incFixedTM.tm (3 : Fin 4) (fun _ _ => rfl)
      x rest (List.replicate j true ++ [false]) (List.replicate j false ++ [true])
      (by simpa [List.append_assoc] using hx)
    have hh : f2_incFixedTM.ComputesInTime x (List.replicate j false ++ true :: rest)
        ((j + 1 + (j + 1)) + ((j + 1) + (rest.length + 1))) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hrew, MultiTapeTM.runFrom_add, hemit]
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hcopy
      rw [hcopy]
      exact ⟨rfl, by simp [f2_scanCfg, List.append_assoc]⟩
    have hlen : x.length = j + 1 + rest.length := by simp [hx]; omega
    simpa only [hinc, Option.getD_some] using hh.mono (by omega)

/-- A right-moving zero-tape transition advances the indexed configuration
and appends exactly its optional emission. -/
private lemma f2_scanStep_right {S : Type} (tm : MultiTapeTM 0 Bool S)
    (x : List Bool) (q : S) (q' : Option S) (i : ℕ) (hi : i < x.length)
    (out : List Bool) (emit : Option Bool)
    (htr : ∀ work, tm.tr q x[i]? work = ⟨.pos, fun j => j.elim0, emit, q'⟩) :
    tm.step (f2_scanCfg x (some q) i (by omega) out) =
      f2_scanCfg x q' (i + 1) (by omega) (out ++ emit.toList) := by
  unfold MultiTapeTM.step
  change (tm.tr q _ _).apply _ = _
  rw [f2_scanCfg_read, htr]
  apply Cfg.ext_zero_tapes
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
  · rfl

/-- Scan aligned pairs of bits, retaining just the first bit of the current
block. Only a terminal verdict transition emits output. -/
private def f2_pairValidTM : FinTM Bool where
  k := 0
  State := Option Bool
  tm :=
    { q₀ := none
      tr := fun q inp _ => match q, inp with
        | none, some b => ⟨.pos, fun j => j.elim0, none, some (some b)⟩
        | some b, some c =>
          if b = c then ⟨.pos, fun j => j.elim0, none, some none⟩
          else ⟨.pos, fun j => j.elim0, some (!b && c), none⟩
        | _, none => ⟨0, fun j => j.elim0, some false, none⟩ }

/-- One aligned block either continues silently or halts with its verdict. -/
private lemma f2_pairValid_block (x pre rest : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    f2_pairValidTM.tm.runFrom (f2_scanCfg x (some none) pre.length (by simp [hx]) []) 2 =
      if b = c then f2_scanCfg x (some none) (pre.length + 2) (by simp [hx]) []
      else f2_scanCfg x none (pre.length + 2) (by simp [hx]) [!b && c] := by
  have h1 := f2_scanStep_right f2_pairValidTM.tm x none (some (some b)) pre.length
    (by simp [hx]) [] none (by intro work; simp [hx, f2_pairValidTM])
  have h2 := f2_scanStep_right f2_pairValidTM.tm x (some b)
    (if b = c then some none else none) (pre.length + 1) (by simp [hx])
    [] (if b = c then none else some (!b && c)) (by
      intro work
      have hr : x[pre.length + 1]? = some c := by simp [hx]
      rw [hr]
      by_cases h : b = c <;> simp [f2_pairValidTM, h])
  change f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _) = _
  rw [h1]
  simp only [Option.toList_none, List.append_nil]
  rw [h2]
  by_cases h : b = c <;> simp [h]

/-- The validity scanner halts within one more than the unprocessed length.
**Proof sketch.** Induct in aligned two-bit blocks. The empty and singleton
cases fail on a boundary blank. Equal-bit blocks invoke the induction
hypothesis silently; `01` succeeds and `10` fails immediately, independently
of the suffix. Thus no verdict is emitted before validity is decided. -/
private lemma f2_pairValid_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (f2_pairValidTM.tm.runFrom
        (f2_scanCfg x (some none) pre.length (by simp [hx]) []) t).state = none ∧
      (f2_pairValidTM.tm.runFrom
        (f2_scanCfg x (some none) pre.length (by simp [hx]) []) t).output =
          [(pairDecode rest).isSome] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_pairValidTM.tm.tr none _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    simp [hx, f2_pairValidTM, Action.apply, f2_scanCfg, pairDecode]
  | singleton b =>
    intro pre hx
    have h1 := f2_scanStep_right f2_pairValidTM.tm x none (some (some b)) pre.length
      (by simp [hx]) [] none (by intro work; simp [hx, f2_pairValidTM])
    refine ⟨2, by simp, ?_⟩
    change (f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _)).state = none ∧
      (f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _)).output = _
    rw [h1]
    unfold MultiTapeTM.step
    change ((f2_pairValidTM.tm.tr (some b) _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    cases b <;> simp [hx, f2_pairValidTM, Action.apply, f2_scanCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_pairValid_block x pre rest b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> simpa [pairDecode] using ho
    · refine ⟨2, by simp, ?_⟩
      rw [f2_pairValid_block x pre rest b c hx, if_neg h]
      cases b <;> cases c <;> simp_all [f2_scanCfg, pairDecode]

/-- The validity test starts with an empty aligned prefix and uses the
linear envelope `|x|+1`. -/
private lemma f2_pairValid_computes (x : List Bool) :
    f2_pairValidTM.ComputesInTime x [(pairDecode x).isSome] (x.length + 1) := by
  obtain ⟨t, ht, hs, ho⟩ := f2_pairValid_run x x [] rfl
  have hinit : f2_pairValidTM.tm.initCfg x = f2_scanCfg x (some none) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> simp [f2_pairValidTM, f2_scanCfg]
  have h : f2_pairValidTM.ComputesInTime x [(pairDecode x).isSome] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact h.mono ht


/-- A shared extractor buffers the decoded prefix, validates the separator,
rewinds and replays the buffer, then optionally copies the suffix. The two
flags select the first component, the second, or their concatenation. -/
private def f2_pairExtractTM (first second : Bool) : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Fin 3
  tm :=
    { q₀ := .inl none
      tr := fun q inp work => match q with
        | .inl none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .inl (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.inl none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some (.inr 0)⟩
        | .inr q => match q.val with
          | 0 => match work 0 with
            | some _ => ⟨0, fun _ => (none, .neg), none, some (.inr 0)⟩
            | none => ⟨0, fun _ => (none, .pos), none, some (.inr 1)⟩
          | 1 => match work 0 with
            | some b => ⟨0, fun _ => (none, .pos), if first then some b else none, some (.inr 1)⟩
            | none => ⟨0, fun _ => (none, 0), none, some (.inr 2)⟩
          | _ => if second then match inp with
              | some b => ⟨.pos, fun _ => (none, 0), some b, some (.inr 2)⟩
              | none => ⟨0, fun _ => (none, 0), none, none⟩
            else ⟨0, fun _ => (none, 0), none, none⟩ }

/-- The shared extractor's one-buffer configurations. -/
private def f2_extractCfg (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool (Option Bool ⊕ Fin 3) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- The extractor reads the indexed input entry independently of its buffer. -/
private lemma f2_extractCfg_read (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (f2_extractCfg x q i hi a z out).inputSymbol = x[i]? :=
  f2_scanCfg_read x q i hi out

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma f2_extract_first (first second : Bool) (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    (f2_pairExtractTM first second).tm.step
      (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) =
      f2_extractCfg x (some (.inl (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change ((f2_pairExtractTM first second).tm.tr (.inl none) _ _).apply _ = _
  rw [f2_extractCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [f2_extractCfg, hx])
  · funext i; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]

/-- Equal-bit blocks append one decoded bit; `01` begins replay and `10`
halts silently. In particular, neither transition emits physical output. -/
private lemma f2_extract_block (first second : Bool) (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then f2_extractCfg x (some (.inl none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then f2_extractCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else f2_extractCfg x (some (.inr 0)) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change (f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _) = _
  rw [f2_extract_first first second x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change ((f2_pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _ = _
  rw [f2_extractCfg_read]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ := by
    exact moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (bufferTape_append a _).symm)
    | (funext i; simp [f2_pairExtractTM, Action.apply, f2_extractCfg])

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma f2_extract_rewind (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) []) (j + 1) =
      f2_extractCfg x (some (.inr 1)) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_pairExtractTM first second).tm.step
        (f2_extractCfg x (some (.inr 0)) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay reads the buffered word once; the first-component flag decides
whether those reads emit. At the right blank the controller starts the suffix.
**Proof sketch.** Induct on the number of replayed cells. Each live step
preserves the tape and appends either its bit or nothing. -/
private lemma f2_extract_replay (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j (_hj : j ≤ a.length),
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 1)) i hi a 0 []) j =
      f2_extractCfg x (some (.inr 1)) i hi a j (if first then a.take j else []) := by
  intro j
  induction j with
  | zero => intro hj; cases first <;> rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change (if first then a.take j else []) ++
        (if first then some (a[j]'(by omega)) else none).toList =
          (if first then a.take (j + 1) else [])
      have ht : a.take j ++ [a[j]'(by omega)] = a.take (j + 1) := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
        rfl
      cases first with
      | false => rfl
      | true => exact ht

/-- Replay's right-blank test dispatches to the suffix state silently. -/
private lemma f2_extract_replay_finish (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) :
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 1)) i hi a 0 []) (a.length + 1) =
      f2_extractCfg x (some (.inr 2)) i hi a a.length (if first then a else []) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_extract_replay first second x a i hi _ (by omega)]
  unfold MultiTapeTM.step
  simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_length, List.take_length]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext k; simp [Action.apply]
  · simp [Action.apply]

/-- With suffix copying enabled, the final phase emits the remaining input.
**Proof sketch.** The input prefix grows by one at each emitting transition;
the buffer and its head remain fixed. A right-blank test supplies the final
halting step. This is the one-buffer version of the private suffix-copy lemma. -/
private lemma f2_extract_suffix (first : Bool) (x rest a : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
    (f2_pairExtractTM first true).tm.runFrom
      (f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out)
        (rest.length + 1) =
      f2_extractCfg x none x.length (by omega) a a.length (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
    rw [f2_extractCfg_read]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [f2_pairExtractTM, Action.apply, f2_extractCfg, hx]
    · funext k; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
    · simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : (f2_pairExtractTM first true).tm.step
        (f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out) =
        f2_extractCfg x (some (.inr 2)) (pre ++ [b]).length (by simp [hx])
          a a.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((f2_pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
      rw [f2_extractCfg_read]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [f2_extractCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once validation succeeds, rewind, replay, and optional suffix copying
cost at most `2|a|+|rest|+3` steps.
**Proof sketch.** The rewind costs `|a|+1`, and replay plus dispatch costs
`|a|+1`. Disabled suffix copying halts in one step; enabled copying uses
`|rest|+1`. Only these postvalidation phases emit output. -/
private lemma f2_extract_finish (first second : Bool) (x pre rest a : List Bool)
    (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 3,
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).state = none ∧
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          (if first then a else []) ++ (if second then rest else []) := by
  have hp : (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) [])
        ((a.length + 1) + (a.length + 1)) =
      f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length (if first then a else []) := by
    rw [MultiTapeTM.runFrom_add, f2_extract_rewind first second x a _ _ _ (by omega),
      f2_extract_replay_finish]
  cases second with
  | false =>
    refine ⟨(a.length + 1) + (a.length + 1) + 1, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hp]
    simp [MultiTapeTM.step, f2_pairExtractTM, f2_extractCfg, Action.apply]
  | true =>
    refine ⟨((a.length + 1) + (a.length + 1)) + (rest.length + 1), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hp, f2_extract_suffix first x rest a pre _ hx]
    exact ⟨rfl, rfl⟩

/-- The silent aligned parser either rejects or validates and invokes replay.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the
already-decoded buffer. A doubled bit costs two steps and enlarges the buffer
by one; the linear potential `3|rest|+2|a|+5` pays for both effects. Missing
and forbidden separators halt silently. At `01`, apply the validated finish
ledger. The result includes the previously buffered prefix only on success. -/
private lemma f2_extract_run (first second : Bool) (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).state = none ∧
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (b, c) => (if first then a ++ b else []) ++ (if second then c else [])
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairExtractTM first second).tm.tr (.inl none) _ _).apply _).state = none ∧ _
    rw [f2_extractCfg_read]
    simp [hx, f2_pairExtractTM, Action.apply, f2_extractCfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change ((f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _)).state = none ∧
      ((f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _)).output = _
    rw [f2_extract_first first second x pre [] a b hx]
    unfold MultiTapeTM.step
    change (((f2_pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _).state = none ∧ _
    rw [f2_extractCfg_read]
    cases b <;> simp [hx, f2_pairExtractTM, Action.apply, f2_extractCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_extract_block first second x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd, List.append_assoc] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := f2_extract_finish first second x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, f2_extract_block first second x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [f2_extract_block first second x pre rest a true false hx]
        simp [f2_extractCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The three extractor modes share the uniform linear envelope `5(|x|+1)`.
The initial buffer and decoded prefix are empty. -/
private lemma f2_pairExtract_computes (first second : Bool) (x : List Bool) :
    (f2_pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := f2_extract_run first second x x [] [] rfl
  have hinit : (f2_pairExtractTM first second).tm.initCfg x =
      f2_extractCfg x (some (.inl none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [f2_pairExtractTM, f2_extractCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : (f2_pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, by simpa using ho⟩
  exact hh.mono (by simp only [List.length_nil] at ht; omega)


/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive f2_CatalogPolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance f2_catalogPolyControlFintype (c C : ℕ) : Fintype (f2_CatalogPolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance f2_catalogPolyControlDecidableEq (c C : ℕ) : DecidableEq (f2_CatalogPolyControl c C) :=
  (proxy_equiv% (f2_CatalogPolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def f2_catalogPolyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def f2_catalogPolyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : f2_CatalogPolyControl c C) : Action (c + 1) Bool (f2_CatalogPolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def f2_catalogPolyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := f2_CatalogPolyControl c C
  tm := {
    q₀ := .copy
    tr := fun s inp w => match s with
      | .copy => match inp with
        | some _ => ⟨.pos, fun _ => (some (some true), .pos), none, some .copy⟩
        | none => ⟨0, fun _ => (some (some true), .neg), none, some .setup⟩
      | .setup =>
        if w 0 = none then
          ⟨0, fun _ => (none, .pos), none, some (.loop (Fin.last c))⟩
        else ⟨0, fun _ => (none, .neg), none, some .setup⟩
      | .loop i =>
        if w i = none then f2_catalogPolyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then f2_catalogPolyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else f2_catalogPolyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then f2_catalogPolyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def f2_catalogPolyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : f2_CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (f2_CatalogPolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => f2_catalogPolyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma f2_catalogPolyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : f2_CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (f2_catalogPolyMove i d s').apply (f2_catalogPolyCfg x q s h o) =
      f2_catalogPolyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [f2_catalogPolyMove, f2_catalogPolyCfg, Action.apply, hj]
  · simp [f2_catalogPolyMove, f2_catalogPolyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma f2_catalogPoly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      f2_catalogPolyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        f2_catalogPolyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma f2_catalogPoly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      f2_catalogPolyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (f2_CatalogPolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, f2_catalogPolyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [f2_catalogPolyCfg] using f2_catalogPolyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (f2_CatalogPolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, f2_catalogPolyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [f2_catalogPolyCfg, sub_eq_add_neg] using f2_catalogPolyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma f2_catalogPoly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (f2_catalogPolyUnaryTM c C).tm.step
      (f2_catalogPolyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      f2_catalogPolyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, i.isLt, ↓reduceDIte]
  simpa [f2_catalogPolyCfg] using f2_catalogPolyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def f2_catalogPolyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (f2_catalogPolyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma f2_catalogPoly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (f2_catalogPolyCost q C i + 2) + q + 2) =
      f2_catalogPolyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (f2_catalogPolyUnaryTM c C).tm.runFrom
          (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (f2_catalogPolyCost q C i + 2) =
        f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (f2_catalogPolyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape, hj]
      have hs : (f2_catalogPolyUnaryTM c C).tm.step (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) =
          f2_catalogPolyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((f2_catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [f2_catalogPolyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [f2_catalogPolyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop 0) h' o) _ = _
        rw [show f2_catalogPolyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [f2_catalogPolyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop 0) h' o) 1 =
            f2_catalogPolyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          f2_catalogPoly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using f2_catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate C true) (⟨0, hi⟩ : Fin (c + 1))
      · have hlow : ∀ k : Fin (c + 1), k.val ≤ i - 1 → h' k = 0 := by
          intro k hk
          have hne : k ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
          simp only [h', Function.update_of_ne hne]
          exact hh k (by omega)
        have hinner := ih (i - 1) (by omega) (by omega) h' hlow o q 0 (by omega)
        have hupdate : Function.update h' ⟨i - 1, by omega⟩ 0 = h' := by
          rw [← hlow ⟨i - 1, by omega⟩ (le_refl _)]
          exact Function.update_eq_self _ _
        have hi' : i - 1 + 1 = i := by omega
        have hout : q * (C * q ^ (i - 1)) = C * q ^ i := by
          calc
            q * (C * q ^ (i - 1)) = C * (q ^ (i - 1) * q) := by ring
            _ = C * q ^ i := by simp only [← Nat.pow_succ, Nat.succ_eq_add_one, hi']
        simp only [dif_neg hz] at hs
        simp only [Nat.cast_zero] at hinner
        rw [hupdate] at hinner
        have hinner' : (f2_catalogPolyUnaryTM c C).tm.runFrom
            (f2_catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (f2_catalogPolyCost q C i) =
            f2_catalogPolyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (f2_catalogPolyCost q C (i - 1) + 2) + q + 2 =
              f2_catalogPolyCost q C i := by
            calc
              _ = f2_catalogPolyCost q C (i - 1 + 1) := rfl
              _ = f2_catalogPolyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show f2_catalogPolyCost q C i + 2 = 1 + f2_catalogPolyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            f2_catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using f2_catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (f2_catalogPolyUnaryTM c C).tm.step
          (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          f2_catalogPolyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((f2_catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [f2_catalogPolyUnaryTM, Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
          f2_catalogPolyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [f2_catalogPolyCfg, sub_eq_add_neg] using f2_catalogPolyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, f2_catalogPoly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (f2_catalogPolyCost q C i + 2) + q + 2 =
          (f2_catalogPolyCost q C i + 2) + (r * (f2_catalogPolyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma f2_catalogPolyTape_write (q : ℕ) :
    Function.update (f2_catalogPolyTape q) (q : ℤ) (some true) = f2_catalogPolyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [f2_catalogPolyTape]
  · rw [Function.update_of_ne hz]
    unfold f2_catalogPolyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma f2_catalogPolyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    f2_catalogPolyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [f2_catalogPolyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      f2_catalogPolyCost q C (r + 1) = q * (f2_catalogPolyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def f2_catalogPolyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (f2_CatalogPolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => f2_catalogPolyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma f2_catalogPoly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x) i =
      f2_catalogPolyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, f2_catalogPolyCopyCfg, f2_catalogPolyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (f2_catalogPolyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [f2_catalogPolyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((f2_catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact f2_catalogPolyTape_write i
    · funext k
      simp [f2_catalogPolyUnaryTM, f2_catalogPolyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma f2_catalogPoly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      f2_catalogPolyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma f2_catalogPoly_start (c C : ℕ) (x : List Bool) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      f2_catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (f2_catalogPolyUnaryTM c C).tm.step
      (f2_catalogPolyCopyCfg c C x x.length (le_refl _)) =
      f2_catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (f2_catalogPolyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [f2_catalogPolyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((f2_catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact f2_catalogPolyTape_write x.length
    · funext k
      simp [f2_catalogPolyUnaryTM, f2_catalogPolyCopyCfg, f2_catalogPolyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      f2_catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_catalogPoly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact f2_catalogPoly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary catalogPolynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma f2_catalogPoly_unary_computes (c C : ℕ) :
    (f2_catalogPolyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := f2_catalogPoly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost (x.length + 1) C (c + 1)) =
      f2_catalogPolyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [f2_catalogPolyCost, hout] using hl
  have hbase : (f2_catalogPolyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + f2_catalogPolyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, f2_catalogPoly_start, hloop]
    simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (f2_catalogPolyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring



/-- After initialization each loop bank remains a fixed unary interval. The
active loop head may scan its right blank; the active rewind head may scan its
left blank; all other active indices stay strictly inside the installed bank. -/
private def f2_polyHeads {d C : ℕ} (q : ℕ)
    (s : Option (f2_CatalogPolyControl d C)) (h : Fin (d + 1) → ℤ) : Prop :=
  match s with
  | none => ∀ j, -1 ≤ h j ∧ h j ≤ q
  | some (.loop i) => ∀ j, 0 ≤ h j ∧ h j ≤ q ∧ (j ≠ i → h j < q)
  | some (.rewind i) => ∀ j, -1 ≤ h j ∧ h j < q ∧ (j ≠ i → 0 ≤ h j)
  | some (.advance _) | some (.emit _) => ∀ j, 0 ≤ h j ∧ h j < q
  | _ => False

/-- The loop-phase invariant implies the common closed head interval. -/
private lemma f2_polyHeads_bounds {d C q : ℕ}
    {s : Option (f2_CatalogPolyControl d C)} {h : Fin (d + 1) → ℤ}
    (hp : f2_polyHeads q s h) (j : Fin (d + 1)) :
    -1 ≤ h j ∧ h j ≤ q := by
  cases s with
  | none => exact hp j
  | some s =>
    cases s <;> simp only [f2_polyHeads] at hp
    all_goals first | contradiction | (have := hp j; omega)

/-- The nested-loop transitions preserve the installed unary words and the
phase-specific head intervals, independently of output length or round count.
**Proof sketch.** Only initialization writes. A loop's right move can reach its
right blank but no farther; a rewind turns on the left blank at minus one.
Advance changes one index, and emission changes no work head. -/
private lemma f2_poly_step {d C q : ℕ} {x : List Bool} (hq : 0 < q)
    (c : Cfg (d + 1) Bool (f2_CatalogPolyControl d C) x)
    (hw : c.workTapes = fun _ => f2_catalogPolyTape q)
    (hp : f2_polyHeads q c.state c.workTapePos) :
    ((f2_catalogPolyUnaryTM d C).tm.step c).workTapes =
        (fun _ => f2_catalogPolyTape q) ∧
      f2_polyHeads q ((f2_catalogPolyUnaryTM d C).tm.step c).state
        ((f2_catalogPolyUnaryTM d C).tm.step c).workTapePos := by
  have hr (i : Fin (d + 1)) : c.workTapeSymbols i =
      if 0 ≤ c.workTapePos i ∧ c.workTapePos i < q then some true else none := by
    simp only [Cfg.workTapeSymbols, hw, f2_catalogPolyTape]
  cases hs : c.state with
  | none => simpa only [MultiTapeTM.step, hs] using And.intro hw hp
  | some s =>
    simp only [hs] at hp
    cases s with
    | copy => exact False.elim hp
    | setup => exact False.elim hp
    | loop i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hblank : c.workTapeSymbols i = none
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast]
            have := hj.2.2 he
            omega
      · have hi : c.workTapePos i < q := by
          rw [hr] at hblank
          split at hblank <;> simp_all
        have hall (j : Fin (d + 1)) : 0 ≤ c.workTapePos j ∧ c.workTapePos j < q := by
          have hj := hp j
          by_cases he : j = i
          · simpa [he] using And.intro (hp i).1 hi
          · exact ⟨hj.1, hj.2.2 he⟩
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank, ↓reduceIte,
            Action.apply]
          split <;> simp only [f2_polyHeads, SignType.cast, add_zero]
          · exact hall
          · intro j
            have := hall j
            exact ⟨this.1, le_of_lt this.2, fun _ => this.2⟩
    | rewind i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hblank : c.workTapeSymbols i = none
      · have hi : c.workTapePos i = -1 := by
          have hlo := (hp i).1
          have hhi := (hp i).2.1
          rw [hr] at hblank
          have hn : ¬(0 ≤ c.workTapePos i ∧ c.workTapePos i < q) := by
            simpa only [ite_eq_right_iff, Option.some_ne_none, imp_false] using hblank
          omega
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact ⟨hj.2.2 he, hj.2.1⟩
      · have hi : 0 ≤ c.workTapePos i := by
          rw [hr] at hblank
          split at hblank <;> simp_all
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact hj
    | advance i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hi : i.val < d + 1
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi,
            ↓reduceDIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = ⟨i.val, hi⟩
          · simp only [he, ↓reduceIte, SignType.cast]
            simp only [he] at hj
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact ⟨hj.1, le_of_lt hj.2, fun _ => hj.2⟩
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi, ↓reduceDIte,
            Action.apply, f2_polyHeads, SignType.cast, add_zero]
          intro j
          have := hp j
          omega
    | emit j =>
      constructor
      · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM]
        split <;> simpa only [Action.apply] using hw
      · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, Action.apply]
        split <;> simpa only [f2_polyHeads, SignType.cast, add_zero] using hp

/-- A work head lies within the number of elapsed steps of its starting cell.
This is a trajectory bound obtained by adding the one-step movement bounds. -/
private lemma f2_head_steps {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) (i : Fin k) :
    c.workTapePos i - (t : ℤ) ≤ (M.runFrom c t).workTapePos i ∧
      (M.runFrom c t).workTapePos i ≤ c.workTapePos i + (t : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs := abs_le.mp (M.workTapePos_step_le (M.runFrom c t) i)
    rw [MultiTapeTM.runFrom_succ_eq_step']
    push_cast
    constructor <;> omega

/-- The generator's all-time work space is linear in the input length.
**Proof sketch.** Startup lasts `2(n+1)` steps from the origin, so its entire
trajectory fits the interval of that radius. The preserved loop invariant
confines every later head to `[-1,n+1]`, including after halt. Contain the
inclusive visited images in the larger fixed interval and sum its cardinality;
the number of loop iterations never appears in this bound. -/
private lemma f2_poly_space (d C : ℕ) (x : List Bool) (t : ℕ) :
    (f2_catalogPolyUnaryTM d C).tm.spaceUsed
      ((f2_catalogPolyUnaryTM d C).tm.initCfg x) t ≤
        (5 * (d + 1)) * (x.length + 1) := by
  let M := (f2_catalogPolyUnaryTM d C).tm
  let c := f2_catalogPolyCfg (c := d) (C := C) x (x.length + 1)
    (.loop (Fin.last d)) (fun _ => 0) []
  have hinv (u : ℕ) : (M.runFrom c u).workTapes =
      (fun _ => f2_catalogPolyTape (x.length + 1)) ∧
      f2_polyHeads (x.length + 1) (M.runFrom c u).state (M.runFrom c u).workTapePos := by
    induction u with
    | zero =>
      refine ⟨rfl, ?_⟩
      simp [c, f2_catalogPolyCfg, f2_polyHeads]
      omega
    | succ u ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step']
      exact f2_poly_step (Nat.succ_pos _) _ ih.1 ih.2
  have hpos (u : ℕ) (i : Fin (d + 1)) :
      -(2 * (x.length + 1) : ℤ) ≤ (M.runFrom (M.initCfg x) u).workTapePos i ∧
        (M.runFrom (M.initCfg x) u).workTapePos i ≤ (2 * (x.length + 1) : ℤ) := by
    by_cases hu : u ≤ 2 * (x.length + 1)
    · have h := f2_head_steps M (M.initCfg x) u i
      change 0 - (u : ℤ) ≤ _ ∧ _ ≤ 0 + (u : ℤ) at h
      constructor <;> omega
    · rw [show u = 2 * (x.length + 1) + (u - 2 * (x.length + 1)) by omega,
        MultiTapeTM.runFrom_add, f2_catalogPoly_start]
      have h := f2_polyHeads_bounds (hinv (u - 2 * (x.length + 1))).2 i
      dsimp only [c, M] at h
      constructor <;> omega
  have hcard (i : Fin (d + 1)) : M.spaceUsedByTape (M.initCfg x) t i ≤
      5 * (x.length + 1) := by
    have hsub : M.visitedByTapeHead (M.initCfg x) t i ⊆
        Finset.Icc (-(2 * (x.length + 1) : ℤ)) (2 * (x.length + 1) : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (hpos u i)
    exact (Finset.card_le_card hsub).trans (by rw [Int.card_Icc]; omega)
  change M.spaceUsed (M.initCfg x) t ≤ _
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _i : Fin (d + 1), 5 * (x.length + 1) :=
      Finset.sum_le_sum (fun i _ => hcard i)
    _ = _ := by simp; ring

/-- Increment a little-endian binary word, extending it on overflow. -/
private def f2_counterInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: f2_counterInc bs

/-- The number of initial true bits cleared by an increment. -/
private def f2_counterCarry : List Bool → ℕ
  | true :: bs => f2_counterCarry bs + 1
  | _ => 0

/-- Each cleared true bit decreases the potential by one; the final write adds one.
This is the local accounting identity behind the amortized bound. -/
private lemma f2_counterInc_potential (bs : List Bool) :
    (f2_counterInc bs).count true + f2_counterCarry bs = bs.count true + 1 := by
  induction bs with
  | nil => simp [f2_counterInc, f2_counterCarry]
  | cons b bs ih =>
    cases b with
    | false => simp [f2_counterInc, f2_counterCarry]
    | true => simp [f2_counterInc, f2_counterCarry]; omega

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma f2_counterInc_bits (n : ℕ) : f2_counterInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [f2_counterInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [f2_counterInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma f2_counterInc_length (bs : List Bool) :
    (f2_counterInc bs).length ≤ bs.length + 1 ∧
      f2_counterCarry bs ≤ (f2_counterInc bs).length := by
  induction bs with
  | nil => simp [f2_counterInc, f2_counterCarry]
  | cons b bs ih =>
    cases b <;> simp only [f2_counterInc, f2_counterCarry, List.length_cons] <;> omega

/-- One carry transition, with the first transition also advancing the input. -/
private def f2_counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- The audit's four-state counter: count = 0, carry = 1, rewind = 2, emit = 3.
[AB09, §1.3 examples], implemented by the phase-1 reaudit's transition table. -/
private def f2_counterTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), none, some 3⟩
          | some _ => f2_counterBump .pos (work 0)
        else if q = 1 then f2_counterBump .zero (work 0)
        else if q = 2 then
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .pos), none, some 0⟩
          | some _ => ⟨.zero, fun _ => (none, .neg), none, some 2⟩
        else
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .zero), none, none⟩
          | some b => ⟨.zero, fun _ => (none, .pos), some b, some 3⟩ }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def f2_counterTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, count, and emission invariants. -/
private def f2_counterCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => f2_counterTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma f2_counterTape_read (pre bs : List Bool) :
    f2_counterTape (pre ++ bs) pre.length = bs.head? := by
  simp only [f2_counterTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma f2_counterTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (f2_counterTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      f2_counterTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [f2_counterTape_read]
  · rw [Function.update_of_ne hz]
    unfold f2_counterTape
    by_cases hn : z < 0
    · simp only [if_pos hn]
    · simp only [if_neg hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_cons, if_neg (by omega), List.getElem?_tail]
        congr 1
        omega

/-- One carry transition updates exactly the currently scanned cell. -/
private lemma f2_counter_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    f2_counterTM.tm.step (f2_counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        f2_counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else f2_counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (f2_counterTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [f2_counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (f2_counterBump .zero (f2_counterTape (pre ++ bs) pre.length)).apply _ = _
  rw [f2_counterTape_read]
  unfold f2_counterBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact f2_counterTape_write pre bs _
    · funext j; simp [Action.apply, f2_counterCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma f2_counter_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    f2_counterTM.tm.runFrom (f2_counterCfg x 1 p pre.length (pre ++ bs) [])
        (f2_counterCarry bs + 1) =
      f2_counterCfg x 2 p ((pre.length : ℤ) + f2_counterCarry bs - 1)
        (pre ++ f2_counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, f2_counter_carry_step]
    simp [f2_counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, f2_counter_carry_step]
      simp [f2_counterInc]
    | true =>
      simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step, f2_counter_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [f2_counterInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the count state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma f2_counter_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    f2_counterTM.tm.runFrom (f2_counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      f2_counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, f2_counterTM, f2_counterCfg, Cfg.workTapeSymbols,
        f2_counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (f2_counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : f2_counterTM.tm.step (f2_counterCfg x 2 p (j : ℤ) bs []) =
        f2_counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (f2_counterTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [f2_counterTM, show (2 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, f2_counterCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The first carry transition also consumes exactly one input symbol. -/
private lemma f2_counter_start (x : List Bool) (i : ℕ) (hi : i < x.length) (bs : List Bool) :
    f2_counterTM.tm.step (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      f2_counterTM.tm.step (f2_counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [f2_counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (f2_counterTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [f2_counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (f2_counterBump .pos (f2_counterTape bs 0)).apply _ =
    (f2_counterBump .zero (f2_counterTape bs 0)).apply _
  unfold f2_counterBump
  by_cases h : f2_counterTape bs 0 = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val =
        (moveInputPos (⟨i + 2, by omega⟩ : Fin (x.length + 2)) 0).val
      rw [moveInputPos_zero, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rfl
    · rfl
    · rfl

/-- One complete increment takes twice the carry length plus two transitions.
**Proof sketch.** The count transition is the first carry transition, with the
input advanced once. The carry uses `r + 1` steps and leaves the head at `r - 1`;
the rewind uses another `r + 1` steps and leaves the incremented word intact. -/
private lemma f2_counter_increment (x : List Bool) (i : ℕ) (hi : i < x.length)
    (bs : List Bool) :
    f2_counterTM.tm.runFrom (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * f2_counterCarry bs + 2) =
      f2_counterCfg x 0 ⟨i + 2, by omega⟩ 0 (f2_counterInc bs) [] := by
  have hc : f2_counterTM.tm.runFrom (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
      (f2_counterCarry bs + 1) =
      f2_counterCfg x 2 ⟨i + 2, by omega⟩ ((f2_counterCarry bs : ℤ) - 1) (f2_counterInc bs) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step, f2_counter_start x i hi,
      ← MultiTapeTM.runFrom_succ_eq_step]
    simpa only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] using
      f2_counter_carry x ⟨i + 2, by omega⟩ bs []
  rw [show 2 * f2_counterCarry bs + 2 = (f2_counterCarry bs + 1) + (f2_counterCarry bs + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact f2_counter_rewind x ⟨i + 2, by omega⟩ (f2_counterInc bs) (f2_counterCarry bs)
    (f2_counterInc_length bs).2

/-- The counting invariant carries a nonnegative potential of twice the popcount.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions. -/
private lemma f2_counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) t =
        f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_⟩
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp [MultiTapeTM.initCfg, f2_counterCfg, f2_counterTape]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc⟩ := ih (by omega)
    refine ⟨t + 2 * f2_counterCarry i.bits + 2, ?_, ?_⟩
    · have hp := f2_counterInc_potential i.bits
      rw [f2_counterInc_bits] at hp
      omega
    · rw [show t + 2 * f2_counterCarry i.bits + 2 = t + (2 * f2_counterCarry i.bits + 2) by omega,
        MultiTapeTM.runFrom_add, hc, f2_counter_increment x i (by omega), f2_counterInc_bits]

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma f2_counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    f2_counterTM.tm.runFrom (f2_counterCfg x 3 p 0 bs []) i =
      f2_counterCfg x 3 p i bs (bs.take i) := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_counterCfg x 3 p i bs (bs.take i)).workTapeSymbols 0 = some bs[i] := by
      simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
        if_neg (by omega : ¬(i : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [f2_counterTM, show (3 : Fin 4) ≠ 0 from by decide,
      show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      ↓reduceIte, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · rfl
    · funext j; simp [Action.apply, f2_counterCfg]
    · simp only [Action.apply, f2_counterCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- At the first blank after the stored word, emission halts without extra output. -/
private lemma f2_counter_emit (x : List Bool) (p : Fin (x.length + 2)) (bs : List Bool) :
    let c := f2_counterTM.tm.runFrom (f2_counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (f2_counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((f2_counterTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [f2_counterTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, f2_counterCfg]

/-- The direct variable-width counter outputs the input length in at most
five times one plus that length. Its complete time proof is copied from the
explicit counter construction in ClassP/TimeConstructible.lean; no existential
witness or sharp space property of timeConstructible_id is assumed. -/
private lemma f2_counter_computes : f2_counterTM.ComputesFunInTime
    (fun x => Nat.bits x.length) (fun n => 5 * (n + 1)) := by
  intro x
  obtain ⟨t, ht, hc⟩ := f2_counter_count x x.length (le_refl _)
  have hs : f2_counterTM.tm.step
      (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    have hin : (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, f2_counterCfg]
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [f2_counterTM, Action.apply, f2_counterCfg]
  have hstart : f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) (t + 1) =
      f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  have he := f2_counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  have hbase : f2_counterTM.ComputesInTime x x.length.bits
      ((t + 1) + (x.length.bits.length + 1)) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.1
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.2
  apply hbase.mono
  have hl := Turing.length_bits_le_self x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

/-- The counting invariant also covers every suspended increment's head
trajectory. Each increment returns to the origin, and its carry length is
bounded by the final input length's binary width.
**Proof sketch.** Reuse the exact `2*carry+2` increment ledger and popcount
potential. Split each prefix at the preceding return; in the current increment
apply the unit-step trajectory bound from the origin. Binary width is monotone. -/
private lemma f2_counter_count_space (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) t =
        f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] ∧
      ∀ u ≤ t, ∀ j : Fin 1,
        -(2 * (Nat.size x.length + 1) : ℤ) ≤
          (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ∧
        (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ≤
          (2 * (Nat.size x.length + 1) : ℤ) := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_, ?_⟩
    · apply Cfg.ext
      · rfl
      · rfl
      · funext j z
        simp [MultiTapeTM.initCfg, f2_counterCfg, f2_counterTape]
      · rfl
      · rfl
    · intro u hu j
      have : u = 0 := by omega
      subst u
      simp [MultiTapeTM.initCfg, Cfg.init]
      omega
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc, hb⟩ := ih (by omega)
    refine ⟨t + (2 * f2_counterCarry i.bits + 2), ?_, ?_, ?_⟩
    · have hp := f2_counterInc_potential i.bits
      rw [f2_counterInc_bits] at hp
      omega
    · rw [MultiTapeTM.runFrom_add, hc,
        f2_counter_increment x i (by omega), f2_counterInc_bits]
    · intro u hu j
      by_cases hut : u ≤ t
      · exact hb u hut j
      · rw [show u = t + (u - t) by omega, MultiTapeTM.runFrom_add, hc]
        have hp := f2_head_steps f2_counterTM.tm
          (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits []) (u - t) j
        have hcarry := (f2_counterInc_length i.bits).2
        rw [f2_counterInc_bits, Nat.size_eq_bits_len] at hcarry
        have hwidth := Nat.size_le_size hi
        change 0 - ((u - t : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((u - t : ℕ) : ℤ) at hp
        constructor <;> omega

/-- All prefixes of the direct counter, including its stationary halted tail,
fit a fixed interval whose radius is twice one plus the final binary width.
Counting rounds return their heads to zero; final emission traverses just the
stored binary word. -/
private lemma f2_counter_heads (x : List Bool) (u : ℕ) (j : Fin 1) :
    -(2 * (Nat.size x.length + 1) : ℤ) ≤
      (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ∧
    (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ≤
      (2 * (Nat.size x.length + 1) : ℤ) := by
  obtain ⟨t, _, hc, hb⟩ := f2_counter_count_space x x.length (le_refl _)
  let c := f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits []
  have hs : f2_counterTM.tm.step
      (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) = c := by
    have hin : (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, f2_counterCfg]
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [c, f2_counterTM, Action.apply, f2_counterCfg]
  have hstart : f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) (t + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  let T := t + 1 + (x.length.bits.length + 1)
  have hhalt : (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) T).state = none := by
    rw [show T = (t + 1) + (x.length.bits.length + 1) from rfl,
      MultiTapeTM.runFrom_add, hstart]
    exact (f2_counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits).1
  have hpre (v : ℕ) (hv : v ≤ T) :
      -(2 * (Nat.size x.length + 1) : ℤ) ≤
        (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) v).workTapePos j ∧
      (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) v).workTapePos j ≤
        (2 * (Nat.size x.length + 1) : ℤ) := by
    by_cases hvt : v ≤ t
    · exact hb v hvt j
    · rw [show v = (t + 1) + (v - (t + 1)) by omega,
        MultiTapeTM.runFrom_add, hstart]
      have hp := f2_head_steps f2_counterTM.tm c (v - (t + 1)) j
      change 0 - ((v - (t + 1) : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((v - (t + 1) : ℕ) : ℤ) at hp
      have hlen := Nat.size_eq_bits_len x.length
      dsimp only [T] at hv
      constructor <;> omega
  by_cases hu : u ≤ T
  · exact hpre u hu
  · rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hhalt]
    exact hpre T (le_refl _)

/-- Taking the cardinality of the counter's inclusive trajectory interval
and summing over its single tape gives a logarithmic all-time space bound. -/
private lemma f2_counter_space (x : List Bool) (t : ℕ) :
    f2_counterTM.tm.spaceUsed (f2_counterTM.tm.initCfg x) t ≤
      5 * (Nat.size x.length + 1) := by
  have hcard (j : Fin 1) :
      f2_counterTM.tm.spaceUsedByTape (f2_counterTM.tm.initCfg x) t j ≤
        5 * (Nat.size x.length + 1) := by
    have hsub : f2_counterTM.tm.visitedByTapeHead (f2_counterTM.tm.initCfg x) t j ⊆
        Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ))
          (2 * (Nat.size x.length + 1) : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (f2_counter_heads x u j)
    exact (Finset.card_le_card hsub).trans (by rw [Int.card_Icc]; omega)
  simpa [MultiTapeTM.spaceUsed] using hcard 0

/-- Administrative actions for the captured length checker move only the
input and final (countdown) head. No tape is written. -/
private def f2_lenAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 4 ⊕ Option Bool))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 4 ⊕ Option Bool)) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture a total generator, rewind the physical input, validate its pair
syntax, then compare the suffix length with the captured word's length.
Only the final comparison or rejection transition emits a verdict. -/
private def f2_pairCountTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 4 ⊕ Option Bool)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => f2_lenAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inr none)))
        | _ => match inp with
          | none => f2_lenAction M 0 0 (some true) none
          | some _ => match work (Fin.last M.k) with
            | none => f2_lenAction M 0 0 (some false) none
            | some _ => f2_lenAction M .pos .neg none (some (.inr (.inl 3)))
      | .inr (.inr none) => match inp with
        | none => f2_lenAction M 0 0 (some false) none
        | some b => f2_lenAction M .pos 0 none (some (.inr (.inr (some b))))
      | .inr (.inr (some b)) => match inp with
        | none => f2_lenAction M 0 0 (some false) none
        | some d => if b = d then f2_lenAction M .pos 0 none (some (.inr (.inr none)))
          else if b then f2_lenAction M 0 0 (some false) none
          else f2_lenAction M .pos 0 none (some (.inr (.inl 3))) }

/-- Checker configurations retain the completed generator bank and its
captured output; `r` is the number of still available countdown cells. -/
private def f2_lenCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (f2_pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    Cfg (M.k + 1) Bool (f2_pairCountTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (f2_pairCountTM M).State))
      (.inr (.inl 0)) [] [] c with
    state := q
    inputPos := ⟨i + 1, by omega⟩
    workTapePos := fun j => if h : j.val < M.k then c.workTapePos ⟨j, h⟩
      else (r : ℤ) - 1 }

/-- The checker's input read is independent of the saved generator bank. -/
private lemma f2_lenCfg_read (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (f2_pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    (f2_lenCfg M c q i hi r).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- A stationary or forward administrative action preserves all work tapes;
its last-head movement subtracts one precisely when consuming a cell. -/
private lemma f2_lenAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (f2_pairCountTM M).State)
    (i j r s : ℕ) (hi : i ≤ x.length) (hj : j ≤ x.length)
    (m d : SignType) (b : Option Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨j + 1, by omega⟩)
    (hd : (r : ℤ) - 1 + d.cast = (s : ℤ) - 1) :
    (f2_lenAction M m d b q').apply (f2_lenCfg M c q i hi r) =
      {f2_lenCfg M c q' j hj s with output := b.toList} := by
  refine Cfg.ext rfl hm ?_ ?_ rfl
  · rfl
  · funext k
    by_cases hk : k.val < M.k
    · simp [f2_lenAction, f2_lenCfg, Action.apply, hk]
    · simpa [f2_lenAction, f2_lenCfg, Action.apply, hk] using hd

/-- Suffix comparison consumes one captured cell per input bit and emits one
verdict at termination. Empty suffixes succeed even with an empty counter.
**Proof sketch.** Induct on the suffix. A zero counter rejects a nonempty
suffix immediately; otherwise one silent step decrements both lengths. -/
private lemma f2_lenSuffix_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).state = none ∧
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).output =
          [decide (rest.length ≤ r)] := by
  induction rest with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply]
  | cons b rest ih =>
    intro pre hx r hr
    cases r with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change (((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
      rw [f2_lenCfg_read]
      simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Cfg.workTapeSymbols,
        bufferTape_left, Action.apply]
    | succ r =>
      have hs : (f2_pairCountTM M).tm.step
          (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) (r + 1)) =
          f2_lenCfg M c (some (.inr (.inl 3))) (pre.length + 1) (by simp [hx]) r := by
        unfold MultiTapeTM.step
        change ((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _ = _
        rw [f2_lenCfg_read]
        have hin : x[pre.length]? = some b := by simp [hx]
        have hw : (f2_lenCfg M c (some (.inr (.inl 3))) pre.length
            (by simp [hx]) (r + 1)).workTapeSymbols (Fin.last M.k) =
              some (c.output[r]'(by omega)) := by
          simp [f2_lenCfg, captureCfg, Cfg.workTapeSymbols, bufferTape,
            List.getElem?_eq_getElem (by omega : r < c.output.length)]
        simp only [f2_pairCountTM, hin, hw]
        exact f2_lenAction_apply M c _ _ pre.length (pre.length + 1) (r + 1) r
          (by simp [hx]) (by simp [hx]) .pos .neg none
          (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast]; omega)
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [b]) (by simpa [List.append_assoc] using hx)
        r (by omega)
      refine ⟨1 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add]
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      rw [hs]
      simpa using And.intro hh ho

/-- The first half of an aligned block changes only finite control and the
input position; countdown cells remain untouched during validation. -/
private lemma f2_lenParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b : Bool) (r : ℕ)
    (hx : x = pre ++ b :: rest) :
    (f2_pairCountTM M).tm.step
      (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) =
      f2_lenCfg M c (some (.inr (.inr (some b)))) (pre.length + 1) (by simp [hx]) r := by
  unfold MultiTapeTM.step
  change ((f2_pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _ = _
  rw [f2_lenCfg_read]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [f2_pairCountTM, hin]
  exact f2_lenAction_apply M c _ _ pre.length (pre.length + 1) r r
    (by simp [hx]) (by simp [hx]) .pos 0 none
    (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast])

/-- Two parser steps either advance over a doubled bit, enter the suffix
comparison at `01`, or reject `10`. Nothing is emitted on a valid block. -/
private lemma f2_lenParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b d : Bool) (r : ℕ)
    (hx : x = pre ++ b :: d :: rest) :
    (f2_pairCountTM M).tm.runFrom
      (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) 2 =
      if b = d then f2_lenCfg M c (some (.inr (.inr none)))
          (pre.length + 2) (by simp [hx]) r
      else if b then {f2_lenCfg M c none (pre.length + 1) (by simp [hx]) r with output := [false]}
      else f2_lenCfg M c (some (.inr (.inl 3))) (pre.length + 2) (by simp [hx]) r := by
  change (f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _) = _
  rw [f2_lenParse_first M c pre (d :: rest) b r hx]
  unfold MultiTapeTM.step
  change ((f2_pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _ = _
  rw [f2_lenCfg_read]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  rw [hin]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases d <;>
    simp only [f2_pairCountTM, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals first
    | exact f2_lenAction_apply M c _ _ (pre.length + 1) (pre.length + 2) r r
        (by simp [hx]) (by simp [hx]) .pos 0 none hm (by simp [SignType.cast])
    | exact f2_lenAction_apply M c _ _ (pre.length + 1) (pre.length + 1) r r
        (by simp [hx]) (by simp [hx]) 0 0 (some false)
        (moveInputPos_zero _) (by simp [SignType.cast])

/-- Aligned validation followed by countdown comparison decides the payload
bound in at most one more than the unread input length.
**Proof sketch.** Induct over two-bit blocks, using the existing parser's
same grammar and induction pattern. Equal-bit blocks preserve the counter;
`01` invokes suffix comparison; malformed endings and `10` reject. -/
private lemma f2_lenParse_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).state = none ∧
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).output =
          [match pairDecode rest with
            | some (_, b) => decide (b.length ≤ r)
            | none => false] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply, pairDecode]
  | singleton b =>
    intro pre hx r hr
    refine ⟨2, by simp, ?_⟩
    change ((f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _)).state = none ∧
      ((f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _)).output = _
    rw [f2_lenParse_first M c pre [] b r hx]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    cases b <;> simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply, pairDecode]
  | cons_cons b d rest ih _ =>
    intro pre hx r hr
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b])
        (by simpa [List.append_assoc] using hx) r hr
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_lenParse_block M c pre rest b b r hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd] using ho
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := f2_lenSuffix_run M c rest (pre ++ [false, true])
          (by simpa [List.append_assoc] using hx) r hr
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, f2_lenParse_block M c pre rest false true r hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [f2_lenParse_block M c pre rest true false r hx]
        simp [f2_lenCfg, pairDecode]
      · exact False.elim (h rfl)

/-- Quantitative input rewind, adapted from the wrapper controller's proved
`timed_rewind` pattern using the public `rewind_scan` interface.
**Proof sketch.** One mandatory left move is followed by exactly the new
position plus one scan steps. Work tapes and output are preserved. -/
private lemma f2_catalogRewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- A completed generator is captured without physical output, then its
last cell and the first physical input cell are exposed for comparison.
**Proof sketch.** Use the least source halting time to discharge `capture_run`'s
liveness guard. One step moves the capture head left; quantitative rewind
restores the input head while preserving the completed generator bank. -/
private lemma f2_lenStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + x.length + 4, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (f2_pairCountTM M).tm.runFrom ((f2_pairCountTM M).tm.initCfg x) t =
        f2_lenCfg M c (some (.inr (.inr none))) 0 (by omega) c.output.length := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (f2_pairCountTM M).State := Sum.inl
  let ret : (f2_pairCountTM M).State := .inr (.inl 0)
  have hinit : (f2_pairCountTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (f2_pairCountTM M).tm.runFrom ((f2_pairCountTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (f2_pairCountTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  let ready : Cfg (M.k + 1) Bool (f2_pairCountTM M).State x :=
    {f2_lenCfg M c (some (.inr (.inl 1))) 0 (by omega) c.output.length with
      inputPos := c.inputPos}
  have hback : (f2_pairCountTM M).tm.step (captureCfg emb ret [] [] c) = ready := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      by_cases hi : i.val < M.k <;>
        simp [f2_pairCountTM, ret, f2_lenAction, Action.apply, captureCfg, ready, f2_lenCfg, hi,
          sub_eq_add_neg]
    · rfl
  obtain ⟨r, hrle, hr⟩ := f2_catalogRewind (f2_pairCountTM M).tm
    (.inr (.inl 1)) (.inr (.inl 2)) (some (.inr (.inr none)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) ready rfl
  refine ⟨t + 1 + r, ?_, c, ho, ?_⟩
  · change r ≤ c.inputPos.val + 2 at hrle
    have := c.inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [hback, hr]
    rfl

/-- The captured checker compares a valid pair's payload with the length of
the generator's output, and rejects every malformed input.
**Proof sketch.** Compose the silent capture/rewind prefix with the aligned
parser and countdown ledger, then absorb the two linear scans. -/
private lemma f2_pairCount_computes {M : FinTM Bool} {g : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime g T) :
    (f2_pairCountTM M).ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false]) (fun n => T n + 2 * n + 5) := by
  intro x
  obtain ⟨t, ht, c, ho, hstart⟩ := f2_lenStart M x (g x) (T x.length) (hM x)
  obtain ⟨r, hr, hs, hout⟩ := f2_lenParse_run M c x [] rfl c.output.length (le_refl _)
  have hc : (f2_pairCountTM M).ComputesInTime x
      [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false] (t + r) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, by simpa only [ho] using hout⟩
  exact hc.mono (by dsimp only; omega)

/-- A successful aligned parse reconstructs the input's exact encoding.
**Proof sketch.** Induct over two-bit blocks: equal bits prepend one decoded
bit; the separator exposes the entire remaining suffix. -/
private lemma f2_catalogPair_inverse (x : List Bool) :
    ∀ a v, pairDecode x = some (a, v) → x = pairEncode a v := by
  induction x using List.twoStepInduction with
  | nil => intro a v h; simp [pairDecode] at h
  | singleton b => intro a v h; cases b <;> simp [pairDecode] at h
  | cons_cons b d rest ih _ =>
    intro a v h
    cases b <;> cases d
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      rcases p with ⟨u, w⟩
      cases he
      rw [ih u w hp]
      rfl
    · cases h; rfl
    · simp [pairDecode] at h
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      rcases p with ⟨u, w⟩
      cases he
      rw [ih u w hp]
      rfl

/-- Every all-time head position of a halted computation already occurs before
its time bound. Taking the image of that finite prefix gives at most `T+1`
cells per tape, including the initial cell.
**Proof sketch.** For a later time, split the run at `T` and use halt absorption;
for an earlier time use the same time index. Take cardinalities and sum. -/
private lemma f2_space_of_time {M : FinTM Bool} {x y : List Bool} {T : ℕ}
    (h : M.ComputesInTime x y T) (t : ℕ) :
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (T + 1) := by
  have hh := ((computesInTime_iff _ _ _ _).mp h).1
  have hsub (i : Fin M.k) :
      M.tm.visitedByTapeHead (M.tm.initCfg x) t i ⊆
        M.tm.visitedByTapeHead (M.tm.initCfg x) T i := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
    by_cases hu : u ≤ T
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩
    · have hr : M.tm.runFrom (M.tm.initCfg x) u =
          M.tm.runFrom (M.tm.initCfg x) T := by
        rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_of_halt _ hh]
      exact Finset.mem_image.mpr ⟨T, Finset.mem_range.mpr (by omega),
        congrArg (fun c => c.workTapePos i) hr.symm⟩
  calc
    _ ≤ ∑ _i : Fin M.k, (T + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_le_card (hsub i)).trans (by
        unfold MultiTapeTM.visitedByTapeHead
        exact (Finset.card_image_le).trans (by rw [Finset.card_range]))
    _ = _ := by simp

/-- **P1 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.computesFunInTime_id`). The copy machine runs in
constant work-tape space: one witness does the whole job on its input and
output heads alone.

**Proof sketch.** The existing witness `idTM` has no work tapes, so every
`spaceUsed` value is `0`; re-exhibit it and join the audited time
contract with the constant bound. -/
theorem computesFunInTime_id_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime id (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_idTM, 1, ?_, ?_⟩
  · intro x
    obtain ⟨hstate, hpos, hout⟩ := f2_idTM_run x x.length (le_refl _)
    have h0 : (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).inputPos ≠ 0 := by
      intro h
      rw [h] at hpos
      simp at hpos
    have hsym : (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).inputSymbol = none := by
      unfold Cfg.inputSymbol
      rw [dif_neg h0, dif_pos (by omega)]
    have hrun1 : f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) (x.length + 1) =
        (f2_idTM.tm.tr () none
          ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).workTapeSymbols)).apply
          (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [hsym]
    have hbase : f2_idTM.ComputesInTime x x (x.length + 1) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hrun1]
        simp [f2_idTM, Action.apply]
      · rw [hrun1]
        simp only [f2_idTM, Action.apply]
        rw [hout]
        simp
    exact hbase.mono (le_of_eq (one_mul _).symm)
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P2 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_const`). The fixed-word emission chain
runs in constant work-tape space.

**Proof sketch.** The existing witness `constTM w` is a zero-work-tape
emission chain, so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_const_spaceUsed (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun _ => w) (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_constTM w, w.length + 1, ?_, ?_⟩
  · intro x
    obtain ⟨hs, ho⟩ := emit_halts (f2_constTM w).tm w id (fun _ _ _ => rfl)
      ((f2_constTM w).tm.initCfg x) rfl
    have hbase : (f2_constTM w).ComputesInTime x w (w.length + 1) := by
      exact ⟨_, hs, by simpa only [MultiTapeTM.initCfg, Cfg.init, List.nil_append] using ho, rfl⟩
    exact hbase.mono (Nat.le_mul_of_pos_right _ (by omega))
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P3 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_prepend`). Prepending a fixed word runs
in constant work-tape space: an emission chain followed by the input
copy scan never moves a work head.

**Proof sketch.** The existing witness `catalogPrefixTM` has no work-tape
movement (head-movement count zero on every phase), so each visited set
is the origin singleton and the total is the tape count, a machine
constant absorbed into `c`. -/
theorem computesFunInTime_prepend_spaceUsed (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => w ++ x) (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_catalogPrefixTM w, w.length + 1, ?_, ?_⟩
  · intro x
    apply (f2_catalogPrefixTM_computes w x).mono
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P4 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_lengthBits`). The binary length counter
runs in logarithmic work-tape space: the counter word has `Nat.size n`
bits and the scan never leaves its interval (the sharp clause the
chapter-4 campaign consumes).

**Proof sketch.** The witness drives an in-place binary counter on one
work tape (the `Turing.incFixed` carry discipline): its head stays within
the counter interval `[-1, Nat.size n + 1]`, whose visit count the carry
head-movement bounds; constants absorb the boundary cells. -/
theorem computesFunInTime_lengthBits_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits x.length)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (Nat.size x.length + 1) := by
  exact ⟨f2_counterTM, 5, f2_counter_computes, f2_counter_space⟩

/-- **P5 space row, unary clause** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_polyUnary`). The unary
polynomial generator runs in linear work-tape space: each of its `e`
nested loop tapes holds a unary counter of side `n + 1`.

**Proof sketch.** Head-movement count per loop tape: installed by one
input scan and bounded by the box side `n + 1`, revisited in place
across iterations — per-tape visited sets lie in `[-1, n + 1]`, and the
tape count depends only on `e`, absorbed into `c`. -/
theorem computesFunInTime_polyUnary_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  cases e with
  | zero =>
    obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (List.replicate C true)
    refine ⟨M, c, by simpa using ht, ?_⟩
    intro x t
    exact (hs x t).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  | succ d =>
    refine ⟨f2_catalogPolyUnaryTM d C, C + 10 * (d + 1) + 4, ?_, ?_⟩
    · intro x
      apply (f2_catalogPoly_unary_computes d C x).mono
      apply Nat.mul_le_mul
      · omega
      · exact Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    · intro x t
      exact (f2_poly_space d C x t).trans
        (Nat.mul_le_mul_right (x.length + 1) (by omega))

/-- **P5 space row, binary clause** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_polyBits`). The binary
polynomial evaluator runs in linear work-tape space: it is the unary
generator buffered into the length counter, and the buffer tape holds
the unary intermediate — the linear clause is the witness family's
honest bound (a logarithmic-space evaluator would be a new machine, out
of this increment's scope; recorded as a deviation from the sharpest
conceivable form).

**Proof sketch.** Split on the coefficient and exponent (round-1
finding 5 — the unqualified buffered-generator route fails at `C = 0`,
where the old generator still initializes length-`n + 1` unary banks
against a constant bound): for `C = 0`, and likewise for `e = 0`, the
witness is the constant-output family (zero work tapes, constant
space); for `C > 0` and `e > 0`, where `n + 1 ≤ C·(n+1)^e`, the buffered
composition's buffer holds the unary intermediate of length
`C·(n+1)^e`, the generator's banks are linear, and the counter is
logarithmic — all inside the stated value-linear bound. -/
theorem computesFunInTime_polyBits_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (C * (x.length + 1) ^ e + 1) := by
  by_cases hC : C = 0
  · subst C
    obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (Nat.bits 0)
    refine ⟨M, c, ?_, ?_⟩
    · intro x
      simpa only [Nat.zero_mul] using (ht x).mono
        (Nat.mul_le_mul_left c (by
          simpa only [Nat.pow_one] using
            Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)))
    · simpa using hs
  · cases e with
    | zero =>
      obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (Nat.bits C)
      refine ⟨M, c, by simpa using ht, ?_⟩
      intro x t
      simpa using (hs x t).trans (Nat.le_mul_of_pos_right c (Nat.succ_pos C))
    | succ d =>
      let A := C + 5 * (d + 1) + 4
      let K := A + 6 * C + 7
      let M := bufferedCompTM (f2_catalogPolyUnaryTM d C) f2_counterTM
      have ht : M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ (d + 1)))
          (fun n => K * (n + 1) ^ (d + 1)) := by
        intro x
        have h := bufferedCompTM_computesInTime
          (f2_catalogPolyUnaryTM d C) f2_counterTM
          (f2_catalogPoly_unary_computes d C x)
          (f2_counter_computes (List.replicate (C * (x.length + 1) ^ (d + 1)) true))
        simp only [List.length_replicate] at h
        apply h.mono
        have hp := Nat.one_le_pow (d + 1) (x.length + 1) (Nat.succ_pos _)
        change A * (x.length + 1) ^ (d + 1) + C * (x.length + 1) ^ (d + 1) + 2 +
          5 * (C * (x.length + 1) ^ (d + 1) + 1) ≤ K * (x.length + 1) ^ (d + 1)
        have hseven := Nat.mul_le_mul_left 7 hp
        calc
          _ = (A + 6 * C) * (x.length + 1) ^ (d + 1) + 7 := by ring
          _ ≤ (A + 6 * C) * (x.length + 1) ^ (d + 1) +
              7 * (x.length + 1) ^ (d + 1) := Nat.add_le_add_left hseven _
          _ = _ := by dsimp only [K]; ring
      refine ⟨M, M.k * (K + 1) + K, ?_, ?_⟩
      · intro x
        apply (ht x).mono
        exact Nat.mul_le_mul (by omega)
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      · intro x t
        have h := f2_space_of_time (ht x) t
        have hp : (x.length + 1) ^ (d + 1) ≤ C * (x.length + 1) ^ (d + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        have hb : K * (x.length + 1) ^ (d + 1) + 1 ≤
            (K + 1) * (C * (x.length + 1) ^ (d + 1) + 1) := by
          have hh := Nat.mul_le_mul_left K hp
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          omega
        exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))

/-- **P6 space row, fixed-first-component encoder** (spec, fill pending —
design §12 R3; annotates `Turing.FinTM.computesFunInTime_pairEncodeFixed`).
Pairing with a fixed first component runs in constant work-tape space: it
is the prepend row at the doubled fixed word.

**Proof sketch.** Same witness route as
`computesFunInTime_prepend_spaceUsed` at the word
`(α doubled) ++ [false, true]`: no work-head movement at all. -/
theorem computesFunInTime_pairEncodeFixed_spaceUsed (α : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode α x)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  simpa only [pairEncode] using
    computesFunInTime_prepend_spaceUsed ((α.flatMap fun b => [b, b]) ++ [false, true])

/-- **P6 space row, first extraction** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairFst`). The
first-component extractor runs in linear work-tape space: the aligned
scan buffers the undoubled prefix before any emission.

**Proof sketch.** The witness's single work tape holds the undoubled
prefix, of length at most half the input; its head walks the buffer
forward once and replays it once, so the visited set lies in
`[-1, n + 1]`. -/
theorem computesFunInTime_pairFst_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM true false, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes true false x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes true false x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P6 space row, second extraction** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairSnd`). The
second-component extractor runs in linear work-tape space (it shares the
buffered parser with the first extractor).

**Proof sketch.** As `computesFunInTime_pairFst_spaceUsed`: one buffer
tape of at most the input length, walked forward and replayed once. -/
theorem computesFunInTime_pairSnd_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM false true, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes false true x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes false true x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P6 space row, validity test** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_pairValid`). The grammar
validity test runs in constant work-tape space: alignment is finite
control, nothing is buffered.

**Proof sketch.** The existing witness `pairValidTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_pairValid_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [(pairDecode x).isSome])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_pairValidTM, 1, ?_, ?_⟩
  · intro x
    simpa using f2_pairValid_computes x
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P13 space row, pair to concatenation** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_pairConcat`). The
concatenation extractor runs in linear work-tape space.

**Proof sketch.** The shared buffered parser again: one buffer tape
holding the undoubled prefix, walked forward and replayed once before
the suffix copy. -/
theorem computesFunInTime_pairConcat_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => a ++ b
          | none => [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM true true, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes true true x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes true true x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P14 space row, pair duplication** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairDup`). The duplication
encoder runs in constant work-tape space: both passes re-read the input
tape, nothing is buffered.

**Proof sketch.** The existing witness `pairDupTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_pairDup_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode x x)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_pairDupTM, 4, f2_pairDup_computes, ?_⟩
  intro x t
  rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
  omega

/-- The unary generator's received time proof has the sharper degree `e`;
only the fixed-output case needs the separate linear allowance. -/
private lemma f2_unary_sharp (C e : ℕ) :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        (fun n => a * ((n + 1) ^ e + n + 1)) := by
  cases e with
  | zero =>
    obtain ⟨M, a, ht, _⟩ := computesFunInTime_const_spaceUsed (List.replicate C true)
    refine ⟨M, a, ?_⟩
    intro x
    simpa only [Nat.pow_zero, Nat.mul_one] using
      (ht x).mono (Nat.mul_le_mul_left a (by omega : x.length + 1 ≤ 1 + x.length + 1))
  | succ d =>
    refine ⟨f2_catalogPolyUnaryTM d C, C + 5 * (d + 1) + 4, ?_⟩
    intro x
    exact (f2_catalogPoly_unary_computes d C x).mono
      (Nat.mul_le_mul_left _ (by omega))

/-- The decoded first component is no longer than the original encoding;
a malformed encoding extracts the empty word. -/
private lemma f2_first_length (x : List Bool) :
    (((pairDecode x).map Prod.fst).getD []).length ≤ x.length := by
  cases hd : pairDecode x with
  | none => simp
  | some ab =>
    rcases ab with ⟨a, b⟩
    simp only [Option.map_some, Option.getD_some]
    rw [f2_catalogPair_inverse x a b hd, length_pairEncode]
    omega

/-- **P8 space row, threaded length check** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_pairLenCheck`). The
threaded length checker's space is dominated by the unary polynomial
bank `C·(|a|+1)^e` it counts down against, plus the linear parse
buffers.

**Proof sketch.** Head-movement count per stage: the extractor buffers at
most `n` cells, the unary generator's bank holds `C·(|a|+1)^e ≤
C·(n+1)^e` cells, and the countdown walks that bank in place; boundary
cells and the stage count go into `c`. -/
theorem computesFunInTime_pairLenCheck_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => [match pairDecode x with
          | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
          | none => false])
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ c * ((x.length + 1) ^ e + x.length + 1) := by
  obtain ⟨U, a, hU⟩ := f2_unary_sharp C e
  let G := bufferedCompTM (f2_pairExtractTM true false) U
  have hF : (f2_pairExtractTM true false).ComputesFunInTime
      (fun x => ((pairDecode x).map Prod.fst).getD []) (fun n => 5 * (n + 1)) := by
    intro x
    have h := f2_pairExtract_computes true false x
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some ab => cases ab; simpa [hd] using h
  have hG : G.ComputesFunInTime
      (fun x => List.replicate (C * ((((pairDecode x).map Prod.fst).getD []).length + 1) ^ e) true)
      (fun n => (a + 8) * ((n + 1) ^ e + n + 1)) := by
    intro x
    have hlen := f2_first_length x
    have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) e
    have hu := (hU (((pairDecode x).map Prod.fst).getD [])).mono
      (Nat.mul_le_mul_left a (Nat.add_le_add_right (Nat.add_le_add hpow hlen) 1))
    have h := bufferedCompTM_computesInTime _ _ (hF x) hu
    apply h.mono
    have hp := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
    simp only [Nat.add_mul]
    omega
  let M := f2_pairCountTM G
  let K := a + 13
  have ht : M.ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (u, v) => decide (v.length ≤ C * (u.length + 1) ^ e)
        | none => false])
      (fun n => K * ((n + 1) ^ e + n + 1)) := by
    intro x
    have h := f2_pairCount_computes hG x
    have htime : (a + 8) * ((x.length + 1) ^ e + x.length + 1) + 2 * x.length + 5 ≤
        K * ((x.length + 1) ^ e + x.length + 1) := by
      dsimp only [K]
      simp only [Nat.add_mul]
      omega
    have h' := h.mono htime
    cases hd : pairDecode x with
    | none => simpa [hd] using h'
    | some uv => cases uv; simpa [hd] using h'
  refine ⟨M, 2 * K + M.k * (K + 1), ?_, ?_⟩
  · intro x
    apply (ht x).mono
    have hp : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hn : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
      simpa only [Nat.pow_one] using
        Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
    calc
      K * ((x.length + 1) ^ e + x.length + 1) ≤
          K * (2 * (x.length + 1) ^ (e + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * K) * (x.length + 1) ^ (e + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · intro x t
    have h := f2_space_of_time (ht x) t
    have hb : K * ((x.length + 1) ^ e + x.length + 1) + 1 ≤
        (K + 1) * ((x.length + 1) ^ e + x.length + 1) := by
      calc
        _ ≤ K * ((x.length + 1) ^ e + x.length + 1) +
            ((x.length + 1) ^ e + x.length + 1) := by omega
        _ = _ := by ring
    exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

/- Local copies of the received raw-strip and guard witnesses. -/
/-- Copy the physical input, erase its final false-run and last true, rewind,
then replay. An all-false input halts silently during the reverse scan. -/
private def f2_rawStripTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match inp with
        | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 1⟩
      | 1 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), none, none⟩
        | some b => ⟨0, fun _ => (some none, .neg), none, some (if b then 2 else 1)⟩
      | 2 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some 2⟩
        | none => ⟨0, fun _ => (none, .pos), none, some 3⟩
      | _ => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some 3⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Raw-strip configurations expose the indexed input and a contiguous buffer. -/
private def f2_stripCfg (x : List Bool) (q : Option (Fin 4)) (i : ℕ) (hi : i ≤ x.length)
    (w : List Bool) (h : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape w, fun _ => h, out⟩

/-- Erasing the last written cell restores exactly the shorter buffer. -/
private lemma f2_catalogBuffer_erase (w : List Bool) (b : Bool) :
    Function.update (bufferTape (w ++ [b])) (w.length : ℤ) none = bufferTape w := by
  rw [bufferTape_append, Function.update_idem]
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp
  · simp [Function.update_of_ne hz]

/-- The forward copy is silent and installs exactly the scanned input prefix.
**Proof sketch.** One input step appends the next bit at the buffer's right
blank; the input and work heads both advance once. -/
private lemma f2_rawStrip_copy (x : List Bool) : ∀ j (hj : j ≤ x.length),
    f2_rawStripTM.tm.runFrom (f2_rawStripTM.tm.initCfg x) j =
      f2_stripCfg x (some 0) j hj (x.take j) j [] := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext <;> simp [f2_rawStripTM, f2_stripCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (f2_stripCfg x (some 0) j (by omega) (x.take j) j []).inputSymbol =
        some (x[j]'(by omega)) := inputSymbolInner j (by simp [f2_stripCfg]; omega) (by omega)
    unfold MultiTapeTM.step
    change (f2_rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    refine Cfg.ext rfl (moveInputPos_pos_of_ne_right _ (by simp [f2_stripCfg]; omega)) ?_ ?_ rfl
    · funext k
      change Function.update (bufferTape (x.take j)) (j : ℤ) (some (x[j]'(by omega))) =
        bufferTape (x.take (j + 1))
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simpa only [List.length_take, Nat.min_eq_left (by omega : j ≤ x.length)] using
        (bufferTape_append (x.take j) (x[j]'(by omega))).symm
    · funext k; simp [f2_rawStripTM, f2_stripCfg, Action.apply]

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma f2_rawStrip_rewind (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    f2_rawStripTM.tm.runFrom
      (f2_stripCfg x (some 2) i hi a ((j : ℤ) - 1) []) (j + 1) =
      f2_stripCfg x (some 3) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : f2_rawStripTM.tm.step
        (f2_stripCfg x (some 2) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_stripCfg x (some 2) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay appends exactly the visited buffer prefix and preserves its tape.
**Proof sketch.** The same replay invariant as the shared extractor: induct
on the number of visited cells and use the next-prefix equation for lists. -/
private lemma f2_rawStrip_replay (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j (_hj : j ≤ a.length),
    f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 3) i hi a 0 []) j =
      f2_stripCfg x (some 3) i hi a j (a.take j) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change a.take j ++ [a[j]'(by omega)] = a.take (j + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl

/-- Rewind followed by replay halts with exactly the retained buffer.
**Proof sketch.** The rewind costs `|a|+1`; replay and its final blank test
cost another `|a|+1`, and no earlier phase has emitted anything. -/
private lemma f2_rawStrip_finish (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).state = none ∧
    (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).output = a := by
  have htime : 2 * (a.length + 1) = (a.length + 1) + (a.length + 1) := by omega
  rw [htime, MultiTapeTM.runFrom_add, f2_rawStrip_rewind x a i hi a.length (le_refl _),
    MultiTapeTM.runFrom_succ_eq_step', f2_rawStrip_replay x a i hi a.length (le_refl _)]
  simp [MultiTapeTM.step, f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, Action.apply]

/-- The reverse phase erases the last cell and moves left, branching to
replay preparation precisely when the erased bit is true. -/
private lemma f2_rawStrip_erase (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) (b : Bool) :
    f2_rawStripTM.tm.step
      (f2_stripCfg x (some 1) i hi (w ++ [b]) ((w ++ [b]).length - 1) []) =
      f2_stripCfg x (some (if b then 2 else 1)) i hi w (w.length - 1) [] := by
  have hz : (((w ++ [b]).length : ℕ) : ℤ) - 1 = w.length := by simp
  rw [hz]
  unfold MultiTapeTM.step
  simp only [f2_stripCfg, f2_rawStripTM, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_append_right (by omega : w.length ≤ w.length), Nat.sub_self,
    List.getElem?_cons_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext k; exact f2_catalogBuffer_erase w b
  · funext k; simp [Action.apply, sub_eq_add_neg]

/-- Reverse erasure implements `splitAtLastTrue` exactly, including rejection
of every all-false word.
**Proof sketch.** Induct from the right. A final false is erased and the
induction continues. A final true is erased and the retained prefix is
rewound and replayed. These are exactly the `reverse.dropWhile` equations. -/
private lemma f2_rawStrip_trim (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∃ t ≤ 3 * (w.length + 1),
      (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 1) i hi w (w.length - 1) []) t).state = none ∧
      (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 1) i hi w (w.length - 1) []) t).output =
        (splitAtLastTrue w).getD [] := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, f2_rawStripTM, f2_stripCfg,
      Cfg.workTapeSymbols, Action.apply, splitAtLastTrue]
  | append_singleton w b ih =>
    cases b with
    | false =>
      obtain ⟨t, ht, hs, ho⟩ := ih
      refine ⟨t + 1, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_rawStrip_erase]
      exact ⟨hs, by simpa [splitAtLastTrue] using ho⟩
    | true =>
      refine ⟨2 * (w.length + 1) + 1,
        by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_rawStrip_erase]
      simpa [splitAtLastTrue] using f2_rawStrip_finish x w i hi

/-- Raw marker stripping runs in linear time, with physical output delayed
until the last true has been located and removed.
**Proof sketch.** Copy in `|x|+1` steps, including the right-blank turn;
the reverse/replay ledger uses at most another `3(|x|+1)` steps. -/
private lemma f2_rawStrip_computes : f2_rawStripTM.ComputesFunInTime
    (fun x => (splitAtLastTrue x).getD []) (fun n => 4 * (n + 1)) := by
  intro x
  have hstart : f2_rawStripTM.tm.runFrom (f2_rawStripTM.tm.initCfg x) (x.length + 1) =
      f2_stripCfg x (some 1) x.length (le_refl _) x (x.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_rawStrip_copy x x.length (le_refl _)]
    have hin : (f2_stripCfg x (some 0) x.length (le_refl _) (x.take x.length) x.length []).inputSymbol =
        none := by simp [f2_stripCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (f2_rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [f2_rawStripTM, f2_stripCfg, Action.apply, sub_eq_add_neg]
  obtain ⟨t, ht, hs, ho⟩ := f2_rawStrip_trim x x x.length (le_refl _)
  have hc : f2_rawStripTM.ComputesInTime x ((splitAtLastTrue x).getD []) (x.length + 1 + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, ho⟩
  exact hc.mono (by dsimp only; omega)

/-- A finite scanner emits whether its input contains a true bit. -/
private def f2_anyTrueTM : FinTM Bool where
  k := 0
  State := Unit
  tm := {
    q₀ := ()
    tr := fun _ inp _ => match inp with
      | some false => ⟨.pos, fun i => i.elim0, none, some ()⟩
      | some true => ⟨0, fun i => i.elim0, some true, none⟩
      | none => ⟨0, fun i => i.elim0, some false, none⟩ }

/-- The marker-existence scan halts within one more than the remaining length.
**Proof sketch.** False bits advance silently; a true or the right boundary
emits the corresponding verdict and halts. -/
private lemma f2_anyTrue_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (f2_anyTrueTM.tm.runFrom (f2_scanCfg x (some ()) pre.length (by simp [hx]) []) t).state = none ∧
      (f2_anyTrueTM.tm.runFrom (f2_scanCfg x (some ()) pre.length (by simp [hx]) []) t).output =
        [rest.any id] := by
  induction rest with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    simp [hx, f2_anyTrueTM, Action.apply, f2_scanCfg]
  | cons b rest ih =>
    intro pre hx
    cases b with
    | true =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change ((f2_anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
      rw [f2_scanCfg_read]
      simp [hx, f2_anyTrueTM, Action.apply, f2_scanCfg]
    | false =>
      have hs := f2_scanStep_right f2_anyTrueTM.tm x () (some ()) pre.length (by simp [hx]) [] none
        (by intro work; simp [hx, f2_anyTrueTM])
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [false]) (by simpa [List.append_assoc] using hx)
      refine ⟨t + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, hs]
      simpa using And.intro hh ho

/-- The true-bit scanner starts at the first input cell and uses a linear bound. -/
private lemma f2_anyTrue_computes : f2_anyTrueTM.ComputesFunInTime
    (fun x => [x.any id]) (fun n => n + 1) := by
  intro x
  obtain ⟨t, ht, hs, ho⟩ := f2_anyTrue_run x x [] rfl
  have hinit : f2_anyTrueTM.tm.initCfg x = f2_scanCfg x (some ()) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hc : f2_anyTrueTM.ComputesInTime x [x.any id] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact hc.mono ht

/-- Marker absence is exactly the false verdict; a present marker can be
stripped after any fixed prefix without disturbing that prefix.
**Proof sketch.** Right induction follows `reverse.dropWhile`: append-false
preserves the previous result, and append-true selects the whole old word. -/
private lemma f2_catalogMarker_cases (v : List Bool) :
    (v.any id = false ∧ splitAtLastTrue v = none) ∨
      ∃ u, v.any id = true ∧ splitAtLastTrue v = some u ∧
        ∀ pre, splitAtLastTrue (pre ++ v) = some (pre ++ u) := by
  induction v using List.reverseRecOn with
  | nil => left; simp [splitAtLastTrue]
  | append_singleton v b ih =>
    cases b with
    | false =>
      rcases ih with ⟨ha, hs⟩ | ⟨u, ha, hs, hp⟩
      · left; simpa [splitAtLastTrue] using And.intro ha hs
      · right
        refine ⟨u, by simpa using ha, by simpa [splitAtLastTrue] using hs, ?_⟩
        intro pre
        simpa [splitAtLastTrue, List.append_assoc] using hp pre
    | true =>
      right
      refine ⟨v, by simp, by simp [splitAtLastTrue], ?_⟩
      intro pre
      simp [splitAtLastTrue]

private lemma f2_strip_linear :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        fun n => c * (n + 1) := by
  obtain ⟨S, a, hS, _⟩ := computesFunInTime_pairSnd_spaceUsed
  obtain ⟨D, b, hD⟩ := computesFunInTime_comp hS f2_anyTrue_computes
    (by intro m n h; exact Nat.add_le_add_right h 1)
  have hD' : D.ComputesFunInTime
      (fun x => [((pairDecode x).map Prod.snd |>.getD []).any id])
      (fun n => b * (a * (n + 1) + (a * (n + 1) + 1) + 1)) := by
    simpa only [Function.comp_apply] using hD
  obtain ⟨E, c, hE, _⟩ := computesFunInTime_const_spaceUsed ([] : List Bool)
  obtain ⟨M, d, hM⟩ := computesFunInTime_cond hD' f2_rawStrip_computes hE
  refine ⟨M, d * (2 * b * (a + 1) + (4 + c) + 1), fun x => ?_⟩
  have hh : M.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => match splitAtLastTrue v with
          | some w => pairEncode u w
          | none => []
        | none => [])
      (d * (b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
        max (4 * (x.length + 1)) (c * (x.length + 1)) + 1)) := by
    have hm := hM x
    cases hd : pairDecode x with
    | none => simpa [hd] using hm
    | some uv =>
      rcases uv with ⟨u, v⟩
      rcases f2_catalogMarker_cases v with ⟨ha, hs⟩ | ⟨w, ha, hs, hp⟩
      · simpa [hd, ha, hs] using hm
      · have hx : splitAtLastTrue x = some (pairEncode u w) := by
          rw [f2_catalogPair_inverse x u v hd]
          exact hp _
        simpa [hd, ha, hs, hx] using hm
  apply hh.mono
  have hbase : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  have hg : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) ≤
      (2 * b * (a + 1)) * (x.length + 1) := by
    calc
      _ = (2 * b) * (a * (x.length + 1) + 1) := by ring
      _ ≤ (2 * b) * ((a + 1) * (x.length + 1)) := Nat.mul_le_mul_left _ hbase
      _ = _ := by ring
  have hm : max (4 * (x.length + 1)) (c * (x.length + 1)) ≤
      (4 + c) * (x.length + 1) := by
    apply max_le
    · exact Nat.mul_le_mul_right _ (by omega)
    · exact Nat.mul_le_mul_right _ (by omega)
  have hb : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
      max (4 * (x.length + 1)) (c * (x.length + 1)) + 1 ≤
      (2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1) := by
    calc
      _ ≤ (2 * b * (a + 1)) * (x.length + 1) +
          (4 + c) * (x.length + 1) + (x.length + 1) :=
        Nat.add_le_add (Nat.add_le_add hg hm) (by omega)
      _ = _ := by ring
  calc
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1)) := Nat.mul_le_mul_left d hb
    _ = _ := by ring

/-- **P9 space row, marker stripping** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_stripLast`). The marker
stripper runs in linear work-tape space: the raw buffer and the guard
banks are each linear, and the quadratic **time** contract is deliberate
slack over the construction's actual linear-derived bound (round-1
finding/note 8 — the attached witness proves a linear intermediate
before weakening; no replay story is needed).

**Proof sketch.** The witness's guard/extraction banks and the raw-strip
buffer are each at most linear (`O(n + 1)` cells); the timed conditional
keeps them disjoint; every head stays inside linear intervals, and the
retained `(n+1)²` time clause is slack, not a resource actually spent on
space. -/
theorem computesFunInTime_stripLast_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        (fun n => c * (n + 1) ^ 2) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  obtain ⟨M, a, hM⟩ := f2_strip_linear
  refine ⟨M, a + M.k * (a + 1), ?_, ?_⟩
  · intro x
    apply (hM x).mono
    have hn : x.length + 1 ≤ (x.length + 1) ^ 2 := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
        (show 1 ≤ 2 by omega)
    exact (Nat.mul_le_mul_left a hn).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · intro x t
    have h := f2_space_of_time (hM x) t
    have hb : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

/-- **P11 space row, fixed-width increment** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_incFixed`; the
string-function counterpart of `Turing.incrementTM`). The incrementer
runs in constant work-tape space: it validates and emits from two native
input scans with the carry resident in control.

**Proof sketch.** The existing witness `incFixedTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_incFixed_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => (incFixed x).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_incFixedTM, 3, f2_incFixed_computes, ?_⟩
  intro x t
  rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
  omega

/-- **Threaded-map space row** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_pairMapSnd`, the round-2
catalog addition). Given a payload machine with its own space bound
`Sg` (monotone, since the payload runs on the second component, which is
no longer than the whole input), the threaded-map controller's space is
the payload's plus linear administration. **The witness is a new
forwarding controller, not the received captured-payload machine**
(round-1 finding 4, the witness-honesty refutation: `pairMapTM`'s
capture tape visits `|g b| + 1` cells — the unary-square payload defeats
any linear administrative claim about it; output length is not bounded
by the payload's work space).

**Proof sketch.** The commissioned controller: validate and buffer the
input pair (`O(n + 1)` cells), emit the encoded first component, then
simulate `Mg` on the buffered second component **forwarding its output**
(the E2/`embedEmitTM` discipline — emissions go to the physical output,
never to a work bank), leaving the payload's work-head trajectories
unchanged — coefficient `1` on `Sg` — plus the linear buffer and
administration; the `Monotone Sg` hypothesis transports the payload
bound from `|b|` to `n`. Named construction obligations for the brief:
the validating buffer stage, the forwarding payload stage, and their
seam. -/
theorem computesFunInTime_pairMapSnd_spaceUsed {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ} (Sg : ℕ → ℕ)
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg)
    (hgs : ∀ (y : List Bool) (t : ℕ),
      Mg.tm.spaceUsed (Mg.tm.initCfg y) t ≤ Sg y.length)
    (hSg : Monotone Sg) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => pairEncode a (g b)
          | none => [])
        (fun n => c * (n + 1 + Tg n)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ Sg x.length + c * (x.length + 1) := by
  sorry

/-- A live endpoint rules out a halt anywhere in its preceding run. -/
private lemma f2_loop_live_prefix {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom cfg t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom cfg u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom cfg t = tm.runFrom cfg u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- An empty final output forces every earlier output to be empty. -/
private lemma f2_loop_silent_prefix {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom cfg t).output = []) :
    ∀ u ≤ t, (tm.runFrom cfg u).output = [] := by
  intro u hu
  have hp := tm.output_prefix cfg hu
  rw [ht] at hp
  simpa using hp

/-- Replace a possibly padded halting-time witness by its first halt,
retaining the entire endpoint configuration.
**Proof sketch.** Choose the least halting time. Minimality supplies the
strict liveness guard; the absorbing-halt law identifies its endpoint
with the original, possibly later, witness. -/
private lemma f2_loop_first_halt {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧
      (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      (tm.runFrom cfg u).state = none ∧ tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, ?_, hu, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · intro v hv
    exact Nat.find_min h hv
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hu]

/-- The declared invariant holds at each orbit word, including unreachable
rounds after an earlier acceptance. -/
private lemma f2_loop_orbit_inv (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool) (s0 : List Bool → List Bool)
    (hInv0 : ∀ x, Inv x (s0 x))
    (hInvStep : ∀ x s, Inv x s → Inv x (stepF x s)) (x : List Bool) (i : ℕ) :
    Inv x ((stepF x)^[i] (s0 x)) := by
  induction i with
  | zero => exact hInv0 x
  | succ i ih => rw [Function.iterate_succ_apply']; exact hInvStep x _ ih

/-- The fuel run bounds the fixed counter width on each actual input. -/
private lemma f2_loop_fuel_width (F : FinTM Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    (Nat.bits (R x.length)).length ≤ T x.length := by
  obtain ⟨s, hhalt, hout, hspace⟩ := hF x
  simpa only [hout] using F.tm.output_length_le x (T x.length)

/-- One native input-head move increases its position by at most one. -/
private lemma f2_loop_input_move_le {n : ℕ} (p : Fin (n + 2)) (m : SignType) :
    (moveInputPos p m).val ≤ p.val + 1 := by
  cases m with
  | zero => simp
  | neg => rw [moveInputPos_neg_val]; omega
  | pos =>
    by_cases hp : p.val = n + 1
    · have he : p = ⟨n + 1, by omega⟩ := Fin.ext hp
      rw [he]
      simp only [SignType.pos_eq_one, moveInputPos_rightBoundary]
      omega
    · rw [moveInputPos_pos_of_ne_right p hp]

/-- Input displacement is bounded by elapsed time, even for sublinear budgets. -/
private lemma f2_loop_input_run_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).inputPos.val ≤ c.inputPos.val + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
    cases hd : d.state with
    | none => simp [MultiTapeTM.step, hd]
    | some q =>
      simpa only [MultiTapeTM.step, hd, Action.apply] using
        f2_loop_input_move_le d.inputPos (tm.tr q d.inputSymbol d.workTapeSymbols).inputTape
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- A run appends at most one output bit per step, from any seam configuration. -/
private lemma f2_loop_output_length_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).output.length ≤ c.output.length + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).output.length ≤ d.output.length + 1 := by
    rw [MultiTapeTM.step_output, List.length_append]
    cases tm.outputSymbol d <;> simp
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- The input rewind has a bound in its starting position, so it can be
charged to the preceding run without scanning the entire input.
**Proof sketch.** Take the mandatory first left move and apply the proved
`rewind_scan` at the resulting position. Its exact scan time is position
plus one; the first left move never increases position. -/
private lemma f2_loop_rewind_bounded {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t ≤ cfg.inputPos.val + 2,
      tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_, ?_⟩
  · simp only [c, hstep, moveInputPos_neg_val]
    omega
  · rw [MultiTapeTM.runFrom_add]
    have hfirst : tm.runFrom cfg 1 = c := rfl
    rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
    simp only [c, hstep]

/-- Fixed-width little-endian decrement and its success flag. Underflow
sets the existing cells to true and returns false, without extending the word. -/
private def f2_loopDebit : List Bool → List Bool × Bool
  | [] => ([], false)
  | true :: bs => (false :: bs, true)
  | false :: bs => (true :: (f2_loopDebit bs).1, (f2_loopDebit bs).2)

/-- Number of low zero bits traversed by a borrow. -/
private def f2_loopBorrowPos : List Bool → ℕ
  | false :: bs => f2_loopBorrowPos bs + 1
  | _ => 0

/-- The borrow scan cannot cross more cells than the fixed width. -/
private lemma f2_loopBorrowPos_le (u : List Bool) : f2_loopBorrowPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [f2_loopBorrowPos, List.length_cons] <;> omega

/-- Both successful decrements and underflow preserve the counter width. -/
private lemma f2_loopDebit_length (u : List Bool) : (f2_loopDebit u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [f2_loopDebit, ih]

/-- Little-endian counter value; high zero cells contribute nothing. -/
private def f2_loopValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * f2_loopValue bs + if b then 1 else 0

/-- The fuel machine's binary word has its declared numerical value. -/
private lemma f2_loopValue_bits (n : ℕ) : f2_loopValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [f2_loopValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [f2_loopValue, ih, Nat.bit_val]

/-- A successful debit reduces value by one; underflow occurs only at zero.
**Proof sketch.** A low one is cleared immediately. A low zero becomes one
while the inductive debit reduces the higher part; doubling that equation
gives the successor equation for the full word. -/
private lemma f2_loopDebit_value (u : List Bool) :
    if (f2_loopDebit u).2 then f2_loopValue (f2_loopDebit u).1 + 1 = f2_loopValue u
    else f2_loopValue u = 0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | true => simp [f2_loopDebit, f2_loopValue]
    | false =>
      cases h : (f2_loopDebit u).2 <;>
        simp only [f2_loopDebit, h, Bool.false_eq_true, ↓reduceIte,
          f2_loopValue, Nat.add_zero] at ih ⊢ <;> omega

/-- The borrow returns success exactly for positive counter values. -/
private lemma f2_loopDebit_success (u : List Bool) :
    (f2_loopDebit u).2 = true ↔ 0 < f2_loopValue u := by
  have h := f2_loopDebit_value u
  cases hb : (f2_loopDebit u).2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    simp [h]
  · simp only [hb, ↓reduceIte] at h
    simp only [true_iff]
    omega

/-- Iterating debit retains the original fixed width at every index. -/
private lemma f2_loopDebit_iterate_length (u : List Bool) (i : ℕ) :
    ((fun w => (f2_loopDebit w).1)^[i] u).length = u.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', f2_loopDebit_length, ih]

/-- Before exhaustion, the counter after `i` debits has value `R-i`.
**Proof sketch.** Start from the fuel word's value. Before the last debit
the induction hypothesis gives a positive value, so the success equation
reduces it by exactly one. No representation is shortened. -/
private lemma f2_loopDebit_iterate_value (R i : ℕ) (hi : i ≤ R) :
    f2_loopValue ((fun w => (f2_loopDebit w).1)^[i] R.bits) = R - i := by
  induction i with
  | zero => simpa using f2_loopValue_bits R
  | succ i ih =>
    have hv := ih (by omega)
    have hs : (f2_loopDebit ((fun w => (f2_loopDebit w).1)^[i] R.bits)).2 = true :=
      (f2_loopDebit_success _).2 (by omega)
    have hd := f2_loopDebit_value ((fun w => (f2_loopDebit w).1)^[i] R.bits)
    simp only [hs, ↓reduceIte] at hd
    rw [Function.iterate_succ_apply']
    omega

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma f2_loopBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma f2_loopBuffer_write (pre bs : List Bool) (old new : Bool) :
    Function.update (bufferTape (pre ++ old :: bs)) (pre.length : ℤ) (some new) =
      bufferTape (pre ++ new :: bs) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold bufferTape
    by_cases hn : 0 ≤ z
    · simp only [if_pos hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
    · simp only [if_neg hn]

/-- One-tape fixed-width decrement, followed by a rewind. The live states are
borrow (`inl none`), rewind with success flag (`inl (some b)`), and return
(`inr b`). No transition emits physical output. Return states wait for a
surrounding controller. This privately re-derives the counter template. -/
private def f2_loopDebitTM : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Bool
  tm :=
    { q₀ := .inl none
      tr := fun q _ work => match q with
        | .inl none => match work 0 with
          | some false => ⟨0, fun _ => (some (some true), .pos), none, some (.inl none)⟩
          | some true => ⟨0, fun _ => (some (some false), .neg), none, some (.inl (some true))⟩
          | none => ⟨0, fun _ => (none, .neg), none, some (.inl (some false))⟩
        | .inl (some b) => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, .pos), none, some (.inr b)⟩
        | .inr b => controlAction 0 (some (.inr b)) }

/-- A candidate on the borrow tape, with arbitrary native input-head position. -/
private def f2_loopDebitCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg f2_loopDebitTM.k Bool f2_loopDebitTM.State x :=
  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩

/-- One borrow transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma f2_loopBorrow_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    f2_loopDebitTM.tm.step (f2_loopDebitCfg x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => f2_loopDebitCfg x p (.inl (some false)) (pre.length - 1) pre
      | true :: us => f2_loopDebitCfg x p (.inl (some true)) (pre.length - 1) (pre ++ false :: us)
      | false :: us => f2_loopDebitCfg x p (.inl none) (pre.length + 1) (pre ++ true :: us) := by
  unfold MultiTapeTM.step
  change (f2_loopDebitTM.tm.tr (.inl none) _ _).apply _ = _
  simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, f2_loopBuffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    all_goals first
      | (funext i; exact f2_loopBuffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The borrow phase takes one step beyond the leading false prefix, including
one blank test on underflow.
**Proof sketch.** Induct on the remaining candidate. Each false bit is set
and added to the processed prefix. A true bit or the right blank starts
rewind without changing the width. -/
private lemma f2_loopBorrow_run (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl none) pre.length (pre ++ u))
        (f2_loopBorrowPos u + 1) =
      f2_loopDebitCfg x p (.inl (some (f2_loopDebit u).2))
        ((pre.length : ℤ) + f2_loopBorrowPos u - 1) (pre ++ (f2_loopDebit u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      f2_loopBorrow_step x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | true =>
      simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        f2_loopBorrow_step x p pre (true :: u)
    | false =>
      simp only [f2_loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_loopBorrow_step]
      simpa [f2_loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma f2_loopBorrow_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = f2_loopDebitCfg x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : f2_loopDebitTM.tm.step
        (f2_loopDebitCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          f2_loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width decrement and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading false-prefix length. It returns live at cell zero,
retains the input head, and emits nothing. Width zero returns underflow only
when this subroutine is called, so enumeration can process `[]` first. -/
private lemma f2_loopBorrow_correct (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * f2_loopBorrowPos u + 2 ≤ 2 * u.length + 2 ∧
      f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl none) 0 u)
          (2 * f2_loopBorrowPos u + 2) =
        f2_loopDebitCfg x p (.inr (f2_loopDebit u).2) 0 (f2_loopDebit u).1 := by
  refine ⟨by have := f2_loopBorrowPos_le u; omega, ?_⟩
  have hr := f2_loopBorrow_run x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * f2_loopBorrowPos u + 2 = (f2_loopBorrowPos u + 1) + (f2_loopBorrowPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact f2_loopBorrow_rewind x p (f2_loopDebit u).1 (f2_loopDebit u).2 _
    (by rw [f2_loopDebit_length]; exact f2_loopBorrowPos_le u)

/-- Stop the body at the next anchor entry, distinguishing that return from
a genuine source halt on an extra one-cell flag tape. A true release bit
forces one source action, even at the anchor; every source successor clears
the release bit. The body's full output is retained for subsequent capture. -/
private def f2_loopBodyTM (body : FinTM Bool) (anchor : body.State) : FinTM Bool where
  k := body.k + 1
  State := body.State × Bool
  tm :=
    { q₀ := (body.tm.q₀, false)
      tr := fun q inp work =>
        if q.1 = anchor ∧ q.2 = false then
          { inputTape := 0
            workTapes := fun i =>
              if (i : ℕ) < body.k then (none, 0) else (some (some false), 0)
            output := none
            state := none }
        else
          let a := body.tm.tr q.1 inp (fun i => work i.castSucc)
          { inputTape := a.inputTape
            workTapes := fun i =>
              if h : (i : ℕ) < body.k then a.workTapes ⟨i, h⟩
              else (if a.state = none then some (some true) else none, 0)
            output := a.output
            state := a.state.map (fun s => (s, false)) } }

/-- Embed a source configuration with its release bit and the one-cell
halt-kind flag. The flag head stays at the origin throughout a body call. -/
private def f2_loopBodyCfg (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool) :
    Cfg (f2_loopBodyTM body anchor).k Bool (f2_loopBodyTM body anchor).State x where
  state := c.state.map (fun s => (s, release))
  inputPos := c.inputPos
  workTapes := fun i => if h : (i : ℕ) < body.k then c.workTapes ⟨i, h⟩
    else fun z => if z = 0 then flag else none
  workTapePos := fun i => if h : (i : ℕ) < body.k then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- At an unreleased anchor the stop wrapper takes one silent step and
records rejection, without changing the body's configuration data. -/
private lemma f2_loopBody_stop (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (hc : c.state = some anchor) (flag : Option Bool) :
    (f2_loopBodyTM body anchor).tm.step (f2_loopBodyCfg body anchor c false flag) =
      f2_loopBodyCfg body anchor {c with state := none} false (some false) := by
  unfold MultiTapeTM.step
  simp only [f2_loopBodyCfg, hc, Option.map_some, f2_loopBodyTM, and_self, ↓reduceIte]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hi : (i : ℕ) < body.k
    · simp [Action.apply, hi]
    · simp only [Action.apply, hi, ↓reduceIte]
      by_cases hz : z = 0 <;> simp [hz, hi, Function.update]
  · funext i
    by_cases hi : (i : ℕ) < body.k <;> simp [Action.apply, hi]
  · simp [Action.apply]

/-- Away from an unreleased anchor, the wrapper executes exactly one body
action and records a true flag precisely on a genuine halting transition. -/
private lemma f2_loopBody_step (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (q : body.State) (release : Bool)
    (flag : Option Bool) (hc : c.state = some q)
    (hgo : ¬(q = anchor ∧ release = false)) :
    (f2_loopBodyTM body anchor).tm.step (f2_loopBodyCfg body anchor c release flag) =
      f2_loopBodyCfg body anchor (body.tm.step c) false
        (if (body.tm.step c).state = none then some true else flag) := by
  let a := body.tm.tr q c.inputSymbol c.workTapeSymbols
  have hb : body.tm.step c = a.apply c := by simp only [MultiTapeTM.step, hc, a]
  rw [hb]
  unfold MultiTapeTM.step
  simp only [f2_loopBodyCfg, hc, Option.map_some, f2_loopBodyTM, hgo, ↓reduceIte]
  have hr : (fun i : Fin body.k =>
      (f2_loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc) =
        c.workTapeSymbols := by
    funext i
    simp [f2_loopBodyCfg, Cfg.workTapeSymbols, i.isLt]
  change (let a' : Action body.k Bool body.State :=
            body.tm.tr q c.inputSymbol (fun i : Fin body.k =>
              (f2_loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc);
    ({
      inputTape := a'.inputTape
      workTapes := fun i => if h : (i : ℕ) < body.k then a'.workTapes ⟨i, h⟩
        else (if a'.state = none then some (some true) else none, 0)
      output := a'.output
      state := a'.state.map (fun s => (s, false)) } :
        Action (body.k + 1) Bool (body.State × Bool))).apply _ = _
  rw [hr]
  dsimp only
  dsimp only [a] at *
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : (i : ℕ) < body.k
    · simp [Action.apply, hi]
    · by_cases ha : (body.tm.tr q c.inputSymbol c.workTapeSymbols).state = none
      · simp only [Action.apply, hi, ↓reduceDIte, ha, ↓reduceIte]
        by_cases hz : z = 0 <;> simp [hz, hi, Function.update]
      · simp [Action.apply, hi, ha]
  · funext i
    by_cases hi : (i : ℕ) < body.k <;> simp [Action.apply, hi]

/-- Up to the first halt or anchor return, the stop wrapper simulates the
body exactly. The release flag is consumed by the first action.
**Proof sketch.** Induct on elapsed time. Strict liveness supplies a source
state; the no-anchor condition, except for the released first action,
enables the one-step lemma. Its flag update records a halting emission's
transition without discarding that emission. -/
private lemma f2_loopBody_run (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) t =
      f2_loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
        (if (body.tm.runFrom c t).state = none then some true else none) := by
  induction t with
  | zero => simp [hc]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    rw [ih (fun u hu => hlive u (by omega)) (fun u hu => hanchor u (by omega))]
    have ht := hlive t (by omega)
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp ht
    have hgo : ¬(q = anchor ∧ (if t = 0 then release else false) = false) := by
      rcases hanchor t (by omega) with ⟨hz, hr⟩ | hn
      · simp [hz, hr]
      · rintro ⟨rfl, _⟩
        exact hn hq
    rw [if_neg ht, f2_loopBody_step body anchor _ q _ none hq hgo]
    simp only [Nat.succ_ne_zero, ↓reduceIte, MultiTapeTM.runFrom_succ_eq_step']

/-- W1 captures the stopped body's complete trace in any agreeing controller.
This includes an output bit emitted by the halting transition.
**Proof sketch.** The preceding simulation gives strict liveness of the
stop wrapper before the endpoint. Apply the audited capture contract with
the supplied controller as host, then substitute the simulated endpoint. -/
private lemma f2_loopBody_capture (body : FinTM Bool) (anchor : body.State)
    {H : Type*} {x : List Bool} (host : MultiTapeTM (body.k + 1 + 1) Bool H)
    (emb : body.State × Bool → H) (ret : H)
    (hagree : ∀ s inp work, host.tr (emb s) inp work =
      captureAction emb ret ((f2_loopBodyTM body anchor).tm.tr s inp fun i => work i.castSucc))
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    host.runFrom (captureCfg emb ret [] [] (f2_loopBodyCfg body anchor c release none)) t =
      captureCfg emb ret [] []
        (f2_loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
          (if (body.tm.runFrom c t).state = none then some true else none)) := by
  have hguard : ∀ u < t,
      ¬((f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) u).Halted := by
    intro u hu
    rw [f2_loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, f2_loopBodyCfg] using hlive u hu
  rw [capture_run (f2_loopBodyTM body anchor).tm host emb ret hagree [] [] _ t hguard,
    f2_loopBody_run body anchor c release hc t hlive hanchor]

/-- Disjoint finite control for fuel, body calls, and fourteen controller phases. -/
private abbrev f2_LoopHostState (body F : FinTM Bool) :=
  F.State ⊕ ((Bool × (body.State × Bool)) ⊕ Fin 14)

/-- Relocate the fuel machine past the untouched body, flag, and counter tapes. -/
private def f2_loopFuelSource (body F : FinTM Bool) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool F.State where
  q₀ := F.tm.q₀
  tr := fun q inp work =>
    rightAction (body.k + 1) id (rightAction 1 id
      (F.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1) (Fin.natAdd 1 i))))

/-- Extend the stopped body with a preserved counter and the fuel-phase residue. -/
private def f2_loopBodySource (body F : FinTM Bool) (anchor : body.State) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) where
  q₀ := (body.tm.q₀, false)
  tr := fun q inp work => leftAction (1 + F.k) id
    ((f2_loopBodyTM body anchor).tm.tr q inp fun i => work (Fin.castAdd (1 + F.k) i))

/-- A controller action touches only the flag, counter, and capture tapes. -/
private def f2_loopControlAction (body F : FinTM Bool) (inp : SignType)
    (flag : Option (Option Bool)) (counter payload : Option (Option Bool) × SignType)
    (out : Option Bool) (next : Option (f2_LoopHostState body F)) :
    Action (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) where
  inputTape := inp
  workTapes := fun i =>
    if (i : ℕ) = body.k then (flag, 0)
    else if (i : ℕ) = body.k + 1 then counter
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then payload
    else (none, 0)
  output := out
  state := next

/-- Concrete loop controller, with fixed-verdict and payload-replay modes.
Fuel is captured, rewound, copied into the fixed-width counter while the
capture tape is cleared, and both heads are rewound together. Two further
phases rewind the native input before starting the body. Body startup and
active rounds have disjoint return states; only an active rejection debits.
The release bit forces one body action before another anchor is recognized.

Control phases: 0/1 fuel rewind; 2 counter copy; 3 counter/capture rewind;
4/5 input rewind; 6 startup return; 7 round return; 8 borrow; 9/10 successful
and underflow rewinds; 11 exhaustion; 12/13 payload rewind and replay.
The fuel work tapes are never cleared or reused after the fuel phase. -/
private def f2_loopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool where
  k := body.k + 1 + (1 + F.k) + 1
  State := f2_LoopHostState body F
  tm :=
    { q₀ := .inl F.tm.q₀
      tr := fun q inp work =>
        let ctrl (j : Fin 14) : f2_LoopHostState body F := .inr (.inr j)
        let call (startup : Bool) (s : body.State × Bool) : f2_LoopHostState body F :=
          .inr (.inl (startup, s))
        let flag : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k, by omega⟩
        let counter : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k + 1, by omega⟩
        let payload := Fin.last (body.k + 1 + (1 + F.k))
        let act := f2_loopControlAction body F
        match q with
        | .inl s => captureAction Sum.inl (ctrl 0)
            ((f2_loopFuelSource body F).tr s inp fun i => work i.castSucc)
        | .inr (.inl (startup, s)) =>
            captureAction (call startup) (ctrl (if startup then 6 else 7))
              ((f2_loopBodySource body F anchor).tr s inp fun i => work i.castSucc)
        | .inr (.inr phase) =>
            if phase = 0 then act 0 none (none, 0) (none, .neg) none (some (ctrl 1))
            else if phase = 1 then
              match work payload with
              | some _ => act 0 none (none, 0) (none, .neg) none (some (ctrl 1))
              | none => act 0 none (none, 0) (none, .pos) none (some (ctrl 2))
            else if phase = 2 then
              match work payload with
              | some b => act 0 none (some (some b), .pos) (some none, .pos) none
                  (some (ctrl 2))
              | none => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))
            else if phase = 3 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))
              | none => act 0 none (none, .pos) (none, .pos) none (some (ctrl 4))
            else if phase = 4 then act .neg none (none, 0) (none, 0) none (some (ctrl 5))
            else if phase = 5 then
              match inp with
              | some _ => act .neg none (none, 0) (none, 0) none (some (ctrl 5))
              | none => act .pos none (none, 0) (none, 0) none
                  (some (call true (body.tm.q₀, false)))
            else if phase = 6 then act 0 (some none) (none, 0) (none, 0) none
              (some (call false (anchor, true)))
            else if phase = 7 then
              if work flag = some true then
                if findMode then act 0 none (none, 0) (none, .neg) none (some (ctrl 12))
                else act 0 none (none, 0) (none, 0) (some true) none
              else act 0 (some none) (none, 0) (none, 0) none (some (ctrl 8))
            else if phase = 8 then
              match work counter with
              | some false => act 0 none (some (some true), .pos) (none, 0) none
                  (some (ctrl 8))
              | some true => act 0 none (some (some false), .neg) (none, 0) none
                  (some (ctrl 9))
              | none => act 0 none (none, .neg) (none, 0) none (some (ctrl 10))
            else if phase = 9 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, 0) none (some (ctrl 9))
              | none => act 0 none (none, .pos) (none, 0) none
                  (some (call false (anchor, true)))
            else if phase = 10 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, 0) none (some (ctrl 10))
              | none => act 0 none (none, .pos) (none, 0) none (some (ctrl 11))
            else if phase = 11 then
              act 0 none (none, 0) (none, 0) (if findMode then none else some false) none
            else if phase = 12 then
              match work payload with
              | some _ => act 0 none (none, 0) (none, .neg) none (some (ctrl 12))
              | none => act 0 none (none, 0) (none, .pos) none (some (ctrl 13))
            else
              match work payload with
              | some b => act 0 none (none, 0) (none, .pos) (some b) (some (ctrl 13))
              | none => act 0 none (none, 0) (none, 0) none none }

/-- The concrete host's body states agree with W1 on the entire source table;
startup and active calls return to distinct controller phases. -/
private lemma f2_loopHost_body_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) (t : ℕ)
    (hlive : ∀ u < t, ¬((f2_loopBodySource body F anchor).runFrom c u).Halted) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
          (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] [] c) t =
      captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
        (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
        ((f2_loopBodySource body F anchor).runFrom c t) := by
  exact capture_run (f2_loopBodySource body F anchor) (f2_loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel states capture all fuel emissions directly in the concrete host. -/
private lemma f2_loopHost_fuel_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool F.State x) (t : ℕ)
    (hlive : ∀ u < t, ¬((f2_loopFuelSource body F).runFrom c u).Halted) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] c) t =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((f2_loopFuelSource body F).runFrom c t) := by
  exact capture_run (f2_loopFuelSource body F) (f2_loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel capture starts at the host's genuine blank initial configuration. -/
private lemma f2_loopHost_init (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) :
    (f2_loopHost body F anchor findMode).tm.initCfg x =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((f2_loopFuelSource body F).initCfg x) := by
  rw [initCfg_ofWords, initCfg_ofWords]
  simp [Cfg.ofWords, captureCfg, f2_loopHost, f2_loopFuelSource]

/-- With no track operations, a controller action is the standard input-only action. -/
private lemma f2_loopControl_idle (body F : FinTM Bool) (inp : SignType)
    (next : Option (f2_LoopHostState body F)) :
    f2_loopControlAction body F inp none (none, 0) (none, 0) none next =
      controlAction inp next := by
  simp [f2_loopControlAction, controlAction]

/-- Host phases 4 and 5 rewind the native input in bounded time, retaining
all tapes, heads, and output, then dispatch to genuine body startup. -/
private lemma f2_loopHost_input_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (cfg : Cfg (f2_loopHost body F anchor findMode).k Bool (f2_loopHost body F anchor findMode).State x)
    (hs : cfg.state = some (.inr (.inr (4 : Fin 14)))) :
    ∃ t ≤ cfg.inputPos.val + 2,
      (f2_loopHost body F anchor findMode).tm.runFrom cfg t =
        {cfg with state := some (.inr (.inl (true, (body.tm.q₀, false)))), inputPos := 1} := by
  apply f2_loop_rewind_bounded (f2_loopHost body F anchor findMode).tm
    (.inr (.inr 4)) (.inr (.inr 5)) (.some (.inr (.inl (true, (body.tm.q₀, false)))))
    ?_ ?_ cfg hs
  · intro inp work
    exact f2_loopControl_idle body F .neg _
  · intro inp work
    cases inp <;> exact f2_loopControl_idle body F _ _

/-- A controller configuration with arbitrary preserved body/fuel residue.
Only the flag, counter, and capture tracks are replaced by the parameters. -/
private def f2_loopFrame (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x where
  state := q
  inputPos := p
  workTapes := fun i =>
    if (i : ℕ) = body.k then flag
    else if (i : ℕ) = body.k + 1 then counter
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then payload
    else base.workTapes i
  workTapePos := fun i =>
    if (i : ℕ) = body.k then 0
    else if (i : ℕ) = body.k + 1 then ch
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then ph
    else base.workTapePos i
  output := out

/-- Optional writes update exactly their current cell. -/
private def f2_loopWrite (tape : ℤ → Option Bool) (head : ℤ) :
    Option (Option Bool) → ℤ → Option Bool
  | none => tape
  | some symbol => Function.update tape head symbol

/-- Controller actions preserve the inactive frame and perform precisely
the three declared track operations. -/
private lemma f2_loopControl_apply (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool)
    (inp : SignType) (fw : Option (Option Bool))
    (ca pa : Option (Option Bool) × SignType) (emit : Option Bool)
    (next : Option (f2_LoopHostState body F)) :
    (f2_loopControlAction body F inp fw ca pa emit next).apply
        (f2_loopFrame body F base q p flag counter payload ch ph out) =
      f2_loopFrame body F base next (moveInputPos p inp)
        (f2_loopWrite flag 0 fw) (f2_loopWrite counter ch ca.1) (f2_loopWrite payload ph pa.1)
        (ch + ca.2) (ph + pa.2) (out ++ emit.toList) := by
  have hcf : body.k + 1 ≠ body.k := by omega
  have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  have hpc : body.k + 1 + (1 + F.k) ≠ body.k + 1 := by omega
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hf, ↓reduceIte]
      cases fw <;> rfl
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hc, hcf, ↓reduceIte]
        cases ca.1 <;> rfl
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hp, hpf, hpc, ↓reduceIte]
          cases pa.1 <;> rfl
        · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf, hc, hp]
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hc]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k) <;>
          simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf, hc, hp, hpf]

/-- One-tape payload replay: emit each stored bit, then halt on the right blank. -/
private def f2_loopReplayTM : FinTM Bool where
  k := 1
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ _ work => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some ()⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Replay configuration with arbitrary input position and output prefix. -/
private def f2_loopReplayCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Unit) (z : ℤ) (word out : List Bool) : Cfg 1 Bool Unit x :=
  ⟨q, p, fun _ => bufferTape word, fun _ => z, out⟩

/-- A replay step emits the current bit without modifying the captured word;
at the right blank it halts without an additional bit. -/
private lemma f2_loopReplay_step (x : List Bool) (p : Fin (x.length + 2))
    (pre rest out : List Bool) :
    f2_loopReplayTM.tm.step (f2_loopReplayCfg x p (some ()) pre.length (pre ++ rest) out) =
      match rest with
      | [] => f2_loopReplayCfg x p none pre.length pre out
      | b :: bs => f2_loopReplayCfg x p (some ()) (pre.length + 1) (pre ++ b :: bs) (out ++ [b]) := by
  unfold MultiTapeTM.step
  change (f2_loopReplayTM.tm.tr () _ _).apply _ = _
  simp only [f2_loopReplayTM, f2_loopReplayCfg, Cfg.workTapeSymbols, f2_loopBuffer_read]
  cases rest with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ ?_
    · simp
    · funext i; simp [Action.apply]
    · simp [Action.apply]
  | cons b rest =>
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]

/-- Replay emits exactly the remaining payload in its length plus one steps,
including an empty payload.
**Proof sketch.** Induct on the unprocessed suffix. The step lemma emits
one bit and moves the frontier; the empty suffix supplies the final blank
test. Concatenation associativity preserves the exact output order. -/
private lemma f2_loopReplay_run (x : List Bool) (p : Fin (x.length + 2))
    (rest : List Bool) : ∀ pre out : List Bool,
    f2_loopReplayTM.tm.runFrom (f2_loopReplayCfg x p (some ()) pre.length (pre ++ rest) out)
        (rest.length + 1) =
      f2_loopReplayCfg x p none (pre ++ rest).length (pre ++ rest) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out
    simpa [MultiTapeTM.runFrom_succ_eq_step] using f2_loopReplay_step x p pre [] out
  | cons b rest ih =>
    intro pre out
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step, f2_loopReplay_step]
    simpa [List.append_assoc, List.length_append, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using ih (pre ++ [b]) (out ++ [b])

/-- A payload-only controller action is the right-block action extension. -/
private lemma f2_loopControl_payload (body F : FinTM Bool) (d : SignType)
    (out : Option Bool) (next : Option (f2_LoopHostState body F)) :
    f2_loopControlAction body F 0 none (none, 0) (none, d) out next =
      rightAction (body.k + 1 + (1 + F.k)) id
        (⟨0, fun _ : Fin 1 => (none, d), out, next⟩ : Action 1 Bool (f2_LoopHostState body F)) := by
  simp only [f2_loopControlAction, rightAction, Option.map_id]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
    simp [hj]
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
    simp [hf]

/-- Phase 13 replays the captured payload in the actual host, preserving
the arbitrary completed body/fuel tapes. -/
private lemma f2_loopHost_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) (p : Fin (x.length + 2)) (word out : List Bool)
    (tapes : Fin (body.k + 1 + (1 + F.k)) → ℤ → Option Bool)
    (heads : Fin (body.k + 1 + (1 + F.k)) → ℤ) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (f2_loopReplayCfg x p (some ()) 0 word out) tapes heads) (word.length + 1) =
      rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
        (f2_loopReplayCfg x p none word.length word (out ++ word)) tapes heads := by
  have htr : ∀ q inp work,
      (f2_loopHost body F anchor findMode).tm.tr (.inr (.inr (13 : Fin 14))) inp work =
        rightAction (body.k + 1 + (1 + F.k))
          (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (f2_loopReplayTM.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1 + (1 + F.k)) i)) := by
    intro q inp work
    cases q
    change (match work (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => f2_loopControlAction body F 0 none (none, 0) (none, .pos) (some b)
          (some (.inr (.inr 13)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, 0) none none) = _
    cases hw : work (Fin.last (body.k + 1 + (1 + F.k)))
    · simpa only [f2_loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        f2_loopControl_payload body F 0 none none
    · simpa only [f2_loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        f2_loopControl_payload body F .pos _ _
  refine (rightCfg_run (k := body.k + 1 + (1 + F.k)) (l := 1)
    f2_loopReplayTM.tm (f2_loopHost body F anchor findMode).tm
    (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) htr
    (f2_loopReplayCfg x p (some ()) 0 word out) tapes heads (word.length + 1)).trans ?_
  have hr := f2_loopReplay_run x p word [] out
  simpa using congrArg
    (fun c => rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) c tapes heads) hr

/-- The fuel configuration on its relocated block, with the body, flag, and
counter still blank. The completed fuel residue is retained by this embedding. -/
private def f2_loopFuelCfg (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool F.State x :=
  rightCfg id (rightCfg id c (fun (_ : Fin 1) _ => none) (fun _ => 0))
    (fun (_ : Fin (body.k + 1)) _ => none) (fun _ => 0)

/-- Relocating fuel through the counter and body blocks preserves every run.
**Proof sketch.** Apply the right-block simulation twice. Each inactive block
has its own blank tapes and origin heads, retained throughout the source run. -/
private lemma f2_loopFuel_run (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (t : ℕ) :
    (f2_loopFuelSource body F).runFrom (f2_loopFuelCfg body F c) t =
      f2_loopFuelCfg body F (F.tm.runFrom c t) := by
  let pad : MultiTapeTM (1 + F.k) Bool F.State :=
    { q₀ := F.tm.q₀
      tr := fun q inp work => rightAction 1 id
        (F.tm.tr q inp (fun i => work (Fin.natAdd 1 i))) }
  unfold f2_loopFuelCfg
  rw [rightCfg_run pad (f2_loopFuelSource body F) id (fun _ _ _ => rfl),
    rightCfg_run F.tm pad id (fun _ _ _ => rfl)]

/-- The relocated fuel source begins at its genuine blank configuration. -/
private lemma f2_loopFuel_init (body F : FinTM Bool) (x : List Bool) :
    (f2_loopFuelSource body F).initCfg x = f2_loopFuelCfg body F (F.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]

/-- The capture track of a frame reads precisely its parameterized tape. -/
private lemma f2_loopFrame_payload (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        (Fin.last (body.k + 1 + (1 + F.k))) = payload ph := by
  have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  simp [f2_loopFrame, Cfg.workTapeSymbols, hf]

/-- The counter track of a frame reads precisely its parameterized tape. -/
private lemma f2_loopFrame_counter (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k + 1, by omega⟩ = counter ch := by
  simp [f2_loopFrame, Cfg.workTapeSymbols]

/-- Fuel-rewind phase 1 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma f2_loopHost_fuel_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 2))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 1)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 2)))).apply _ = _
    rw [f2_loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 1)))
        | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 2)))).apply _ = _
      rw [f2_loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- During fuel copying, the processed prefix of the capture tape is blank. -/
private def f2_loopCopyTape (pre rest : List Bool) (z : ℤ) : Option Bool :=
  if z < pre.length then none else bufferTape (pre ++ rest) z

/-- The copying frontier reads the first bit of the remaining suffix. -/
private lemma f2_loopCopy_read (pre rest : List Bool) :
    f2_loopCopyTape pre rest pre.length = rest.head? := by
  simp only [f2_loopCopyTape, lt_self_iff_false, ↓reduceIte, f2_loopBuffer_read]

/-- Clearing one fuel cell extends the already-cleared prefix by that bit. -/
private lemma f2_loopCopy_erase (pre rest : List Bool) (b : Bool) :
    Function.update (f2_loopCopyTape pre (b :: rest)) (pre.length : ℤ) none =
      f2_loopCopyTape (pre ++ [b]) rest := by
  funext z
  by_cases hz : z = pre.length
  · subst z; simp [f2_loopCopyTape]
  · rw [Function.update_of_ne hz]
    have hlt : z < (pre.length : ℤ) ↔ z < ((pre ++ [b]).length : ℤ) := by
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    simp only [f2_loopCopyTape, hlt, List.append_assoc, List.singleton_append]

/-- Before copying begins the capture tape is the original fuel buffer. -/
private lemma f2_loopCopy_initial (word : List Bool) :
    f2_loopCopyTape [] word = bufferTape word := by
  funext z
  by_cases hz : z < 0
  · simp [f2_loopCopyTape, bufferTape, hz, show ¬0 ≤ z by omega]
  · simp [f2_loopCopyTape, hz]

/-- After copying ends the capture tape is completely blank. -/
private lemma f2_loopCopy_final (word : List Bool) :
    f2_loopCopyTape word [] = bufferTape [] := by
  funext z
  by_cases hz : z < word.length
  · simp [f2_loopCopyTape, hz]
  · have hn : 0 ≤ z := by omega
    simp [f2_loopCopyTape, hz, bufferTape, hn]

/-- Phase 2 copies the remaining fuel bits to the counter, clearing each
captured bit, then starts the synchronized rewind.
**Proof sketch.** Induct on the uncopied suffix. A nonempty suffix writes
its head at the counter's right blank, clears the corresponding payload
cell, and advances both heads. The empty suffix detects the right blank
and moves both heads left once, including when the original word is empty. -/
private lemma f2_loopHost_fuel_copy (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (out : List Bool)
    (rest : List Bool) : ∀ pre,
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre rest) pre.length pre.length out) (rest.length + 1) =
      f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape (pre ++ rest))
        (bufferTape []) ((pre ++ rest).length - 1) ((pre ++ rest).length - 1) out := by
  induction rest with
  | nil =>
    intro pre
    rw [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
        (f2_loopCopyTape pre []) pre.length pre.length out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => f2_loopControlAction body F 0 none (some (some b), .pos)
          (some none, .pos) none (some (.inr (.inr 2)))
      | none => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))).apply _ = _
    rw [f2_loopFrame_payload, f2_loopCopy_read]
    dsimp only [List.head?]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, f2_loopCopy_final, sub_eq_add_neg]
  | cons b rest ih =>
    intro pre
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre (b :: rest)) pre.length pre.length out) =
        f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape (pre ++ [b]))
          (f2_loopCopyTape (pre ++ [b]) rest) (pre ++ [b]).length (pre ++ [b]).length out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre (b :: rest)) pre.length pre.length out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some bit => f2_loopControlAction body F 0 none (some (some bit), .pos)
            (some none, .pos) none (some (.inr (.inr 2)))
        | none => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))).apply _ = _
      rw [f2_loopFrame_payload, f2_loopCopy_read]
      dsimp only [List.head?]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, f2_loopCopy_erase, bufferTape_append]
    rw [hs]
    simpa [List.append_assoc] using ih (pre ++ [b])

/-- Phase 3 rewinds counter and cleared capture heads together.
**Proof sketch.** Induct on the number of counter cells to the left. Both
heads take the same moves; only the counter is read, so the already-cleared
capture tape stays blank. The final left-blank test moves both heads to zero. -/
private lemma f2_loopHost_fuel_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
        (bufferTape []) ((0 : ℤ) - 1) ((0 : ℤ) - 1) out).workTapeSymbols
          ⟨body.k + 1, by omega⟩ with
      | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))
      | none => f2_loopControlAction body F 0 none (none, .pos) (none, .pos) none
          (some (.inr (.inr 4)))).apply _ = _
    rw [f2_loopFrame_counter]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            ⟨body.k + 1, by omega⟩ with
        | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))
        | none => f2_loopControlAction body F 0 none (none, .pos) (none, .pos) none
            (some (.inr (.inr 4)))).apply _ = _
      rw [f2_loopFrame_counter]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Fuel setup phases 0--3 copy the complete fuel word to the counter,
clear the capture track, and return both heads to zero in exactly `3|word|+4`
steps. This includes the empty word, with no counter debit.
**Proof sketch.** Compose the mandatory left move, the fuel rewind, the
copy/clear scan, and the synchronized rewind. Their costs are respectively
one and three copies of the word length plus one. -/
private lemma f2_loopHost_fuel_setup (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
          (bufferTape word) 0 word.length out) (3 * word.length + 4) =
      f2_loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  have hs : (f2_loopHost body F anchor findMode).tm.step
      (f2_loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
        (bufferTape word) 0 word.length out) =
      f2_loopFrame body F base (some (.inr (.inr 1))) p flag (bufferTape [])
        (bufferTape word) 0 ((word.length : ℤ) - 1) out := by
    change (f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
      (some (.inr (.inr 1)))).apply _ = _
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, sub_eq_add_neg]
  rw [show 3 * word.length + 4 =
      ((word.length + 1) + (word.length + 1) + (word.length + 1)) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs]
  rw [MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add (a := word.length + 1) (b := word.length + 1),
    f2_loopHost_fuel_rewind body F anchor findMode base p flag (bufferTape []) 0 word out
      word.length (le_refl _)]
  have hc := f2_loopHost_fuel_copy body F anchor findMode base p flag out word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, f2_loopCopy_initial] at hc
  rw [hc, f2_loopHost_fuel_return body F anchor findMode base p flag word out
    word.length (le_refl _)]

/-- The host's captured fuel endpoint, retaining all completed fuel residue. -/
private def f2_loopFuelCaptured (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] (f2_loopFuelCfg body F c)

/-- The prepared startup configuration: fuel copied, capture blank, input
and active heads at their origins, and completed fuel work retained. -/
private def f2_loopReady (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  f2_loopFrame body F (f2_loopFuelCaptured body F c)
    (some (.inr (.inl (true, (body.tm.q₀, false))))) 1
    (bufferTape []) (bufferTape c.output) (bufferTape []) 0 0 []

/-- At a genuine fuel halt the capture endpoint has the frame expected by
phase 0, with the flag and counter still blank.
**Proof sketch.** Split the physical tape index into capture, body/flag,
counter, and fuel blocks. The three active controller tracks agree with
their explicit parameters; every inactive track is retained from the base. -/
private lemma f2_loopFuelCaptured_frame (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (hc : c.state = none) :
    f2_loopFuelCaptured body F c =
      f2_loopFrame body F (f2_loopFuelCaptured body F c) (some (.inr (.inr 0))) c.inputPos
        (bufferTape []) (bufferTape []) (bufferTape c.output) 0 c.output.length [] := by
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hc]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hf]
    · intro j
      have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [f2_loopFrame, hbf, Nat.ne_of_lt b.isLt]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [f2_loopFrame, hbf, Nat.ne_of_lt b.isLt]

/-- Fuel execution, setup, and input rewind reach prepared body startup
within `5*T+7` steps, retaining the actual fuel endpoint.
**Proof sketch.** Replace the supplied padded fuel run by its first halt,
relocate it twice, and capture it in the actual host. Setup costs `3L+4`,
where `L ≤ T`; the input rewind costs at most the first run's displacement
plus two, hence at most `T+3`. No bound in the input length is used. -/
private lemma f2_loopHost_prepare (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (f2_loopHost body F anchor findMode).tm.runFrom
        ((f2_loopHost body F anchor findMode).tm.initCfg x) t = f2_loopReady body F c ∧
      ∀ i, -(T x.length : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ T x.length := by
  obtain ⟨space, hhalt, hout, hspace⟩ := hF x
  obtain ⟨u, hu, hut, hlive, huh, hue⟩ :=
    f2_loop_first_halt F.tm (F.tm.initCfg x) (T x.length) (by simp [MultiTapeTM.initCfg, Cfg.init]) hhalt
  let c := F.tm.runFrom (F.tm.initCfg x) u
  have hc : c.state = none := huh
  have ho : c.output = Nat.bits (R x.length) := by dsimp only [c]; rw [hue]; exact hout
  have hcap : (f2_loopHost body F anchor findMode).tm.runFrom
      ((f2_loopHost body F anchor findMode).tm.initCfg x) u = f2_loopFuelCaptured body F c := by
    rw [f2_loopHost_init, f2_loopFuel_init]
    rw [f2_loopHost_fuel_capture]
    · rw [f2_loopFuel_run]; rfl
    · intro v hv
      rw [f2_loopFuel_run]
      simpa [Cfg.Halted, f2_loopFuelCfg, rightCfg] using hlive v hv
  let prepared := f2_loopFrame body F (f2_loopFuelCaptured body F c)
    (some (.inr (.inr 4))) c.inputPos (bufferTape []) (bufferTape c.output)
    (bufferTape []) 0 0 []
  have hsetup : (f2_loopHost body F anchor findMode).tm.runFrom
      (f2_loopFuelCaptured body F c) (3 * c.output.length + 4) = prepared := by
    conv_lhs => arg 1; rw [f2_loopFuelCaptured_frame body F c hc]
    exact f2_loopHost_fuel_setup body F anchor findMode _ _ _ _ _
  obtain ⟨v, hv, hrew⟩ := f2_loopHost_input_rewind body F anchor findMode prepared rfl
  have hw : c.output.length ≤ T x.length := by rw [ho]; exact f2_loop_fuel_width F R T hF x
  have hp : c.inputPos.val ≤ 1 + u := f2_loop_input_run_le F.tm (F.tm.initCfg x) u
  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_, ?_⟩
  · change v ≤ c.inputPos.val + 2 at hv
    omega
  · rw [MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew]
    rfl

  · intro i
    have h := f2_head_steps F.tm (F.tm.initCfg x) u i
    have hh : -(u : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ u := by
      simpa [c, MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords] using h
    omega

/-- The stopped body's padded source configuration, preserving the counter
word and the complete fuel residue through every call. -/
private def f2_loopBodyPadded (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x :=
  leftCfg id (f2_loopBodyCfg body anchor c release flag)
    (Fin.addCases (fun (_ : Fin 1) => bufferTape word) fuel.workTapes)
    (Fin.addCases (fun (_ : Fin 1) => 0) fuel.workTapePos)

/-- A body call viewed inside the concrete capturing host. A halted stopped
body is represented by the corresponding startup/active return phase. -/
private def f2_loopCall (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (startup : Bool) (c : Cfg body.k Bool body.State x) (release : Bool)
    (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
    (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
    (f2_loopBodyPadded body F anchor c release flag word fuel)

/-- The padded body source simulates the stopped body with arbitrary inactive
counter and fuel tracks. -/
private lemma f2_loopBodySource_run (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool}
    (c : Cfg (body.k + 1) Bool (body.State × Bool) x)
    (tapes : Fin (1 + F.k) → ℤ → Option Bool) (heads : Fin (1 + F.k) → ℤ) (t : ℕ) :
    (f2_loopBodySource body F anchor).runFrom (leftCfg id c tapes heads) t =
      leftCfg id ((f2_loopBodyTM body anchor).tm.runFrom c t) tapes heads :=
  leftCfg_run (f2_loopBodyTM body anchor).tm (f2_loopBodySource body F anchor)
    id (fun _ _ _ => rfl) c tapes heads t

/-- A live anchor endpoint is captured after one additional stop step.
The exact endpoint keeps every inactive tape and carries the false stop flag.
**Proof sketch.** The live endpoint rules out earlier halts. Use the source
wrapper simulation up to that endpoint, take its silent anchor-stop step,
and lift the resulting run through the padded source and actual host capture.
The guard at time zero is supplied by the release bit for active calls. -/
private lemma f2_loopHost_anchor_return (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hend : (body.tm.runFrom c t).state = some anchor)
    (hreleased : t = 0 → release = false)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor startup c release none word fuel) (t + 1) =
      f2_loopCall body F anchor startup {body.tm.runFrom c t with state := none}
        false (some false) word fuel := by
  have hlive : ∀ u ≤ t, (body.tm.runFrom c u).state ≠ none :=
    f2_loop_live_prefix body.tm c t (by rw [hend]; simp)
  have hc : c.state ≠ none := by simpa using hlive 0 (Nat.zero_le _)
  have hr : (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) t =
      f2_loopBodyCfg body anchor (body.tm.runFrom c t) false none := by
    rw [f2_loopBody_run body anchor c release hc t
      (fun u hu => hlive u (by omega)) hanchor]
    have hn := hlive t (le_refl _)
    rw [if_neg hn]
    by_cases ht : t = 0
    · rw [if_pos ht, hreleased ht]
    · rw [if_neg ht]
  have hstop : (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none)
      (t + 1) =
      f2_loopBodyCfg body anchor {body.tm.runFrom c t with state := none} false (some false) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hr, f2_loopBody_stop body anchor _ hend]
  unfold f2_loopCall f2_loopBodyPadded
  rw [f2_loopHost_body_capture]
  · rw [f2_loopBodySource_run, hstop]
  · intro u hu
    rw [f2_loopBodySource_run, f2_loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, leftCfg, f2_loopBodyCfg] using hlive u (by omega)

/-- Prepared fuel startup is the canonical captured body call on blank body
tapes; the counter and fuel residue are exactly the padded inactive block.
**Proof sketch.** Compare the four physical tape blocks. The input head and
all active heads are at their origins; only the completed fuel bank has
arbitrary contents and head positions. -/
private lemma f2_loopReady_call (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (fuel : Cfg F.k Bool F.State x) :
    f2_loopReady body F fuel =
      f2_loopCall body F anchor true (body.tm.initCfg x) false none fuel.output fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
        f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
          f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, f2_loopFuelCaptured, f2_loopFuelCfg,
          rightCfg, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
            f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hb : (b : ℕ) < F.k := b.isLt
          simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
            f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, f2_loopFuelCaptured, f2_loopFuelCfg,
            rightCfg, hbf, hb, Nat.ne_of_lt hb, Fin.addCases]

/-- Phase 6 clears startup's false flag and releases the first anchor for
free. It changes no body, counter, or fuel data.
**Proof sketch.** The captured stopped body is in phase 6. Its sole write
clears the flag's origin cell. Comparing tape blocks identifies the result
with the active released call on the same body data. -/
private lemma f2_loopHost_release (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    (f2_loopHost body F anchor findMode).tm.step
        (f2_loopCall body F anchor true {c with state := none} false (some false) word fuel) =
      f2_loopCall body F anchor false {c with state := some anchor} true none word fuel := by
  change (f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
    (some (.inr (.inl (false, (anchor, true)))))).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hf : (i : ℕ) = body.k
    · have hi : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
        leftCfg, f2_loopBodyCfg, hf, hi, Fin.addCases, Function.update]
    · by_cases hb : (i : ℕ) < body.k + 1
      · have hi : (i : ℕ) < body.k := by omega
        simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
          leftCfg, f2_loopBodyCfg, hf, Fin.addCases, hb, hi]
      · simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
          leftCfg, f2_loopBodyCfg, hf, Fin.addCases, hb]
  · funext i
    by_cases hf : (i : ℕ) = body.k <;>
      simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
        leftCfg, f2_loopBodyCfg, hf]
  · simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg]

/-- Genuine body startup reaches the released first candidate in at most
its source startup time plus two host steps.
**Proof sketch.** The no-anchor prefix includes time zero, so startup is
captured without a premature stop. Its live endpoint yields the false flag;
one stop step and phase 6's flag-clear step release the initial candidate. -/
private lemma f2_loopHost_start (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s : List Bool) (t : ℕ)
    (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s)) :
    (f2_loopHost body F anchor findMode).tm.runFrom (f2_loopReady body F fuel) (t + 2) =
      f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
        true none fuel.output fuel := by
  rw [f2_loopReady_call body F anchor, show t + 2 = (t + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step']
  rw [f2_loopHost_anchor_return body F anchor findMode true (body.tm.initCfg x) false t
    fuel.output fuel (by rw [hend]; rfl) (fun _ => rfl) (fun u hu => Or.inr (hguard u hu))]
  rw [hend, f2_loopHost_release body F anchor findMode _ _ _]
  rfl

/-- A genuine first halt returns to phase 7 with the true stop flag and the
entire source output captured, including its halting emission.
**Proof sketch.** Simulate the released body through its first halting action.
Strict liveness permits actual-host capture throughout; the positive duration
consumes the release bit and the halting action sets the true flag. -/
private lemma f2_loopHost_halt_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (t : ℕ) (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (ht : 0 < t) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u, 0 < u → u < t → (body.tm.runFrom c u).state ≠ some anchor)
    (hend : (body.tm.runFrom c t).state = none) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c true none word fuel) t =
      f2_loopCall body F anchor false (body.tm.runFrom c t) false (some true) word fuel := by
  have hc : c.state ≠ none := by simpa using hlive 0 ht
  have hg : ∀ u < t, (u = 0 ∧ true = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor := by
    intro u hu
    by_cases hz : u = 0
    · exact Or.inl ⟨hz, rfl⟩
    · exact Or.inr (hanchor u (by omega) hu)
  unfold f2_loopCall f2_loopBodyPadded
  rw [f2_loopHost_body_capture]
  · rw [f2_loopBodySource_run, f2_loopBody_run body anchor c true hc t hlive hg]
    simp [hend, Nat.ne_of_gt ht]
  · intro u hu
    rw [f2_loopBodySource_run, f2_loopBody_run body anchor c true hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hg v (by omega))]
    simpa [Cfg.Halted, leftCfg, f2_loopBodyCfg] using hlive u hu

/-- A captured body call has the explicit flag, counter, and payload tracks
used by the controller frame, with arbitrary inactive body and fuel residue. -/
private lemma f2_loopCall_frame (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    f2_loopCall body F anchor startup c release flag word fuel =
      f2_loopFrame body F (f2_loopCall body F anchor startup c release flag word fuel)
        (f2_loopCall body F anchor startup c release flag word fuel).state c.inputPos
        (fun z => if z = 0 then flag else none) (bufferTape word) (bufferTape c.output)
        0 c.output.length [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hp, hpf]
        · simp [f2_loopFrame, hf, hc, hp]

/-- Reframing a body call changes precisely its control, flag, and counter.
**Proof sketch.** The source configuration changes only in state. Thus all
inactive body and fuel data coincide; compare the three explicitly replaced
tracks and retain every other physical tape and head. -/
private lemma f2_loopCall_reframe (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (c : Cfg body.k Bool body.State x)
    (startup startup' release release' : Bool) (flag flag' : Option Bool)
    (word word' : List Bool) (fuel : Cfg F.k Bool F.State x) (q : Option body.State) :
    f2_loopFrame body F (f2_loopCall body F anchor startup c release flag word fuel)
        (f2_loopCall body F anchor startup' {c with state := q} release' flag' word' fuel).state
        c.inputPos (fun z => if z = 0 then flag' else none) (bufferTape word')
        (bufferTape c.output) 0 c.output.length [] =
      f2_loopCall body F anchor startup' {c with state := q} release' flag' word' fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hp, hpf]
        · by_cases hb : (i : ℕ) < body.k + 1
          · have hi : (i : ℕ) < body.k := by omega
            simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hi]
          · have hn : (i : ℕ) - (body.k + 1) ≠ 0 := by omega
            simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hn]

/-- One actual-host borrow step changes only the counter, recording success
or underflow in the rewind phase. -/
private lemma f2_loopHost_borrow_step (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (pre rest : List Bool) :
    (f2_loopHost body F anchor findMode).tm.step
      (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
        (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []) =
      match rest with
      | [] => f2_loopFrame body F base (some (.inr (.inr 10))) p (bufferTape [])
          (bufferTape pre) (bufferTape []) (pre.length - 1) 0 []
      | true :: us => f2_loopFrame body F base (some (.inr (.inr 9))) p (bufferTape [])
          (bufferTape (pre ++ false :: us)) (bufferTape []) (pre.length - 1) 0 []
      | false :: us => f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ true :: us)) (bufferTape []) (pre.length + 1) 0 [] := by
  change (match (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
      (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []).workTapeSymbols
        ⟨body.k + 1, by omega⟩ with
    | some false => f2_loopControlAction body F 0 none (some (some true), .pos) (none, 0)
        none (some (.inr (.inr 8)))
    | some true => f2_loopControlAction body F 0 none (some (some false), .neg) (none, 0)
        none (some (.inr (.inr 9)))
    | none => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none
        (some (.inr (.inr 10)))).apply _ = _
  rw [f2_loopFrame_counter, f2_loopBuffer_read]
  cases rest with
  | nil =>
    simp only [List.head?]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, sub_eq_add_neg]
  | cons b rest =>
    cases b <;> simp only [List.head?]
    all_goals rw [f2_loopControl_apply]; simp [f2_loopWrite, f2_loopBuffer_write, sub_eq_add_neg]

/-- The actual host performs the borrow scan in the standalone scan's exact
time, preserving all non-counter tracks.
**Proof sketch.** Induct on the remaining word. Each false bit advances the
processed prefix. A true bit or the right blank starts the appropriate
rewind phase; no cell outside the original counter width is written. -/
private lemma f2_loopHost_borrow_run (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) : ∀ pre,
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ word)) (bufferTape []) pre.length 0 [])
        (f2_loopBorrowPos word + 1) =
      f2_loopFrame body F base (some (.inr (.inr (if (f2_loopDebit word).2 then 9 else 10)))) p
        (bufferTape []) (bufferTape (pre ++ (f2_loopDebit word).1)) (bufferTape [])
        ((pre.length : ℤ) + f2_loopBorrowPos word - 1) 0 [] := by
  induction word with
  | nil =>
    intro pre
    simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      f2_loopHost_borrow_step body F anchor findMode base p pre []
  | cons b word ih =>
    intro pre
    cases b with
    | true =>
      simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        f2_loopHost_borrow_step body F anchor findMode base p pre (true :: word)
    | false =>
      simp only [f2_loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_loopHost_borrow_step]
      simpa [f2_loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- The host's success/underflow rewind returns the counter head to zero.
Success releases the next anchor; underflow enters phase 11 without yet
emitting. Both paths retain all inactive residue.
**Proof sketch.** Induct on the number of counter cells to the left. The
left-blank test dispatches according to the stored success bit. -/
private lemma f2_loopHost_borrow_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) (success : Bool) :
    ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 []) (j + 1) =
      f2_loopFrame body F base
        (some (if success then .inr (.inl (false, (anchor, true))) else .inr (.inr 11))) p
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    cases success <;>
      (change (match (f2_loopFrame body F base _ p (bufferTape []) (bufferTape word)
          (bufferTape []) ((0 : ℤ) - 1) 0 []).workTapeSymbols ⟨body.k + 1, by omega⟩ with
        | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none _
        | none => f2_loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
    all_goals
      rw [f2_loopFrame_counter]
      simp only [zero_sub, bufferTape_left]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []) =
        f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 [] := by
      cases success <;>
        (change (match (f2_loopFrame body F base _ p (bufferTape []) (bufferTape word)
            (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []).workTapeSymbols
              ⟨body.k + 1, by omega⟩ with
          | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none _
          | none => f2_loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
      all_goals
        rw [f2_loopFrame_counter, show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
          bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
        rw [f2_loopControl_apply]
        simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- The complete actual-host counter operation has the fixed-width
worst-case bound `2|word|+2`, covering underflow and width zero. -/
private lemma f2_loopHost_borrow (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) :
    2 * f2_loopBorrowPos word + 2 ≤ 2 * word.length + 2 ∧
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape word) (bufferTape []) 0 0 []) (2 * f2_loopBorrowPos word + 2) =
      f2_loopFrame body F base
        (some (if (f2_loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) p
        (bufferTape []) (bufferTape (f2_loopDebit word).1) (bufferTape []) 0 0 [] := by
  refine ⟨by have := f2_loopBorrowPos_le word; omega, ?_⟩
  have hr := f2_loopHost_borrow_run body F anchor findMode base p word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * f2_loopBorrowPos word + 2 =
      (f2_loopBorrowPos word + 1) + (f2_loopBorrowPos word + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact f2_loopHost_borrow_rewind body F anchor findMode base p (f2_loopDebit word).1
    (f2_loopDebit word).2 _ (by rw [f2_loopDebit_length]; exact f2_loopBorrowPos_le word)

/-- The flag read is at its fixed origin, independently of inactive residue. -/
private lemma f2_loopFrame_flag (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k, by omega⟩ = flag 0 := by
  simp [f2_loopFrame, Cfg.workTapeSymbols]

/-- Clearing the only flag cell leaves a completely blank flag tape. -/
private lemma f2_loopFlag_clear (flag : Option Bool) :
    f2_loopWrite (fun z : ℤ => if z = 0 then flag else none) 0 (some none) = bufferTape [] := by
  funext z
  by_cases hz : z = 0 <;> simp [f2_loopWrite, Function.update, hz]

/-- A rejecting stopped call clears its flag, debits in worst-case width
time, and either releases the next anchor or emits exhaustion and halts.
Underflow and its emission are included in this same segment.
**Proof sketch.** Phase 7 clears the false flag in one step. The proved host
borrow takes `2j+2` steps. Success is the reframed next body seam; underflow
takes one additional phase-11 step, for at most `2|word|+4` steps in total. -/
private lemma f2_loopHost_reject (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.state = none) (ho : c.output = []) :
    ∃ t ≤ 2 * word.length + 4,
      if (f2_loopDebit word).2 then
        (f2_loopHost body F anchor findMode).tm.runFrom
            (f2_loopCall body F anchor false c false (some false) word fuel) t =
          f2_loopCall body F anchor false {c with state := some anchor} true none (f2_loopDebit word).1 fuel
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom
          (f2_loopCall body F anchor false c false (some false) word fuel) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom
          (f2_loopCall body F anchor false c false (some false) word fuel) t).output =
            (if findMode then [] else [false]) := by
  let base := f2_loopCall body F anchor false c false (some false) word fuel
  have hs : base.state = some (.inr (.inr (7 : Fin 14))) := by
    simp [base, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hc]
  have hf : base = f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos
      (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 [] := by
    have h := f2_loopCall_frame body F anchor false c false (some false) word fuel
    have hstate : (f2_loopCall body F anchor false c false (some false) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := hs
    simpa only [hstate, ho, List.length_nil, Nat.cast_zero] using h
  have hstep : (f2_loopHost body F anchor findMode).tm.step base =
      f2_loopFrame body F base (some (.inr (.inr 8))) c.inputPos
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
    conv_lhs => arg 1; rw [hf]
    change (if (f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos
        (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopFrame_flag]
    change (f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
      (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopControl_apply, f2_loopFlag_clear]
    simp [f2_loopWrite]
  have hrun : (f2_loopHost body F anchor findMode).tm.runFrom base (2 * f2_loopBorrowPos word + 3) =
      f2_loopFrame body F base
        (some (if (f2_loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) c.inputPos
        (bufferTape []) (bufferTape (f2_loopDebit word).1) (bufferTape []) 0 0 [] := by
    rw [show 2 * f2_loopBorrowPos word + 3 = (2 * f2_loopBorrowPos word + 2) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact (f2_loopHost_borrow body F anchor findMode base c.inputPos word).2
  have hw := f2_loopBorrowPos_le word
  by_cases hb : (f2_loopDebit word).2 = true
  · refine ⟨2 * f2_loopBorrowPos word + 3, by omega, ?_⟩
    simp only [hb, if_true] at hrun ⊢
    rw [hrun]
    have h := f2_loopCall_reframe body F anchor c false false false true (some false) none
      word (f2_loopDebit word).1 fuel (some anchor)
    simpa [base, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, ho] using h
  · refine ⟨2 * f2_loopBorrowPos word + 4, by omega, ?_⟩
    simp only [hb] at hrun ⊢
    have hh : (f2_loopHost body F anchor findMode).tm.runFrom base (2 * f2_loopBorrowPos word + 4) =
        f2_loopFrame body F base none c.inputPos (bufferTape []) (bufferTape (f2_loopDebit word).1)
          (bufferTape []) 0 0 (if findMode then [] else [false]) := by
      rw [show 2 * f2_loopBorrowPos word + 4 = (2 * f2_loopBorrowPos word + 3) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step', hrun]
      change (f2_loopControlAction body F 0 none (none, 0) (none, 0)
        (if findMode then none else some false) none).apply _ = _
      rw [f2_loopControl_apply]
      cases findMode <;> simp [f2_loopWrite]
    rw [hh]
    exact ⟨rfl, rfl⟩

/-- Accepting-payload phase 12 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma f2_loopHost_payload_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 12)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 13)))).apply _ = _
    rw [f2_loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 12)))
        | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 13)))).apply _ = _
      rw [f2_loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Phase 13 replays a framed payload, retaining arbitrary inactive tracks.
**Proof sketch.** Express the frame as the right-block replay configuration
using its own inactive tape and head projections, then apply the already
proved actual-host replay correspondence. -/
private lemma f2_loopHost_frame_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool) (ch : ℤ) (word : List Bool) :
    let c := f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
    ((f2_loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).state = none ∧
    ((f2_loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).output = word := by
  dsimp only
  let c := f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
  let tapes := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapes i.castSucc
  let heads := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapePos i.castSucc
  have he : c = rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
      (f2_loopReplayCfg x p (some ()) 0 word []) tapes heads := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    all_goals
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [rightCfg, Fin.addCases_left, tapes, heads]
        congr 1
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
        simp [c, rightCfg, f2_loopReplayCfg, f2_loopFrame, hf]
  change ((f2_loopHost body F anchor findMode).tm.runFrom c _).state = _ ∧
    ((f2_loopHost body F anchor findMode).tm.runFrom c _).output = _
  rw [he, f2_loopHost_replay]
  exact ⟨rfl, rfl⟩

/-- An accepting stopped call emits its fixed verdict or replays its full
captured payload, including the empty payload, within `2|output|+3` steps.
**Proof sketch.** The true stop flag dispatches acceptance independently of
payload length. Decision mode emits immediately. Find mode takes one left
move, the length-plus-one rewind, and the length-plus-one replay. -/
private lemma f2_loopHost_accept (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state = none) :
    ∃ t ≤ 2 * c.output.length + 3,
      ((f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c false (some true) word fuel) t).state = none ∧
      ((f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c false (some true) word fuel) t).output =
          (if findMode then c.output else [true]) := by
  let base := f2_loopCall body F anchor false c false (some true) word fuel
  let flag := fun z : ℤ => if z = 0 then some true else none
  have hf : base = f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
      (bufferTape word) (bufferTape c.output) 0 c.output.length [] := by
    have hstate : (f2_loopCall body F anchor false c false (some true) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := by
      simp [f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hc]
    simpa only [hstate] using f2_loopCall_frame body F anchor false c false (some true) word fuel
  have hstep : (f2_loopHost body F anchor findMode).tm.step base =
      if findMode then
        f2_loopFrame body F base (some (.inr (.inr 12))) c.inputPos flag
          (bufferTape word) (bufferTape c.output) 0 (c.output.length - 1) []
      else f2_loopFrame body F base none c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length [true] := by
    conv_lhs => arg 1; rw [hf]
    change (if (f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopFrame_flag]
    change (if findMode then
      f2_loopControlAction body F 0 none (none, 0) (none, .neg) none (some (.inr (.inr 12)))
      else f2_loopControlAction body F 0 none (none, 0) (none, 0) (some true) none).apply _ = _
    cases findMode <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [f2_loopControl_apply] <;> simp [f2_loopWrite, sub_eq_add_neg]
  cases findMode with
  | false =>
    refine ⟨1, by omega, ?_⟩
    change ((f2_loopHost body F anchor false).tm.step base).state = none ∧
      ((f2_loopHost body F anchor false).tm.step base).output = [true]
    rw [hstep]
    exact ⟨rfl, rfl⟩
  | true =>
    refine ⟨2 * c.output.length + 3, le_refl _, ?_⟩
    have hrun : (f2_loopHost body F anchor true).tm.runFrom base (2 * c.output.length + 3) =
        (f2_loopHost body F anchor true).tm.runFrom
          (f2_loopFrame body F base (some (.inr (.inr 13))) c.inputPos flag
            (bufferTape word) (bufferTape c.output) 0 0 []) (c.output.length + 1) := by
      rw [show 2 * c.output.length + 3 =
          ((c.output.length + 1) + (c.output.length + 1)) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step, hstep]
      simp only [if_true]
      rw [MultiTapeTM.runFrom_add, f2_loopHost_payload_rewind body F anchor true base
        c.inputPos flag (bufferTape word) 0 c.output [] c.output.length (le_refl _)]
    change ((f2_loopHost body F anchor true).tm.runFrom base _).state = _ ∧
      ((f2_loopHost body F anchor true).tm.runFrom base _).output = _
    rw [hrun]
    exact f2_loopHost_frame_replay body F anchor true base c.inputPos flag (bufferTape word) 0 c.output

/-- One body round plus all controller work has a uniform local bound.
Acceptance returns the exact payload/verdict; rejection either reaches the
decremented next seam or finishes underflow within the same segment.
**Proof sketch.** For acceptance, replace a padded endpoint by its first
halt, capture every emission, and use the accepting dispatch bound. At most
one symbol is emitted per source step. For rejection, the live seam supplies
the anchor-stop capture; append the complete width-bounded counter dispatch. -/
private lemma f2_loopHost_round (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s next payload : List Bool) (accepted : Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (t : ℕ) (ht : 0 < t)
    (hanchor : ∀ u, 0 < u → u < t →
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u).state ≠ some anchor)
    (hend : if accepted then
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = payload
      else body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
        Cfg.ofWords anchor (stateWord body.k next)) :
    ∃ v ≤ 3 * t + 2 * word.length + 5,
      let start := f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel
      if accepted then
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then payload else [true])
      else if (f2_loopDebit word).2 then
        (f2_loopHost body F anchor findMode).tm.runFrom start v =
          f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k next))
            true none (f2_loopDebit word).1 fuel
      else ((f2_loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then [] else [false]) := by
  dsimp only
  let start := Cfg.ofWords (input := x) anchor (stateWord body.k s)
  by_cases ha : accepted = true
  · simp only [ha, if_true] at hend ⊢
    obtain ⟨u, hu, hut, hlive, hhalt, he⟩ := f2_loop_first_halt body.tm start t (by simp [start, Cfg.ofWords]) hend.1
    have hcap := f2_loopHost_halt_return body F anchor findMode start u word fuel hu hlive
      (fun v hv hvu => hanchor v hv (by omega)) hhalt
    obtain ⟨v, hv, hstop, hout⟩ := f2_loopHost_accept body F anchor findMode (body.tm.runFrom start u) word fuel hhalt
    have hw : (body.tm.runFrom start u).output.length ≤ u := by
      simpa [start, Cfg.ofWords] using f2_loop_output_length_le body.tm start u
    refine ⟨u + v, by omega, ?_⟩
    change ((f2_loopHost body F anchor findMode).tm.runFrom
      (f2_loopCall body F anchor false start true none word fuel) (u + v)).state = _ ∧ _
    rw [MultiTapeTM.runFrom_add, hcap]
    refine ⟨hstop, ?_⟩
    rw [hout, he, hend.2]
  · simp only [ha] at hend ⊢
    have hguard : ∀ u < t, (u = 0 ∧ true = true) ∨ (body.tm.runFrom start u).state ≠ some anchor := by
      intro u hu
      by_cases hz : u = 0
      · exact Or.inl ⟨hz, rfl⟩
      · exact Or.inr (hanchor u (by omega) hu)
    have hcap := f2_loopHost_anchor_return body F anchor findMode false start true t word fuel
      (by rw [hend]; rfl)
      (by intro hz; omega) hguard
    change (f2_loopHost body F anchor findMode).tm.runFrom _ (t + 1) = _ at hcap
    have hr : body.tm.runFrom start t = Cfg.ofWords anchor (stateWord body.k next) := hend
    rw [hr] at hcap
    obtain ⟨v, hv, hfinish⟩ := f2_loopHost_reject body F anchor findMode
      {Cfg.ofWords (input := x) anchor (stateWord body.k next) with state := none} word fuel rfl rfl
    refine ⟨(t + 1) + v, by omega, ?_⟩
    change (if (f2_loopDebit word).2 then
      (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false start true none word fuel) ((t + 1) + v) = _
      else _)
    rw [MultiTapeTM.runFrom_add, hcap]
    exact hfinish

/-- At a canonical call, only the retained fuel bank can be displaced.
All body, flag, counter and capture heads are at zero. -/
private lemma f2_loopCall_heads (body F : FinTM Bool) (anchor : body.State)
    (x s word : List Bool) (fuel : Cfg F.k Bool F.State x) (B : ℕ)
    (hf : ∀ i, -(B : ℤ) ≤ fuel.workTapePos i ∧ fuel.workTapePos i ≤ B) :
    ∀ i, -(B : ℤ) ≤ (f2_loopCall body F anchor false
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos i ∧
      (f2_loopCall body F anchor false
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos i ≤ B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, Cfg.ofWords]
  · simp only [f2_loopCall, captureCfg, Fin.coe_castSucc, dif_pos j.isLt]
    change -(B : ℤ) ≤ (f2_loopBodyPadded body F anchor
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos j ∧
      (f2_loopBodyPadded body F anchor
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos j ≤ B
    simp only [f2_loopBodyPadded, leftCfg]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [Fin.addCases_left, f2_loopBodyCfg, Cfg.ofWords]
    · simp only [Fin.addCases_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]
        omega
      · simpa only [Fin.addCases_right] using hf j

/-- The audit's fixed maximum for the received phase budgets. -/
private def f2_loopHost_bound : ℕ := max 1 (max 9 (3 + 2 + 5))

/-- Configuration contracts for the concrete controller in both output modes.
**Continuation frontier: unproved.** The public corollaries below are conditional
on this one machine-construction obligation; this is not a closed batch.

**Proof sketch.** Run the relocated fuel source to its first halt using
`f2_loopHost_fuel_capture`. Phases 0--5 copy and retain its binary fuel, clear
the capture tape, and rewind the two work heads and the input head. Run
startup with `f2_loopHost_body_capture`; phase 6 clears the flag and releases
the initial seam without a debit. Define each candidate seam using the
iterated body word and `f2_loopDebit` word, retaining the fuel work residue.
`f2_loop_orbit_inv` supplies every local body premise. The body simulation and
first-halt lemmas identify the first stop; W1 preserves its full payload.
Phase 7 either emits/replays that payload or starts the width-bounded
borrow. `f2_loopBorrow_correct` is the standalone counter template to be
lifted into phases 8--10. Final zero underflow and phase 11 belong to the
last rejecting segment. If the last candidate accepts, choose any halted
false/empty terminal. Sum the phase constants with the audit's maximum
ledger. The missing proof is precisely the controller-level lifting and
assembly of these phase contracts, including startup and replay bounds. -/
/- Batch L2 closure: the preceding continuation docstring is retained as
historical evidence. Its listed obligations are discharged below by the phase
lemmas and the canonical family; there is no remaining construction admission. -/
private lemma f2_loopHost_contracts (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool) (findMode : Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ c : ℕ, ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg (f2_loopHost body F anchor findMode).k Bool
          (f2_loopHost body F anchor findMode).State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        (f2_loopHost body F anchor findMode).tm.runFrom
          ((f2_loopHost body F anchor findMode).tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = (if findMode then [] else [false]) ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            ((f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t).state = none ∧
            ((f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t).output =
              (if findMode then out x ((stepF x)^[i] (s0 x)) else [true])
          else (f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t = cfg (i + 1)) ∧
        (∀ i ≤ R x.length, ∀ j,
          -(T x.length : ℤ) ≤ (cfg i).workTapePos j ∧
          (cfg i).workTapePos j ≤ T x.length) ∧
        (∀ j, -((T x.length + c * (T x.length + 1) : ℕ) : ℤ) ≤
          (cfg (R x.length + 1)).workTapePos j ∧
          (cfg (R x.length + 1)).workTapePos j ≤
            (T x.length + c * (T x.length + 1) : ℕ)) := by
  classical
  refine ⟨f2_loopHost_bound, ?_⟩
  intro x
  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare, hfuel⟩ :=
    f2_loopHost_prepare body F anchor findMode R T hF x
  obtain ⟨btime, hbt, hbguard, hbend⟩ := hstart x
  let words (i : ℕ) := (fun w => (f2_loopDebit w).1)^[i] (Nat.bits (R x.length))
  let orbit (i : ℕ) := (stepF x)^[i] (s0 x)
  let candidate (i : ℕ) := f2_loopCall body F anchor false
    (Cfg.ofWords (input := x) anchor (stateWord body.k (orbit i))) true none (words i) fuel
  have hheads (i : ℕ) (j) :
      -(T x.length : ℤ) ≤ (candidate i).workTapePos j ∧
      (candidate i).workTapePos j ≤ T x.length :=
    f2_loopCall_heads body F anchor x (orbit i) (words i) fuel (T x.length) hfuel j
  have hwidth (i : ℕ) : (words i).length ≤ T x.length := by
    dsimp only [words]
    rw [f2_loopDebit_iterate_length]
    exact f2_loop_fuel_width F R T hF x
  have hsuccess (i : ℕ) (hi : i ≤ R x.length) :
      (f2_loopDebit (words i)).2 = true ↔ i < R x.length := by
    rw [f2_loopDebit_success]
    dsimp only [words]
    rw [f2_loopDebit_iterate_value _ _ hi]
    omega
  -- Each specified seam has its own local contract, including unreachable
  -- seams following an earlier accepting candidate.
  have hlocal : ∀ i ≤ R x.length, ∃ t ≤ f2_loopHost_bound * (T x.length + 1),
      if acceptF x (orbit i) then
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t = candidate (i + 1)
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then [] else [false]) := by
    intro i hi
    obtain ⟨t, htpos, ht, hguard, hend⟩ := hround x (orbit i)
      (f2_loop_orbit_inv Inv stepF s0 hInv0 hInvStep x i)
    obtain ⟨v, hv, hsegment⟩ := f2_loopHost_round body F anchor findMode
      (orbit i) (stepF x (orbit i)) (out x (orbit i)) (acceptF x (orbit i))
      (words i) fuel t htpos hguard hend
    refine ⟨v, ?_, ?_⟩
    · have hw := hwidth i
      change v ≤ 10 * (T x.length + 1)
      omega
    · simpa only [candidate, words, orbit, Function.iterate_succ_apply', hsuccess i hi] using hsegment
  -- Fix one segment witness per seam so the last rejecting segment's actual
  -- endpoint, including underflow and emission, is the chosen terminal.
  let time (i : ℕ) := if hi : i ≤ R x.length then (hlocal i hi).choose else 0
  have htime (i : ℕ) (hi : i ≤ R x.length) :
      time i ≤ f2_loopHost_bound * (T x.length + 1) ∧
      if acceptF x (orbit i) then
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i) = candidate (i + 1)
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then [] else [false]) := by
    simpa only [time, dif_pos hi] using (hlocal i hi).choose_spec
  have hlast := htime (R x.length) (le_refl _)
  let terminal := if acceptF x (orbit (R x.length)) then
      {candidate (R x.length + 1) with state := none, output := if findMode then [] else [false]}
    else (f2_loopHost body F anchor findMode).tm.runFrom (candidate (R x.length))
      (time (R x.length))
  have hterminal : terminal.state = none ∧ terminal.output = (if findMode then [] else [false]) := by
    dsimp only [terminal]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i ha
      simpa only [ha, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl] using hlast.2
  have hterminalheads (j) :
      -((T x.length + f2_loopHost_bound * (T x.length + 1) : ℕ) : ℤ) ≤
        terminal.workTapePos j ∧
      terminal.workTapePos j ≤ (T x.length + f2_loopHost_bound * (T x.length + 1) : ℕ) := by
    dsimp only [terminal]
    split
    · have h := hheads (R x.length + 1) j
      dsimp only
      omega
    · have hd := f2_head_steps (f2_loopHost body F anchor findMode).tm
        (candidate (R x.length)) (time (R x.length)) j
      have hs := hheads (R x.length) j
      have ht := (htime (R x.length) (le_refl _)).1
      omega
  let cfg (i : ℕ) := if i ≤ R x.length then candidate i else terminal
  have hcfg (i : ℕ) (hi : i ≤ R x.length) : cfg i = candidate i := if_pos hi
  refine ⟨cfg, ftime + (btime + 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ftime + (btime + 2) ≤ 10 * (T x.length + 1)
    omega
  · rw [hcfg 0 (Nat.zero_le _), MultiTapeTM.runFrom_add, hprepare,
      f2_loopHost_start body F anchor findMode (s0 x) btime fuel hbguard hbend]
    simp only [candidate, words, orbit, Function.iterate_zero_apply, hfo]
  · intro i hi
    rw [hcfg i hi]
    rfl
  · simpa only [cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)] using hterminal.1
  · simpa only [cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)] using hterminal.2
  · intro i hi
    have h := htime i hi
    refine ⟨time i, h.1, ?_⟩
    rw [hcfg i hi]
    change (if acceptF x (orbit i) then _ else _)
    by_cases ha : acceptF x (orbit i) = true
    · simp only [ha, if_true] at h ⊢
      simpa only [orbit] using h.2
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hlt : i < R x.length
      · rw [hcfg (i + 1) (by omega)]
        simpa only [if_pos hlt] using h.2
      · have he : i = R x.length := by omega
        subst i
        rw [show cfg (R x.length + 1) = terminal from if_neg (by omega)]
        simp only [terminal, ha, Bool.false_eq_true, ↓reduceIte]

  · intro i hi j
    rw [hcfg i hi]
    exact hheads i j
  · intro j
    rw [show cfg (R x.length + 1) = terminal from if_neg (by omega)]
    exact hterminalheads j

/-- The first accepting segment returns its own payload; an already-halted
empty-output terminal supplies exhaustion.
**Proof sketch.** Induct on the ordered candidate range. Acceptance at its
head terminates immediately. Otherwise compose the advance with the shifted
induction hypothesis; `find?_map` shifts the selected index back by one.
Thus the payload is tied to the least accepting candidate, including when
that payload is empty. -/
private lemma f2_loop_find_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (payload : ℕ → List Bool) (B N : ℕ)
    (hend : (cfg N).state = none ∧ (cfg N).output = [])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = payload j
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ N * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output =
        (match (List.range N).find? accept with | some i => payload i | none => []) := by
  induction N generalizing cfg accept payload with
  | zero => exact ⟨0, by simp, by simpa using hend⟩
  | succ N ih =>
    obtain ⟨t, ht, hc⟩ := hround 0 (by omega)
    by_cases hb : accept 0 = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · exact Nat.le_mul_of_pos_left B (by omega)
      · simpa [List.range_succ_eq_map, hb] using hc.2
    · simp only [hb] at hc
      obtain ⟨s, hs, hhalt, hout⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1))
        (fun j => payload (j + 1)) hend (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc, hout, List.range_succ_eq_map]
        simp only [List.find?_cons_of_neg hb, List.find?_map, Function.comp_def]
        cases (List.range N).find? (fun j => accept (j + 1)) <;> rfl

/-- Uniform seam positions and segment lengths confine the complete loop,
including an accepting halt and all stationary later times. No round count
occurs in the interval: every next segment restarts at a bounded seam. -/
private lemma f2_segment_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x) (N B H : ℕ)
    (hseam : ∀ j < N, ∀ i, -(H : ℤ) ≤ (cfg j).workTapePos i ∧
      (cfg j).workTapePos i ≤ H)
    (hend : (cfg N).state = none)
    (hterminal : ∀ i, -((H + B : ℕ) : ℤ) ≤ (cfg N).workTapePos i ∧
      (cfg N).workTapePos i ≤ (H + B : ℕ))
    (hsegment : ∀ j < N, ∃ u ≤ B,
      (tm.runFrom (cfg j) u).state = none ∨ tm.runFrom (cfg j) u = cfg (j + 1)) :
    ∀ t i, -((H + B : ℕ) : ℤ) ≤ (tm.runFrom (cfg 0) t).workTapePos i ∧
      (tm.runFrom (cfg 0) t).workTapePos i ≤ (H + B : ℕ) := by
  induction N generalizing cfg with
  | zero =>
    intro t i
    rw [MultiTapeTM.runFrom_of_halt _ hend]
    exact hterminal i
  | succ N ih =>
    intro t i
    obtain ⟨u, hu, he⟩ := hsegment 0 (by omega)
    have hs := hseam 0 (by omega) i
    have hp (v : ℕ) (hv : v ≤ B) :
        -((H + B : ℕ) : ℤ) ≤ (tm.runFrom (cfg 0) v).workTapePos i ∧
        (tm.runFrom (cfg 0) v).workTapePos i ≤ (H + B : ℕ) := by
      have hh := f2_head_steps tm (cfg 0) v i
      omega
    by_cases ht : t ≤ u
    · exact hp t (ht.trans hu)
    · rw [show t = u + (t - u) by omega, MultiTapeTM.runFrom_add]
      rcases he with he | he
      · rw [MultiTapeTM.runFrom_of_halt _ he]
        exact hp u hu
      · rw [he]
        exact ih (fun j => cfg (j + 1))
          (fun j hj => hseam (j + 1) (by omega)) hend hterminal
          (fun j hj => hsegment (j + 1) (by omega)) (t - u) i

/-- Convert an all-time, origin-centred trajectory bound to total space.
The inclusive interval contains every head position at every prefix. -/
private lemma f2_space_radius (M : FinTM Bool) (x : List Bool) (B : ℕ)
    (h : ∀ t i, -(B : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ B) (t : ℕ) :
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (2 * B + 1) := by
  have hc (i : Fin M.k) : M.tm.spaceUsedByTape (M.tm.initCfg x) t i ≤ 2 * B + 1 := by
    have hs : M.tm.visitedByTapeHead (M.tm.initCfg x) t i ⊆
        Finset.Icc (-(B : ℤ)) (B : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (h u i)
    exact (Finset.card_le_card hs).trans (by rw [Int.card_Icc]; omega)
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _i : Fin M.k, (2 * B + 1) := Finset.sum_le_sum (fun i _ => hc i)
    _ = _ := by simp

/-- A bounded startup followed by reusable seams has all-time space linear
in the common segment budget, independently of the number of rounds. -/
private lemma f2_seamed_space (M : FinTM Bool) (x : List Bool)
    (cfg : ℕ → Cfg M.k Bool M.State x) (N B H startup : ℕ)
    (hstart : startup ≤ B) (hinit : M.tm.runFrom (M.tm.initCfg x) startup = cfg 0)
    (hseam : ∀ j < N, ∀ i, -(H : ℤ) ≤ (cfg j).workTapePos i ∧
      (cfg j).workTapePos i ≤ H)
    (hend : (cfg N).state = none)
    (hterminal : ∀ i, -((H + B : ℕ) : ℤ) ≤ (cfg N).workTapePos i ∧
      (cfg N).workTapePos i ≤ (H + B : ℕ))
    (hsegment : ∀ j < N, ∃ u ≤ B,
      (M.tm.runFrom (cfg j) u).state = none ∨ M.tm.runFrom (cfg j) u = cfg (j + 1))
    (t : ℕ) : M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (2 * (H + B) + 1) := by
  apply f2_space_radius M x (H + B) _ t
  intro u i
  by_cases hu : u ≤ startup
  · have hp := f2_head_steps M.tm (M.tm.initCfg x) u i
    rw [show (M.tm.initCfg x).workTapePos i = 0 from rfl, zero_sub, zero_add] at hp
    omega
  · rw [show u = startup + (u - startup) by omega, MultiTapeTM.runFrom_add, hinit]
    exact f2_segment_heads M.tm cfg N B H hseam hend hterminal hsegment (u - startup) i

/-- The received result-bearing loop, retaining its reusable-seam space bound. -/
private lemma f2_exists_loopFind_space (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
          | some i => out x ((stepF x)^[i] (s0 x))
          | none => [])
        (fun n => c * (T n + 1) * (R n + 2)) ∧
      ∀ x t, E.tm.spaceUsed (E.tm.initCfg x) t ≤ c * (T x.length + 1) := by
  obtain ⟨c, hc⟩ := f2_loopHost_contracts body F anchor Inv stepF acceptF out true s0 R T
    hF hInv0 hInvStep hstart hround
  let E := f2_loopHost body F anchor true
  have ht : E.ComputesFunInTime
      (fun x => match (List.range (R x.length + 1)).find?
          (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
        | some i => out x ((stepF x)^[i] (s0 x))
        | none => []) (fun n => c * (T n + 1) * (R n + 2)) := by
    intro x
    obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments, hheads, hterminal⟩ := hc x
    obtain ⟨t, ht, hhalt, houtput⟩ := f2_loop_find_run E.tm cfg
      (fun i => acceptF x ((stepF x)^[i] (s0 x)))
      (fun i => out x ((stepF x)^[i] (s0 x))) (c * (T x.length + 1)) (R x.length + 1)
      ⟨hend, by simpa using hout⟩
      (fun j hj => by simpa using hsegments j (by omega))
    have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
    rw [hinit] at hrun
    have hcompute : E.ComputesInTime x
        (match (List.range (R x.length + 1)).find?
            (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
          | some i => out x ((stepF x)^[i] (s0 x))
          | none => []) (startup + t) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hrun]; exact hhalt
      · rw [hrun]; exact houtput
    apply hcompute.mono
    calc startup + t ≤ c * (T x.length + 1) +
          (R x.length + 1) * (c * (T x.length + 1)) := Nat.add_le_add hs ht
      _ = c * (T x.length + 1) * (R x.length + 2) := by
        rw [Nat.mul_comm (R x.length + 1)]
        simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
        omega

  let K := E.k * (2 * (c + 1) + 1)
  refine ⟨E, c + K, ?_, ?_⟩
  · intro x
    exact (ht x).mono (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  · intro x t
    obtain ⟨cfg, startup, hs, hinit, _, hend, _, hsegments, hheads, hterminal⟩ := hc x
    have h := f2_seamed_space E x cfg (R x.length + 1) (c * (T x.length + 1))
      (T x.length) startup hs hinit (fun j hj => hheads j (by omega)) hend hterminal
      (by
        intro j hj
        obtain ⟨u, hu, he⟩ := hsegments j (by omega)
        refine ⟨u, hu, ?_⟩
        split at he
        · exact Or.inl he.1
        · exact Or.inr he) t
    have hb : 2 * (T x.length + c * (T x.length + 1)) + 1 ≤
        (2 * (c + 1) + 1) * (T x.length + 1) := by
      have he : (2 * (c + 1) + 1) * (T x.length + 1) =
          2 * (T x.length + c * (T x.length + 1)) + T x.length + 3 := by ring
      omega
    calc
      _ ≤ E.k * ((2 * (c + 1) + 1) * (T x.length + 1)) :=
        h.trans (Nat.mul_le_mul_left _ hb)
      _ = K * (T x.length + 1) := by dsimp [K]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- The audited split-search step preserves every existing candidate bit;
at the one-past-end state it stalls. -/
private def f2_splitStep (w s : List Bool) : List Bool :=
  if s.length ≤ w.length then s ++ [true] else s

/-- Split-search acceptance is the exact padding length equation. -/
private def f2_splitAccept (C e : ℕ) (w s : List Bool) : Bool :=
  decide (s.length + C * (s.length + 1) ^ e = w.length)

/-- The length invariant is closed even on arbitrary candidate bit patterns. -/
private lemma f2_splitStep_inv (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    (f2_splitStep w s).length ≤ w.length + 1 := by
  unfold f2_splitStep
  split <;> simp_all <;> omega

/-- All orbit points tested by the loop are precisely the unary candidates.
**Proof sketch.** Before fuel is exhausted the current length is the iteration
index, so the step appends one true. The extra one-past-end state is included. -/
private lemma f2_splitStep_orbit (w : List Bool) : ∀ i, i ≤ w.length + 1 →
    (f2_splitStep w)^[i] [] = List.replicate i true := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [f2_splitStep, List.length_replicate, if_pos (by omega : i ≤ w.length)]
    exact (List.replicate_succ').symm

/-- Extensional equality of search predicates on the searched list preserves
both the least-success index and failure. -/
private lemma f2_catalogFind_congr {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a ∈ xs, p a = q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

/-- The orbit predicate and `solveSplit` use the same finite search, including
its unsuccessful branch. The Boolean equality is converted explicitly. -/
private lemma f2_splitFind_eq (C e : ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => f2_splitAccept C e w ((f2_splitStep w)^[i] [])) = solveSplit C e w.length := by
  apply f2_catalogFind_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [f2_splitStep_orbit w i (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [f2_splitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]

/-- Failed split search is equivalent to rejecting every candidate within fuel. -/
private lemma f2_splitFind_none (C e : ℕ) (w : List Bool) :
    solveSplit C e w.length = none ↔
      ∀ i ≤ w.length, f2_splitAccept C e w ((f2_splitStep w)^[i] []) = false := by
  rw [← f2_splitFind_eq, List.find?_eq_none]
  simp only [List.mem_range, Nat.lt_succ_iff, Bool.not_eq_true]

/-- Each successful orbit payload is exactly the split at the returned index;
exhaustion returns the same empty word on both sides. -/
private lemma f2_splitLoop_result (C e : ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => f2_splitAccept C e w ((f2_splitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((f2_splitStep w)^[i] []).length)
          (w.drop ((f2_splitStep w)^[i] []).length)
      | none => []) =
    (match solveSplit C e w.length with
      | some i => pairEncode (w.take i) (w.drop i)
      | none => []) := by
  rw [f2_splitFind_eq]
  cases hs : solveSplit C e w.length with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hs
    have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
    simp only [f2_splitStep_orbit w i (by omega), List.length_replicate]

/-- The loop overhead raises the body's polynomial exponent by exactly one.
**Proof sketch.** Bound the additive one by `(n+1)^(e+1)` and the factor `n+2`
by `2(n+1)`, then combine powers. This includes `n=0` and `e=0`. -/
private lemma f2_splitLoop_bound (c A e n : ℕ) :
    c * (A * (n + 1) ^ (e + 1) + 1) * (n + 2) ≤
      (2 * c * (A + 1)) * (n + 1) ^ (e + 2) := by
  have hp : 1 ≤ (n + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hfirst : A * (n + 1) ^ (e + 1) + 1 ≤ (A + 1) * (n + 1) ^ (e + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ c * ((A + 1) * (n + 1) ^ (e + 1)) * (2 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hfirst) (by omega)
    _ = _ := by rw [show e + 2 = (e + 1) + 1 by omega, Nat.pow_succ]; ring

/-- A physical input position after consuming a unary count, saturated at the
right boundary. -/
private def f2_splitPos (w : List Bool) (j : ℕ) : Fin (w.length + 2) :=
  ⟨min j w.length + 1, by omega⟩

/-- A saturated countdown read is blank exactly after all input bits. -/
private lemma f2_splitPos_read {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = f2_splitPos w j) :
    cfg.inputSymbol = if h : j < w.length then some (w[j]'h) else none := by
  by_cases hj : j < w.length
  · rw [dif_pos hj]
    exact inputSymbolInner j
      (by simp [hp, f2_splitPos, Nat.min_eq_left (by omega : j ≤ w.length), Nat.add_comm]) hj
  · rw [dif_neg hj]
    simp [Cfg.inputSymbol, hp, f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]

/-- A forward move increments a saturated unary countdown position. -/
private lemma f2_splitPos_succ (w : List Bool) (j : ℕ) :
    moveInputPos (f2_splitPos w j) .pos = f2_splitPos w (j + 1) := by
  by_cases hj : j < w.length
  · rw [moveInputPos_pos_of_ne_right _ (by simp [f2_splitPos] <;> omega)]
    apply Fin.ext
    simp only [f2_splitPos, Fin.val_mk]
    omega
  · have he : f2_splitPos w j = ⟨w.length + 1, by omega⟩ := by
      apply Fin.ext
      simp [f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j + 1)]

/-- A partially cleared unary scratch word, with its remaining suffix exposed. -/
private def f2_splitScratch (q j : ℕ) (z : ℤ) : Option Bool :=
  if (j : ℤ) ≤ z ∧ z < q then some true else none

/-- Clearing the exposed scratch cell advances the cleared prefix by one. -/
private lemma f2_splitScratch_erase (q j : ℕ) :
    Function.update (f2_splitScratch q j) (j : ℤ) none = f2_splitScratch q (j + 1) := by
  funext z
  by_cases hz : z = (j : ℤ)
  · subst z; simp [f2_splitScratch]
  · rw [Function.update_of_ne hz]
    have he : ((j : ℤ) ≤ z ∧ z < q) ↔ (((j + 1 : ℕ) : ℤ) ≤ z ∧ z < q) := by omega
    simp only [f2_splitScratch, he]

/-- The rejection cleanup preserves all candidate bits, appends only within
the input-length range, clears every unary scratch tape, and restores heads.
State 4 is an absorbing return seam, suitable for a first-return embedding. -/
private def f2_splitRestoreTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 5 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some none, .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (if q.2 then (none, .neg) else (some (some true), .neg))
            (fun _ => (some none, .neg)), none, some (1, false)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, false)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, false)⟩
      | 2 => controlAction .neg (some (3, false))
      | 3 => match inp with
        | some _ => controlAction .neg (some (3, false))
        | none => controlAction .pos (some (4, false))
      | _ => controlAction 0 (some (4, false)) }

/-- The clearing scan has consumed `j` candidate cells and erased exactly that
prefix on each scratch tape; the physical input tracks the same count. -/
private def f2_splitRestoreScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (f2_splitRestoreTM k).State w :=
  ⟨some (0, decide (w.length < j)), f2_splitPos w j,
    Fin.cases (bufferTape s) (fun _ => f2_splitScratch (s.length + 1) j), fun _ => j, []⟩

/-- The silent cleanup scans each candidate bit once, including false bits.
**Proof sketch.** Each transition preserves tape 0, clears one cell on every
scratch tape, and advances all heads. The overflow flag records precisely
whether more candidate cells than native input cells have been consumed. -/
private lemma f2_splitRestore_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) j =
      f2_splitRestoreScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_splitRestoreScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitRestoreScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    have hin := f2_splitPos_read w (f2_splitRestoreScan k w s j) j rfl
    unfold MultiTapeTM.step
    change ((f2_splitRestoreTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [f2_splitRestoreTM, hw]
    refine Cfg.ext ?_ (f2_splitPos_succ w j) ?_ ?_ rfl
    · change some (0, decide (w.length < j) ||
        (f2_splitRestoreScan k w s j).inputSymbol.isNone) = some (0, decide (w.length < j + 1))
      rw [hin]
      by_cases hjn : j < w.length
      · simp [hjn, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
      · simp [hjn, show w.length < j + 1 by omega]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact f2_splitScratch_erase _ _
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan]

/-- A cleaned configuration has only the candidate on tape zero; all work
heads are synchronized and the physical output is empty. -/
private def f2_splitRestoreClean (k : ℕ) (w s : List Bool)
    (q : (f2_splitRestoreTM k).State) (p : Fin (w.length + 2)) (h : ℤ) :
    Cfg (k + 1) Bool (f2_splitRestoreTM k).State w :=
  ⟨some q, p, Fin.cases (bufferTape s) (fun _ => fun _ => none), fun _ => h, []⟩

/-- The end-of-scan step clears the final extra scratch cell and appends to
tape 0 exactly when the old candidate length is at most the input length. -/
private lemma f2_splitRestore_append (k : ℕ) (w s : List Bool) :
    (f2_splitRestoreTM k).tm.step (f2_splitRestoreScan k w s s.length) =
      f2_splitRestoreClean k w (f2_splitStep w s) (1, false)
        (f2_splitPos w s.length) (s.length - 1) := by
  have hw : (f2_splitRestoreScan k w s s.length).workTapeSymbols 0 = none := by
    simp [f2_splitRestoreScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((f2_splitRestoreTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [f2_splitRestoreTM, hw]
  by_cases hs : s.length ≤ w.length
  · have hflag : decide (w.length < s.length) = false := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [Action.apply, f2_splitRestoreClean, f2_splitStep, hs] using (bufferTape_append s true).symm
      · change Function.update (f2_splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [f2_splitScratch_erase]
        funext z
        simp [f2_splitRestoreClean, f2_splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, sub_eq_add_neg]
  · have hflag : decide (w.length < s.length) = true := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, f2_splitStep, hs]
      · change Function.update (f2_splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [f2_splitScratch_erase]
        funext z
        simp [f2_splitRestoreClean, f2_splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, sub_eq_add_neg]

/-- Candidate-guided rewind restores every head, including heads on tapes
that have already been cleared. No candidate bit is altered. -/
private lemma f2_splitRestore_rewind (k : ℕ) (w s : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ s.length →
      (f2_splitRestoreTM k).tm.runFrom
        (f2_splitRestoreClean k w s (1, false) p ((j : ℤ) - 1)) (j + 1) =
        f2_splitRestoreClean k w s (2, false) p 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, f2_splitRestoreClean, f2_splitRestoreTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, f2_splitRestoreScan]
  | succ j ih =>
    intro hj
    have hs : (f2_splitRestoreTM k).tm.step
        (f2_splitRestoreClean k w s (1, false) p (((j + 1 : ℕ) : ℤ) - 1)) =
        f2_splitRestoreClean k w s (1, false) p ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, f2_splitRestoreClean, f2_splitRestoreTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Complete rejection cleanup restores exactly the audited state-word seam.
It works for arbitrary candidate bits, and its one-past-end stall is silent.
**Proof sketch.** Scan and erase `|s|` cells, handle the final scratch cell,
rewind synchronized heads along the preserved candidate, then rewind input.
The cost is at most `2|s|+|w|+5`, and every transition is silent. -/
private lemma f2_splitRestore_run (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (f2_splitStep w s)) := by
  have hlen : s.length ≤ (f2_splitStep w s).length := by
    unfold f2_splitStep
    split <;> simp
  obtain ⟨r, hr, he⟩ := f2_catalogRewind (f2_splitRestoreTM k).tm (2, false) (3, false)
    (some (4, false)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_splitRestoreClean k w (f2_splitStep w s) (2, false) (f2_splitPos w s.length) 0) rfl
  have hp : (f2_splitPos w s.length).val ≤ w.length + 1 := by simp [f2_splitPos] <;> omega
  have hfirst : (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) (s.length + 1) =
      f2_splitRestoreClean k w (f2_splitStep w s) (1, false) (f2_splitPos w s.length) (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_splitRestore_scan k w s _ (le_refl _),
      f2_splitRestore_append]
  refine ⟨(s.length + 1) + (s.length + 1) + r, ?_, ?_⟩
  · change r ≤ (f2_splitPos w s.length).val + 2 at hr
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (s.length + 1) (s.length + 1),
      hfirst, f2_splitRestore_rewind k w (f2_splitStep w s) _ _ hlen, he]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitRestoreClean, Cfg.ofWords, stateWord]
    · rfl
    · rfl

/-- Replace source emissions by native-input consumption. Tape zero retains
the candidate; the source bank occupies successor-indexed tapes. A finite
flag remembers consumption past the native right boundary. -/
private def f2_splitCountAction {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (over : Bool) (inp : Option Bool) (a : Action k Bool S) : Action (k + 1) Bool H :=
  let over' := over || (a.output.isSome && inp.isNone)
  ⟨if a.output.isSome then .pos else 0, Fin.cases (none, 0) a.workTapes, none,
    some (match a.state with | some q => emb q over' | none => ret over')⟩

/-- Source configurations use an empty virtual input and arbitrary initialized
work tapes. Their output length is consumed after the candidate's length. -/
private def f2_splitCountCfg {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) : Cfg (k + 1) Bool H w :=
  let over := decide (w.length < s.length + c.output.length)
  ⟨some (match c.state with | some q => emb q over | none => ret over),
    f2_splitPos w (s.length + c.output.length), Fin.cases (bufferTape s) c.workTapes,
    Fin.cases 0 c.workTapePos, []⟩

/-- Consuming one additional symbol updates the saturation flag exactly. -/
private lemma f2_splitCount_over {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = f2_splitPos w j) :
    (decide (w.length < j) || cfg.inputSymbol.isNone) = decide (w.length < j + 1) := by
  rw [f2_splitPos_read w cfg j hp]
  by_cases hj : j < w.length
  · simp [hj, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
  · simp [hj, show w.length < j + 1 by omega]

/-- One transformed step consumes exactly its optional source emission,
preserves the candidate, and reproduces all source-bank writes and moves.
**Proof sketch.** Split on the optional output and on tape zero versus source
tapes. The one-emission case is precisely the saturated-position increment
and overflow update; the zero-emission case leaves both unchanged. -/
private lemma f2_splitCount_apply {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) (a : Action k Bool S) :
    (f2_splitCountAction emb ret (decide (w.length < s.length + c.output.length))
      (f2_splitCountCfg emb ret w s c).inputSymbol a).apply (f2_splitCountCfg emb ret w s c) =
      f2_splitCountCfg emb ret w s (a.apply c) := by
  have hflag := f2_splitCount_over w (f2_splitCountCfg emb ret w s c)
    (s.length + c.output.length) rfl
  cases ho : a.output with
  | none =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simp [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho]
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho] using
        moveInputPos_zero (f2_splitPos w (s.length + c.output.length))
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitCountAction, f2_splitCountCfg, Action.apply]
  | some b =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        congrArg (fun flag => some (match a.state with | some q => emb q flag | none => ret flag)) hflag
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        f2_splitPos_succ w (s.length + c.output.length)
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitCountAction, f2_splitCountCfg, Action.apply]

/-- A counted source run follows the original work-bank computation exactly,
including a final emitting halt, while consuming its output on native input.
**Proof sketch.** Empty virtual input always reads blank. Apply the one-step
correspondence through the source's first halt, as in `capture_run`; the
physical output stays empty throughout. -/
private lemma f2_splitCount_run {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      f2_splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c : Cfg k Bool S []) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c j).Halted) :
    host.runFrom (f2_splitCountCfg emb ret w s c) t =
      f2_splitCountCfg emb ret w s (tm.runFrom c t) := by
  have hstep (d : Cfg k Bool S []) (hs : ¬d.Halted) :
      host.step (f2_splitCountCfg emb ret w s d) = f2_splitCountCfg emb ret w s (tm.step d) := by
    cases hq : d.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (f2_splitCountCfg emb ret w s d).state =
          some (emb q (decide (w.length < s.length + d.output.length))) := by
        simp [f2_splitCountCfg, hq]
      have hsource : d.inputSymbol = none := by
        unfold Cfg.inputSymbol
        split_ifs with h₀ h₁
        · rfl
        · rfl
        · have hp := d.inputPos.isLt
          simp only [Fin.ext_iff, Fin.val_zero] at h₀
          simp only [List.length_nil] at hp
          simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff, Fin.val_one] at h₁
          omega
      have hwork : (fun i => (f2_splitCountCfg emb ret w s d).workTapeSymbols i.succ) =
          d.workTapeSymbols := by
        funext i; simp [f2_splitCountCfg, Cfg.workTapeSymbols]
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hwork, hsource]
      exact f2_splitCount_apply emb ret w s d _
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      hstep _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- The in-file generator's loop phase ends with every unary scratch head
back at zero, ready for the restoration controller. The source input is empty;
its loop side length is supplied by the initialized work tapes.
**Proof sketch.** Run the existing exact nested-loop invariant over the full
box and then take the final halting transition. No fresh generator proof is
assumed, and the zero coefficient is included. -/
private lemma f2_splitPoly_loop_end (c C q : ℕ) (hq : 0 < q) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost q C (c + 1) + 1) =
      {f2_catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) with state := none} := by
  have hl := f2_catalogPoly_loop (c := c) (C := C) [] q hq c (by omega)
    (fun _ => 0) (by simp) [] q 0 (by omega)
  have hout : q * (C * q ^ c) = C * q ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost q C (c + 1)) =
      f2_catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) := by
    simpa [f2_catalogPolyCost, hout] using hl
  rw [MultiTapeTM.runFrom_succ_eq_step', hloop]
  simp only [MultiTapeTM.step, f2_catalogPolyCfg, f2_catalogPolyUnaryTM, Fin.val_last,
    Nat.lt_irrefl, ↓reduceDIte]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · rfl
  · funext i; simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, Action.apply, f2_catalogPolyCfg]
  · simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, Action.apply, f2_catalogPolyCfg]

/-- A run reaching an absorbing control state has a least such entry, and its
configuration at that first entry is already the final configuration.
**Proof sketch.** Choose the least hit. Absorption makes its entire suffix
constant, so the bounded endpoint identifies the first-hit configuration. -/
private lemma f2_catalogFirstEntry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (q : S) (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, z.state = some q → tm.step z = z)
    (hd : d.state = some q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some q) ∧ tm.runFrom c t = d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = some q := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = some q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- The cleanup's return seam is absorbing, so its exact restoration can be
exported with positive duration and no earlier return-state visit. -/
private lemma f2_splitRestore_first (k : ℕ) (w s : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * s.length + w.length + 5 ∧
      (∀ j < t, ((f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) j).state
        ≠ some (4, false)) ∧
      (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (f2_splitStep w s)) := by
  obtain ⟨T, hTle, hT⟩ := f2_splitRestore_run k w s
  have hfix (z : Cfg (k + 1) Bool (f2_splitRestoreTM k).State w)
      (hz : z.state = some (4, false)) : (f2_splitRestoreTM k).tm.step z = z := by
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (4, false))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  obtain ⟨t, ht, hi, he⟩ := f2_catalogFirstEntry (f2_splitRestoreTM k).tm (4, false)
    (f2_splitRestoreScan k w s 0) _ T hfix rfl hT
  refine ⟨t, ?_, ht.trans hTle, hi, he⟩
  by_contra h
  have ht0 : t = 0 := by omega
  have hstate := congrArg Cfg.state he
  simp only [ht0, MultiTapeTM.runFrom_zero, f2_splitRestoreScan, Cfg.ofWords,
    Option.some.injEq, Prod.mk.injEq] at hstate
  have hf := congrArg (fun q : (f2_splitRestoreTM k).State => q.1.val) hstate
  norm_num at hf

/-- Native countdown acceptance is exactly equality of the consumed length
and the original input length; overflow and short counts both reject. -/
private lemma f2_splitCount_accept {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) :
    (!decide (w.length < s.length + c.output.length) &&
      (f2_splitCountCfg emb ret w s c).inputSymbol.isNone) =
        decide (s.length + c.output.length = w.length) := by
  rw [f2_splitPos_read w (f2_splitCountCfg emb ret w s c) (s.length + c.output.length) rfl]
  by_cases hlt : s.length + c.output.length < w.length
  · simp [hlt, show ¬s.length + c.output.length = w.length by omega]
  · by_cases he : s.length + c.output.length = w.length
    · simp [he]
    · simp [hlt, he, show w.length < s.length + c.output.length by omega]

/-- The counted simulation can be stopped at the source's first halt without
losing the exact initialized-bank endpoint. This removes any padded halted
tail from a source time bound before entering the next controller phase. -/
private lemma f2_splitCount_firstHalt {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      f2_splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c d : Cfg k Bool S []) (T : ℕ)
    (hd : d.state = none) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (f2_splitCountCfg emb ret w s c) t = f2_splitCountCfg emb ret w s d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = none := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = none := Nat.find_spec hh
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, tm.runFrom_of_halt _ hs] at he
  refine ⟨t, ht, ?_⟩
  rw [f2_splitCount_run tm host emb ret hagree w s c t (fun j hj => Nat.find_min hh hj), ← he]

/-- Prepare the polynomial loop bank by copying the candidate's length to all
scratch tapes in parallel, adding the extra side-length cell, and rewinding
all work heads along the untouched candidate. State 2 is the return seam. -/
private def f2_splitPrepareTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some (some true), .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (none, .neg) (fun _ => (some (some true), .neg)),
            none, some (1, q.2)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, q.2)⟩
      | _ => controlAction 0 (some (2, q.2)) }

/-- During preparation, every scratch tape contains the length scanned so far. -/
private def f2_splitPrepareScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (f2_splitPrepareTM k).State w :=
  ⟨some (0, decide (w.length < j)), f2_splitPos w j,
    Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape j), fun _ => j, []⟩

/-- Preparation copies a unary side length without reading or changing any
candidate bit value. The same induction covers a candidate past native EOF. -/
private lemma f2_splitPrepare_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareScan k w s 0) j =
      f2_splitPrepareScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_splitPrepareScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitPrepareScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    unfold MultiTapeTM.step
    change ((f2_splitPrepareTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [f2_splitPrepareTM, hw]
    refine Cfg.ext ?_ (f2_splitPos_succ w j) ?_ ?_ rfl
    · exact congrArg (fun over => some (0, over))
        (f2_splitCount_over w (f2_splitPrepareScan k w s j) j rfl)
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact f2_catalogPolyTape_write j
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitPrepareScan]

/-- Prepared scratch tapes have side length `|s|+1`, with synchronized heads;
the overflow flag records the candidate's length alone. -/
private def f2_splitPrepareReady (k : ℕ) (w s : List Bool)
    (q : Fin 3) (h : ℤ) : Cfg (k + 1) Bool (f2_splitPrepareTM k).State w :=
  ⟨some (q, decide (w.length < s.length)), f2_splitPos w s.length,
    Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)), fun _ => h, []⟩

/-- Adding the extra side-length cell handles the empty candidate uniformly. -/
private lemma f2_splitPrepare_extra (k : ℕ) (w s : List Bool) :
    (f2_splitPrepareTM k).tm.step (f2_splitPrepareScan k w s s.length) =
      f2_splitPrepareReady k w s 1 (s.length - 1) := by
  have hw : (f2_splitPrepareScan k w s s.length).workTapeSymbols 0 = none := by
    simp [f2_splitPrepareScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((f2_splitPrepareTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [f2_splitPrepareTM, hw]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact f2_catalogPolyTape_write s.length
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [Action.apply, f2_splitPrepareScan, f2_splitPrepareReady, sub_eq_add_neg]

/-- Rewind the synchronized bank along the preserved candidate; each scratch
tape retains its extra cell even though the rewind uses the candidate length. -/
private lemma f2_splitPrepare_rewind (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareReady k w s 1 ((j : ℤ) - 1)) (j + 1) =
      f2_splitPrepareReady k w s 2 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, f2_splitPrepareReady, f2_splitPrepareTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_splitPrepareTM k).tm.step (f2_splitPrepareReady k w s 1 (((j + 1 : ℕ) : ℤ) - 1)) =
        f2_splitPrepareReady k w s 1 ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, f2_splitPrepareReady, f2_splitPrepareTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- From the audited state-word seam, preparation takes exactly `2(|s|+1)`
silent steps and initializes every loop head at zero. -/
private lemma f2_splitPrepare_run (k : ℕ) (w s : List Bool) :
    (f2_splitPrepareTM k).tm.runFrom
      (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) (2 * (s.length + 1)) =
      f2_splitPrepareReady k w s 2 0 := by
  have hinit : Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s) =
      f2_splitPrepareScan k w s 0 := by
    refine Cfg.ext (by simp [f2_splitPrepareScan, Cfg.ofWords]) ?_ ?_ rfl rfl
    · simp [f2_splitPrepareScan, Cfg.ofWords, f2_splitPos]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitPrepareScan, Cfg.ofWords, stateWord]
      funext z
      simp [f2_catalogPolyTape]
  have hfirst : (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareScan k w s 0) (s.length + 1) =
      f2_splitPrepareReady k w s 1 (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_splitPrepare_scan k w s _ (le_refl _), f2_splitPrepare_extra]
  rw [hinit, show 2 * (s.length + 1) = (s.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hfirst, f2_splitPrepare_rewind k w s s.length (le_refl _)]

/-- Preparation can be exposed at its first return-state entry, with no
premature visit and without changing its exact initialized-bank endpoint. -/
private lemma f2_splitPrepare_first (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (∀ j < t, ((f2_splitPrepareTM k).tm.runFrom
        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) j).state ≠
          some (2, decide (w.length < s.length))) ∧
      (f2_splitPrepareTM k).tm.runFrom
        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) t =
          f2_splitPrepareReady k w s 2 0 := by
  apply f2_catalogFirstEntry (f2_splitPrepareTM k).tm (2, decide (w.length < s.length))
  · intro z hz
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (2, decide (w.length < s.length)))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  · rfl
  · exact f2_splitPrepare_run k w s

/-- A phase trace excludes the round anchor even at its two endpoints. -/
private def f2_splitSafe {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (t : ℕ) : Prop :=
  ∀ j ≤ t, (tm.runFrom c j).state ≠ some anchor

/-- Safe traces concatenate at their literal configuration seam. -/
private lemma f2_splitSafe_add {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (u v : ℕ)
    (hu : f2_splitSafe tm anchor c u) (hv : f2_splitSafe tm anchor (tm.runFrom c u) v) :
    f2_splitSafe tm anchor c (u + v) := by
  intro j hj
  by_cases h : j ≤ u
  · exact hu j h
  · have he : j = u + (j - u) := by omega
    rw [he, MultiTapeTM.runFrom_add]
    exact hv (j - u) (by omega)

/-- Cut an absorbing source phase at its first terminal control state and
embed the entire prefix into a disjoint host phase.
**Proof sketch.** Take the least terminal visit. Absorption identifies its
configuration with the known endpoint. Induct on the prefix length using
transition agreement only before that visit; every mapped control state,
including a halted state, is different from the host anchor. -/
private lemma f2_splitEmbed_cut {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (anchor : H) (stop : S → Prop) [DecidablePred stop]
    (haway : ∀ q, emb q ≠ anchor)
    (hfix : ∀ c : Cfg k Bool S w, (∃ q, c.state = some q ∧ stop q) → tm.step c = c)
    (hagree : ∀ q, ¬stop q → ∀ inp work,
      host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (c.mapState emb) t = d.mapState emb ∧
      f2_splitSafe host anchor (c.mapState emb) t := by
  classical
  have hex : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex (by rw [hT]; exact hd)
  have he : tm.runFrom c t = d := by
    have hh := tm.runFrom_add c t (T - t)
    have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
      Function.iterate_fixed (hfix _ (Nat.find_spec hex)) _
    rw [Nat.add_sub_of_le ht, hT, hconst] at hh
    exact hh.symm
  have hp : ∀ j ≤ t, host.runFrom (c.mapState emb) j = (tm.runFrom c j).mapState emb := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
      let z := tm.runFrom c j
      change host.step (z.mapState emb) = (tm.step z).mapState emb
      cases hz : z.state with
      | none => simp [MultiTapeTM.step, Cfg.mapState, hz]
      | some q =>
        have hn : ¬stop q := fun hq => Nat.find_min hex (by omega) ⟨q, hz, hq⟩
        simp only [MultiTapeTM.step, Cfg.mapState, hz, Option.map_some]
        rw [hagree q hn]
        rfl
  refine ⟨t, ht, by rw [hp t (le_refl _), he], ?_⟩
  intro j hj
  rw [hp j hj]
  cases hs : (tm.runFrom c j).state with
  | none => simp [Cfg.mapState, hs]
  | some q => simpa [Cfg.mapState, hs] using haway q

/-- A standalone native-input rewind, with an absorbing return at state two. -/
private def f2_splitRewindTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q inp _ => match q.val with
      | 0 => controlAction .neg (some 1)
      | 1 => match inp with
        | some _ => controlAction .neg (some 1)
        | none => controlAction .pos (some 2)
      | _ => controlAction 0 (some 2) }

/-- Emit a native-input split, using tape zero only as a length counter.
The first two states double native bits, state two completes the separator,
and state three copies the native suffix. No candidate bit is emitted. -/
private def f2_splitEmitTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), some false, some 2⟩
        | some _ => ⟨0, fun _ => (none, 0), inp, some 1⟩
      | 1 => ⟨.pos, Fin.cases (none, .pos) (fun _ => (none, 0)), inp, some 0⟩
      | 2 => ⟨0, fun _ => (none, 0), some true, some 3⟩
      | _ => match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some 3⟩
        | none => controlAction 0 none }

/-- Each subroutine has its own finite control phase; only cleanup can
return to the anchor. The acceptance bit survives the native-input rewind. -/
private inductive f2_SplitBodyState (S : Type) where
  | anchor
  | prepare (q : Fin 3 × Bool)
  | count (q : S) (over : Bool)
  | check (over : Bool)
  | rewind (accept : Bool) (q : Fin 3)
  | restore (q : Fin 5 × Bool)
  | emit (q : Fin 4)

private instance f2_splitBodyStateFintype (S : Type) [Fintype S] :
    Fintype (f2_SplitBodyState S) := derive_fintype% _

/-- Equality of controller states compares only matching phases and their
finite payloads. Keep the instance private, including its generated helpers. -/
private instance f2_splitBodyStateDecidableEq (S : Type) [DecidableEq S] :
    DecidableEq (f2_SplitBodyState S) := by
  intro a b
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro h; cases h)
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.prepare.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.count.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.check.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.rewind.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.restore.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.emit.injEq _ _)))

/-- Combined round controller. The polynomial source starts on the prepared
bank, and its emissions are counted against native input without physical
output. Every seam transition is explicit, including the final anchor return. -/
private def f2_splitBodyTM (M : FinTM Bool) (start : M.State) : FinTM Bool where
  k := M.k + 1
  State := f2_SplitBodyState M.State
  tm := {
    q₀ := .anchor
    tr := fun q inp work => match q with
      | .anchor => controlAction 0 (some (.prepare (0, false)))
      | .prepare p =>
        if p.1 = 2 then controlAction 0 (some (.count start p.2))
        else ((f2_splitPrepareTM M.k).tm.tr p inp work).mapState .prepare
      | .count q over => f2_splitCountAction .count .check over inp
          (M.tm.tr q none (fun i => work i.succ))
      | .check over => controlAction 0 (some (.rewind (!over && inp.isNone) 0))
      | .rewind ok p =>
        if p = 2 then controlAction 0 (some (if ok then .emit 0 else .restore (0, false)))
        else ((f2_splitRewindTM M.k).tm.tr p inp work).mapState (.rewind ok)
      | .restore p =>
        if p = (4, false) then controlAction 0 (some .anchor)
        else ((f2_splitRestoreTM M.k).tm.tr p inp work).mapState .restore
      | .emit p => ((f2_splitEmitTM M.k).tm.tr p inp work).mapState .emit }

/-- The source bank has the candidate's successor length on each tape and
all heads at zero; its virtual input is empty. -/
private def f2_splitBank (M : FinTM Bool) (s : List Bool)
    (q : Option M.State) (out : List Bool) : Cfg M.k Bool M.State [] :=
  ⟨q, 1, fun _ => f2_catalogPolyTape (s.length + 1), fun _ => 0, out⟩

/-- The genuine initial configuration is the empty-candidate anchor seam;
there is no unproved startup work hidden in a zero-time witness. -/
private lemma f2_splitBody_start (M : FinTM Bool) (start : M.State) (w : List Bool) :
    (f2_splitBodyTM M start).tm.initCfg w =
      Cfg.ofWords .anchor (stateWord (M.k + 1) []) := by
  rw [initCfg_ofWords]
  congr 1
  funext i
  simp [stateWord]

/-- A complete source embedding commutes with every step, including halt. -/
private lemma f2_splitEmbed_run {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H) (emb : S → H)
    (hagree : ∀ q inp work, host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c : Cfg k Bool S w) (t : ℕ) :
    host.runFrom (c.mapState emb) t = (tm.runFrom c t).mapState emb := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro z
  cases hs : z.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rw [hagree]
    rfl

/-- Preparation reaches its first return with the exact counted-source bank.
Every configuration of the embedded preparation is outside the anchor phase.
**Proof sketch.** Cut the absorbing source at its first return, map its full
configuration into the preparation phase, then take the explicit dispatch.
Check the source-bank seam field by field, including the native head and flag. -/
private lemma f2_splitBody_prepare (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (f2_splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
          f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
            (f2_splitBank M s (some start) []) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        (Cfg.ofWords (input := w) (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) := by
  obtain ⟨t, ht, he, hsafe⟩ := f2_splitEmbed_cut (f2_splitPrepareTM M.k).tm
    (f2_splitBodyTM M start).tm f2_SplitBodyState.prepare .anchor (fun q => q.1 = 2)
    (by intro q; simp)
    (by
      rintro z ⟨⟨q, over⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2, over))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s))
    (f2_splitPrepareReady M.k w s 2 0) (2 * (s.length + 1))
    ⟨_, rfl, rfl⟩ (f2_splitPrepare_run M.k w s)
  have hstep : (f2_splitBodyTM M start).tm.step
      ((f2_splitPrepareReady M.k w s 2 0).mapState f2_SplitBodyState.prepare) =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
        (f2_splitBank M s (some start) []) := by
    simp only [MultiTapeTM.step, Cfg.mapState, f2_splitPrepareReady, Option.map_some,
      f2_splitBodyTM, ↓reduceIte]
    refine Cfg.ext ?_ ?_ rfl ?_ rfl
    · simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
    · simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
  have hinit : (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s)).mapState
      (f2_SplitBodyState.prepare (S := M.State)) = Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s) := rfl
  rw [hinit] at he hsafe
  have hend : (f2_splitBodyTM M start).tm.runFrom
      (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
        (f2_splitBank M s (some start) []) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', he, hstep]
  refine ⟨t, ht, hend, ?_⟩
  intro j hj
  by_cases hjt : j ≤ t
  · exact hsafe j hjt
  · have hj' : j = t + 1 := by omega
    rw [hj', hend]
    simp [f2_splitCountCfg, f2_splitBank]

/-- Counted evaluation reaches its first source halt; every prefix remains
in a count or check state and therefore cannot revisit the round anchor.
**Proof sketch.** Choose the least source halt and remove its constant halted
suffix. Apply the counted correspondence to every prefix through that halt;
its control image is disjoint from the anchor, including the return state. -/
private lemma f2_splitBody_count (M : FinTM Bool) (start : M.State) (w s : List Bool)
    (out : List Bool) (T : ℕ)
    (hT : M.tm.runFrom (f2_splitBank M s (some start) []) T = f2_splitBank M s none out) :
    ∃ t ≤ T, (f2_splitBodyTM M start).tm.runFrom
      (f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s (some start) [])) t =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s none out) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        (f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s (some start) [])) t := by
  classical
  let c := f2_splitBank M s (some start) []
  let d := f2_splitBank M s none out
  have hh : ∃ t, (M.tm.runFrom c t).state = none := ⟨T, by rw [hT]; rfl⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; rfl)
  have he : M.tm.runFrom c t = d := by
    have h := M.tm.runFrom_add c t (T - t)
    rw [Nat.add_sub_of_le ht, hT, M.tm.runFrom_of_halt _ (Nat.find_spec hh)] at h
    exact h.symm
  have hp (j : ℕ) (hj : j ≤ t) := f2_splitCount_run M.tm (f2_splitBodyTM M start).tm
    f2_SplitBodyState.count f2_SplitBodyState.check (fun _ _ _ _ => rfl) w s c j
    (fun l hl => Nat.find_min hh (by omega))
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hp t (le_refl _), he]
  · intro j hj
    rw [hp j hj]
    cases hq : (M.tm.runFrom c j).state <;> simp [f2_splitCountCfg, hq]

/-- Rewind preserves the exact source bank and physical output. Its terminal
state is cut before dispatch to the accepting emitter or rejecting cleanup.
**Proof sketch.** Use the quantitative native rewind, then cut its absorbing
return and embed that prefix while retaining the acceptance bit in control. -/
private lemma f2_splitBody_rewind (M : FinTM Bool) (start : M.State) (w : List Bool)
    (ok : Bool) (c : Cfg (M.k + 1) Bool (Fin 3) w)
    (hc : c.state = some 0) :
    ∃ t ≤ c.inputPos.val + 2,
      (f2_splitBodyTM M start).tm.runFrom (c.mapState (f2_SplitBodyState.rewind ok)) t =
        ({c with state := some (2 : Fin 3), inputPos := 1}).mapState (f2_SplitBodyState.rewind ok) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor (c.mapState (f2_SplitBodyState.rewind ok)) t := by
  obtain ⟨T, hT, he⟩ := f2_catalogRewind (f2_splitRewindTM M.k).tm (0 : Fin 3) (1 : Fin 3) (some (2 : Fin 3))
    (fun _ _ => rfl) (fun _ _ => rfl) c hc
  obtain ⟨t, ht, hend, hsafe⟩ := f2_splitEmbed_cut (f2_splitRewindTM M.k).tm
    (f2_splitBodyTM M start).tm (f2_SplitBodyState.rewind ok) .anchor (fun q => q = (2 : Fin 3))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2 : Fin 3))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    c {c with state := some (2 : Fin 3), inputPos := 1} T ⟨(2 : Fin 3), rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Rejection cleanup is embedded up to its absorbing return, so its exact
restoration and the no-anchor property hold simultaneously in the body.
**Proof sketch.** Apply the exact restoration run and cut at its absorbing
false-flag return. Its host control remains in the restore phase; the final
transition to the anchor is accounted for separately by the round proof. -/
private lemma f2_splitBody_restore (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (f2_splitBodyTM M start).tm.runFrom
        ((f2_splitRestoreScan M.k w s 0).mapState f2_SplitBodyState.restore) t =
        Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (f2_splitStep w s)) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        ((f2_splitRestoreScan M.k w s 0).mapState f2_SplitBodyState.restore) t := by
  obtain ⟨T, hT, he⟩ := f2_splitRestore_run M.k w s
  obtain ⟨t, ht, hend, hsafe⟩ := f2_splitEmbed_cut (f2_splitRestoreTM M.k).tm
    (f2_splitBodyTM M start).tm f2_SplitBodyState.restore .anchor (fun q => q = (4, false))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (4, false))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    (f2_splitRestoreScan M.k w s 0)
    (Cfg.ofWords (4, false) (stateWord (M.k + 1) (f2_splitStep w s))) T
    ⟨_, rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Emitter configurations preserve the initialized scratch bank and use the
candidate head only to count the doubled native prefix. -/
private def f2_splitEmitCfg (k : ℕ) (w s : List Bool) (q : Option (Fin 4))
    (j h : ℕ) (out : List Bool) : Cfg (k + 1) Bool (Fin 4) w :=
  ⟨q, f2_splitPos w j, Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)),
    Fin.cases (h : ℤ) (fun _ => 0), out⟩

/-- Two transitions emit two copies of the current native bit and advance
both the native head and the candidate counter. Arbitrary candidate bit
values are read only for their presence.
**Proof sketch.** Induct on the number of doubled cells. The two transitions
read the same native bit, emit it twice, and only then advance both heads. -/
private lemma f2_splitEmit_double (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    ∀ j, j ≤ s.length → (f2_splitEmitTM k).tm.runFrom
      (f2_splitEmitCfg k w s (some 0) 0 0 []) (2 * j) =
      f2_splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread (q : Fin 4) (out : List Bool) :
        (f2_splitEmitCfg k w s (some q) j j out).inputSymbol = some (w[j]'(by omega)) := by
      rw [f2_splitPos_read w _ j rfl, dif_pos (by omega)]
    have hwork : (f2_splitEmitCfg k w s (some 0) j j
        ((w.take j).flatMap fun b => [b, b])).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitEmitCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < s.length)]
    have hfirst : (f2_splitEmitTM k).tm.step
        (f2_splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b])) =
        f2_splitEmitCfg k w s (some 1) j j
          (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change ((f2_splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
      simp only [f2_splitEmitTM, hwork, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, f2_splitEmitCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (1 : Fin 4) _ _).apply _ = _
    simp only [f2_splitEmitTM, hread]
    refine Cfg.ext rfl (f2_splitPos_succ w j) ?_ ?_ ?_
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp [Action.apply, f2_splitEmitCfg]
    · change (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) ++
          [w[j]'(by omega)] = (w.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < w.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Once the counter is exhausted, emit the two separator bits without
moving the native head away from the beginning of the suffix. -/
private lemma f2_splitEmit_separator (k : ℕ) (w s : List Bool) (out : List Bool) :
    (f2_splitEmitTM k).tm.runFrom (f2_splitEmitCfg k w s (some 0) s.length s.length out) 2 =
      f2_splitEmitCfg k w s (some 3) s.length s.length (out ++ [false, true]) := by
  have hwork : (f2_splitEmitCfg k w s (some 0) s.length s.length out).workTapeSymbols 0 = none := by
    simp [f2_splitEmitCfg, Cfg.workTapeSymbols]
  have hf : (f2_splitEmitTM k).tm.step (f2_splitEmitCfg k w s (some 0) s.length s.length out) =
      f2_splitEmitCfg k w s (some 2) s.length s.length (out ++ [false]) := by
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
    simp only [f2_splitEmitTM, hwork]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, f2_splitEmitCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step,
    show (f2_splitEmitTM k).tm.step _ = _ from hf, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext i; simp [MultiTapeTM.step, f2_splitEmitTM, Action.apply, f2_splitEmitCfg]
  · simp [MultiTapeTM.step, f2_splitEmitTM, Action.apply, f2_splitEmitCfg, List.append_assoc]

/-- The suffix-copy phase preserves all work tapes and copies native bits
verbatim, including the empty suffix and its final blank-reading halt.
**Proof sketch.** Induct on the remaining suffix while allowing arbitrary
already-copied prefix and output. The nonempty case copies one native bit;
the empty case reads the right blank and halts without an extra emission. -/
private lemma f2_splitEmit_suffix (k : ℕ) (w s rest : List Bool) :
    ∀ pre out h, w = pre ++ rest → (f2_splitEmitTM k).tm.runFrom
      (f2_splitEmitCfg k w s (some 3) pre.length h out) (rest.length + 1) =
      f2_splitEmitCfg k w s none w.length h (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out h hw
    have he : w = pre := by simpa using hw
    clear hw
    subst w
    simp only [List.append_nil, List.length_nil, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := f2_splitPos_read pre (f2_splitEmitCfg k pre s (some 3) pre.length h out) pre.length rfl
    simp only [Nat.lt_irrefl, ↓reduceDIte] at hr
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [hr]
    simp [f2_splitEmitTM, controlAction, f2_splitEmitCfg]
  | cons b rest ih =>
    intro pre out h hw
    have hread : (f2_splitEmitCfg k w s (some 3) pre.length h out).inputSymbol = some b := by
      rw [f2_splitPos_read w _ pre.length rfl]
      simp [hw]
    have hstep : (f2_splitEmitTM k).tm.step (f2_splitEmitCfg k w s (some 3) pre.length h out) =
        f2_splitEmitCfg k w s (some 3) (pre ++ [b]).length h (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((f2_splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
      rw [hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using f2_splitPos_succ w pre.length
      · funext i; simp [f2_splitEmitTM, Action.apply, f2_splitEmitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) h (by simpa [List.append_assoc] using hw)

/-- The accepting emitter produces exactly the encoded native split in
`|s|+|w|+3` steps. Its candidate may contain any bit pattern.
**Proof sketch.** Double exactly the native prefix counted by the candidate,
emit the separator, and copy the remaining native suffix. Concatenate the
three exact runs and cancel the prefix length in the time expression. -/
private lemma f2_splitEmit_run (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    (f2_splitEmitTM k).tm.runFrom (f2_splitEmitCfg k w s (some 0) 0 0 [])
      (s.length + w.length + 3) =
      f2_splitEmitCfg k w s none w.length s.length
        (pairEncode (w.take s.length) (w.drop s.length)) := by
  have ht : s.length + w.length + 3 =
      2 * s.length + 2 + ((w.drop s.length).length + 1) := by
    simp only [List.length_drop]; omega
  rw [ht, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add _ (2 * s.length) 2,
    f2_splitEmit_double k w s hs _ (le_refl _), f2_splitEmit_separator]
  have h := f2_splitEmit_suffix k w s (w.drop s.length) (w.take s.length)
    (((w.take s.length).flatMap fun b => [b, b]) ++ [false, true]) s.length
    (List.take_append_drop s.length w).symm
  simpa [List.length_take, Nat.min_eq_left hs, pairEncode] using h

/-- A single transition is safe when both its endpoints exclude the anchor. -/
private lemma f2_splitSafe_one {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S w)
    (he : tm.step c = d) (hc : c.state ≠ some anchor) (hd : d.state ≠ some anchor) :
    tm.runFrom c 1 = d ∧ f2_splitSafe tm anchor c 1 := by
  refine ⟨he, ?_⟩
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact hc
  · change (tm.step c).state ≠ _
    rw [he]; exact hd

/-- Concatenate two safe exact phase runs. -/
private lemma f2_splitSafe_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d f : Cfg k Bool S w) (u v : ℕ)
    (h1 : tm.runFrom c u = d) (hs1 : f2_splitSafe tm anchor c u)
    (h2 : tm.runFrom d v = f) (hs2 : f2_splitSafe tm anchor d v) :
    tm.runFrom c (u + v) = f ∧ f2_splitSafe tm anchor c (u + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h1, h2], ?_⟩
  apply f2_splitSafe_add tm anchor c u v hs1
  rw [h1]; exact hs2

/-- A completed source gives a complete body round, including acceptance,
rejection, positive duration, and anchor exclusion over every strict interior
step. The bound explicitly includes all dispatches, rewinds, and emission.
**Proof sketch.** Depart the anchor in one step. Concatenate safe preparation,
counting, decision, and rewind traces. Equality accepts and emits native
slices. Inequality dispatches to the exact scratch restoration, followed by
one explicit return to the anchor. All intermediate states belong to disjoint
phases; the only anchor step is the final rejecting transition. -/
private lemma f2_splitBody_round (M : FinTM Bool) (start : M.State) (w s out : List Bool)
    (T : ℕ) (hT : M.tm.runFrom (f2_splitBank M s (some start) []) T = f2_splitBank M s none out) :
    ∃ t, 0 < t ∧ t ≤ T + 5 * s.length + 3 * w.length + 20 ∧
      (∀ j, 0 < j → j < t →
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) j).state ≠ some .anchor) ∧
      if decide (s.length + out.length = w.length) then
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).state = none ∧
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
      else (f2_splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t =
          Cfg.ofWords .anchor (stateWord (M.k + 1) (f2_splitStep w s)) := by
  let tm := (f2_splitBodyTM M start).tm
  let z : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    Cfg.ofWords .anchor (stateWord (M.k + 1) s)
  let p : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)
  let d := f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s none out)
  let ok := decide (s.length + out.length = w.length)
  let c : Cfg (M.k + 1) Bool (Fin 3) w :=
    ⟨some 0, f2_splitPos w (s.length + out.length),
      Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)),
      Fin.cases 0 (fun _ => 0), []⟩
  let r : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    ({c with state := some (2 : Fin 3), inputPos := 1} : Cfg (M.k + 1) Bool (Fin 3) w).mapState
    (f2_SplitBodyState.rewind (S := M.State) ok)
  have hdepart : tm.runFrom z 1 = p := by
    change (controlAction 0 (some (.prepare (0, false)))).apply z = p
    rw [controlAction_apply, moveInputPos_zero]
    rfl
  obtain ⟨a, ha, hprep, hpreps⟩ := f2_splitBody_prepare M start w s
  obtain ⟨b, hb, hcount, hcounts⟩ := f2_splitBody_count M start w s out T hT
  obtain ⟨h1, hs1⟩ := f2_splitSafe_join tm .anchor p _ d (a + 1) b hprep hpreps hcount hcounts
  have hcheck : tm.step d = c.mapState (f2_SplitBodyState.rewind ok) := by
    unfold MultiTapeTM.step
    change (controlAction 0 (some (.rewind
      (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) 0))).apply d = _
    rw [controlAction_apply, moveInputPos_zero]
    have hok := f2_splitCount_accept f2_SplitBodyState.count f2_SplitBodyState.check w s
      (f2_splitBank M s none out)
    change (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) = ok at hok
    rw [hok]
    rfl
  obtain ⟨hcheck', hchecks⟩ := f2_splitSafe_one tm .anchor d _ hcheck
    (by simp [d, f2_splitCountCfg, f2_splitBank]) (by simp [c, Cfg.mapState])
  obtain ⟨h2, hs2⟩ := f2_splitSafe_join tm .anchor p d _ (a + 1 + b) 1 h1 hs1 hcheck' hchecks
  obtain ⟨v, hv, hrew, hrews⟩ := f2_splitBody_rewind M start w ok c rfl
  obtain ⟨h3, hs3⟩ := f2_splitSafe_join tm .anchor p _ r (a + 1 + b + 1) v h2 hs2 hrew hrews
  have hv' : v ≤ w.length + 3 := by
    have hp : c.inputPos.val ≤ w.length + 1 := by simp [c, f2_splitPos]
    omega
  by_cases hok : s.length + out.length = w.length
  · have hs : s.length ≤ w.length := by omega
    let ec := f2_splitEmitCfg M.k w s (some 0) 0 0 []
    let ed := f2_splitEmitCfg M.k w s none w.length s.length
      (pairEncode (w.take s.length) (w.drop s.length))
    have hdispatch : tm.step r = ec.mapState f2_SplitBodyState.emit := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, f2_splitBodyTM, ↓reduceIte, ok, hok, decide_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext rfl ?_ rfl rfl rfl
      simp [ec, f2_splitEmitCfg, f2_splitPos]
    obtain ⟨hd, hds⟩ := f2_splitSafe_one tm .anchor r _ hdispatch
      (by simp [r, Cfg.mapState]) (by simp [ec, Cfg.mapState, f2_splitEmitCfg])
    obtain ⟨h4, hs4⟩ := f2_splitSafe_join tm .anchor p r _ (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    have hemit : tm.runFrom (ec.mapState f2_SplitBodyState.emit) (s.length + w.length + 3) =
        ed.mapState f2_SplitBodyState.emit := by
      rw [f2_splitEmbed_run (f2_splitEmitTM M.k).tm tm f2_SplitBodyState.emit (fun _ _ _ => rfl)]
      exact congrArg (Cfg.mapState f2_SplitBodyState.emit) (f2_splitEmit_run M.k w s hs)
    have hemits : f2_splitSafe tm .anchor (ec.mapState f2_SplitBodyState.emit) (s.length + w.length + 3) := by
      intro j hj
      rw [f2_splitEmbed_run (f2_splitEmitTM M.k).tm tm f2_SplitBodyState.emit (fun _ _ _ => rfl)]
      cases hq : ((f2_splitEmitTM M.k).tm.runFrom ec j).state <;> simp [Cfg.mapState, hq]
    obtain ⟨h5, hs5⟩ := f2_splitSafe_join tm .anchor p _ _ (a + 1 + b + 1 + v + 1)
      (s.length + w.length + 3) h4 hs4 hemit hemits
    let u := a + 1 + b + 1 + v + 1 + (s.length + w.length + 3)
    have hend : tm.runFrom z (1 + u) = ed.mapState f2_SplitBodyState.emit := by
      rw [MultiTapeTM.runFrom_add, hdepart]; exact h5
    refine ⟨1 + u, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_true, ↓reduceIte]
      change (tm.runFrom z (1 + u)).state = none ∧ _
      rw [hend]
      exact ⟨rfl, rfl⟩
  · let rc := (f2_splitRestoreScan M.k w s 0).mapState (f2_SplitBodyState.restore (S := M.State))
    have hdispatch : tm.step r = rc := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, f2_splitBodyTM, ↓reduceIte, ok, hok, decide_false, Bool.false_eq_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext ?_ ?_ ?_ ?_ rfl
      · simp [rc, f2_splitRestoreScan, Cfg.mapState]
      · simp [rc, f2_splitRestoreScan, Cfg.mapState, f2_splitPos]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · rfl
        · funext z; simp [rc, f2_splitRestoreScan, Cfg.mapState, f2_splitScratch, f2_catalogPolyTape]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    obtain ⟨hd, hds⟩ := f2_splitSafe_one tm .anchor r rc hdispatch
      (by simp [r, Cfg.mapState]) (by simp [rc, Cfg.mapState, f2_splitRestoreScan])
    obtain ⟨h4, hs4⟩ := f2_splitSafe_join tm .anchor p r rc (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    obtain ⟨l, hl, hrest, hrests⟩ := f2_splitBody_restore M start w s
    obtain ⟨h5, hs5⟩ := f2_splitSafe_join tm .anchor p rc _ (a + 1 + b + 1 + v + 1) l h4 hs4 hrest hrests
    let u := a + 1 + b + 1 + v + 1 + l
    have hreturn : tm.step (Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (f2_splitStep w s))) =
        Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) (f2_splitStep w s)) := by
      change (controlAction 0 (some (f2_SplitBodyState.anchor (S := M.State)))).apply _ = _
      rw [controlAction_apply, moveInputPos_zero]
      rfl
    refine ⟨1 + u + 1, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_false, Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (1 + u + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hdepart, h5, hreturn]

/-- Given the concrete startup and round contracts, the audited loop supplies
the frozen split-search result and exponent. No body contract is assumed as an
axiom: both are explicit arguments, including the positive silent stall.
**Proof sketch.** Enlarge the body coefficient to cover the existing binary
length machine, instantiate the proved loop, identify its unary orbit and
finite search, then apply the checked exponent calculation. -/
private lemma f2_splitSolve_of_body (C e : ℕ) (body : FinTM Bool) (anchor : body.State)
    (A : ℕ)
    (hstart : ∀ w : List Bool, ∃ t ≤ A * (w.length + 1) ^ (e + 1),
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg w) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg w) t =
        Cfg.ofWords anchor (stateWord body.k []))
    (hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ A * (w.length + 1) ^ (e + 1) ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if f2_splitAccept C e w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (f2_splitStep w s))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  obtain ⟨F, a, hF, _⟩ := computesFunInTime_lengthBits_spaceUsed
  have hn (n : ℕ) : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hbody (n : ℕ) : A * (n + 1) ^ (e + 1) ≤ (A + a) * (n + 1) ^ (e + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hF' : F.ComputesFunInTime (fun w => Nat.bits w.length)
      (fun n => (A + a) * (n + 1) ^ (e + 1)) := by
    intro w
    apply (hF w).mono
    exact (Nat.mul_le_mul_left a (hn w.length)).trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨M, c, hM, hspace⟩ := f2_exists_loopFind_space body F anchor
    (fun w s => s.length ≤ w.length + 1) f2_splitStep (f2_splitAccept C e)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (n + 1) ^ (e + 1)) hF'
    (by intro w; simp) f2_splitStep_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, htpos, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * c * (A + a + 1), ?_, ?_⟩
  · intro w
    have hm := hM w
    dsimp only [id_eq] at hm
    convert hm.mono (f2_splitLoop_bound c (A + a) e w.length) using 1
    exact (f2_splitLoop_result C e w).symm

  · intro x t
    have h := hspace x t
    have hp : 1 ≤ (x.length + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hb : (A + a) * (x.length + 1) ^ (e + 1) + 1 ≤
        (A + a + 1) * (x.length + 1) ^ (e + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    calc
      _ ≤ c * ((A + a + 1) * (x.length + 1) ^ (e + 1)) :=
        h.trans (Nat.mul_le_mul_left c hb)
      _ = (c * (A + a + 1)) * (x.length + 1) ^ (e + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (by omega : c ≤ 2 * c))

/-- The positive-exponent source is the already proved nested-loop phase,
started on the prepared bank rather than rerunning input initialization. -/
private lemma f2_splitSource_poly (c C : ℕ) (s : List Bool) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_splitBank (f2_catalogPolyUnaryTM c C) s (some (.loop (Fin.last c))) [])
      (f2_catalogPolyCost (s.length + 1) C (c + 1) + 1) =
      f2_splitBank (f2_catalogPolyUnaryTM c C) s none
        (List.replicate (C * (s.length + 1) ^ (c + 1)) true) := by
  simpa [f2_splitBank, f2_catalogPolyCfg] using f2_splitPoly_loop_end c C (s.length + 1) (by omega)

/-- Exponent zero uses the fixed prefix source on empty virtual input, with
no scratch tapes. Its last blank-reading step is included in the bound. -/
private lemma f2_splitSource_constant (C : ℕ) (s : List Bool) :
    (f2_catalogPrefixTM (List.replicate C true)).tm.runFrom
      (f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) []) (C + 1) =
      f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s none (List.replicate C true) := by
  have hi : f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) [] =
      (f2_catalogPrefixTM (List.replicate C true)).tm.initCfg [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step']
  have he := f2_catalogPrefixTM_emit (List.replicate C true) [] C (by simp)
  rw [he]
  simp only [List.take_replicate, Nat.min_self]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, f2_catalogPrefixTM, f2_catalogPrefixCfg, Cfg.inputSymbol,
      Fin.ext_iff, Action.apply, f2_splitBank]

/-- The invariant bounds every candidate, including the one-past-end stall,
inside one common body envelope. The factor `2^e` covers the prepared side
length `|s|+1 ≤ 2(|w|+1)` without increasing the exponent.
**Proof sketch.** Bound the source by its proved box cost, compare the two
side lengths, and absorb all linear controller overhead into forty copies of
the positive polynomial envelope. -/
private lemma f2_splitBody_envelope (C e l n T : ℕ) (hl : l ≤ n + 1)
    (hT : T ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    T + 5 * l + 3 * n + 20 ≤
      ((C + 1 + 5 * e) * 2 ^ e + 40) * (n + 1) ^ (e + 1) := by
  have hp : (l + 1) ^ e ≤ 2 ^ e * (n + 1) ^ (e + 1) := by
    calc
      (l + 1) ^ e ≤ (2 * (n + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
      _ = 2 ^ e * (n + 1) ^ e := Nat.mul_pow _ _ _
      _ ≤ 2 ^ e * (n + 1) ^ (e + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hmul := Nat.mul_le_mul_left (C + 1 + 5 * e) hp
  have hn : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hlin : 5 * l + 3 * n + 21 ≤ 40 * (n + 1) ^ (e + 1) := by omega
  calc
    T + 5 * l + 3 * n + 20 ≤
        (C + 1 + 5 * e) * (2 ^ e * (n + 1) ^ (e + 1)) +
          40 * (n + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- Instantiate the completed controller with an exact unary-output source.
The source assumption is discharged below separately for zero and positive
exponents; startup and the full body round have already been constructed.
**Proof sketch.** Supply the exact zero-time startup and constructed round to
the existing loop closure. The common envelope bounds the actual phase times,
and the source's unary-output length identifies the checked acceptance test. -/
private lemma f2_splitSolve_source (C e : ℕ) (M : FinTM Bool) (start : M.State)
    (B : ℕ → ℕ)
    (hsource : ∀ s : List Bool, M.tm.runFrom (f2_splitBank M s (some start) []) (B s.length) =
      f2_splitBank M s none (List.replicate (C * (s.length + 1) ^ e) true))
    (hbound : ∀ l, B l ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    ∃ (N : FinTM Bool) (c : ℕ),
      N.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, N.tm.spaceUsed (N.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  apply f2_splitSolve_of_body C e (f2_splitBodyTM M start) .anchor
    ((C + 1 + 5 * e) * 2 ^ e + 40)
  · intro w
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j hj; omega
    · exact f2_splitBody_start M start w
  · intro w s hs
    obtain ⟨t, htpos, ht, hsafe, hend⟩ := f2_splitBody_round M start w s
      (List.replicate (C * (s.length + 1) ^ e) true) (B s.length) (hsource s)
    refine ⟨t, htpos, ht.trans (f2_splitBody_envelope C e s.length w.length (B s.length)
      hs (hbound s.length)), hsafe, ?_⟩
    simpa only [f2_splitAccept, List.length_replicate] using hend

/-- Close the two exponent cases privately, so compiler-generated proof
helpers also remain private. Both cases instantiate the concrete body and
its proved round contract through the exact source interfaces. -/
private lemma f2_splitSolve_closed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  cases e with
  | zero =>
    apply f2_splitSolve_source C 0 (f2_catalogPrefixTM (List.replicate C true))
      (0 : Fin ((List.replicate C true).length + 1)) (fun _ => C + 1)
    · intro s
      simpa using f2_splitSource_constant C s
    · intro l; simp
  | succ e =>
    apply f2_splitSolve_source C (e + 1) (f2_catalogPolyUnaryTM e C) (.loop (Fin.last e))
      (fun l => f2_catalogPolyCost (l + 1) C (e + 1) + 1)
    · exact f2_splitSource_poly e C
    · intro l
      exact Nat.add_le_add_right (f2_catalogPolyCost_le (l + 1) C (by omega) (e + 1)) 1

/-- **P15 space row, split search** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_splitSolve`). The padding
split search runs in space one polynomial degree below its time: per
candidate it rebuilds unary banks of size at most `C·(n+1)^e` in place,
and candidates reuse the same banks.

**Proof sketch.** Head-movement count of the loop body's phases: the
candidate banks and the generator's output bank are rebuilt in place
every round (the round seam restores heads to the origin), so the
per-tape visited sets are intervals of length at most the largest bank,
`C·(n+1)^e` cells plus linear administration; the round count multiplies
time, not space. -/
theorem computesFunInTime_splitSolve_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  exact f2_splitSolve_closed C e

/- Local copies of the W2 correspondence from Build/Wrappers.lean.
The originals are private; the all-time trajectory is needed for the space row. -/
/-- Map a source state and its last-emission register to simulation, halt,
or the stationary live loop. An empty register never matches a bit. -/
private def catalog_redirectState {S : Type} (haltOn : Bool) (q : Option S)
    (r : Option Bool) : Option ((S × Option Bool) ⊕ Unit) :=
  match q with
  | some s => some (.inl (s, r))
  | none => if r = some haltOn then none else some (.inr ())

/-- Suppress physical emission, updating the register before the halt test. -/
private def catalog_redirectAction {k : ℕ} {S : Type} (haltOn : Bool)
    (a : Action k Bool S) (r : Option Bool) : Action k Bool ((S × Option Bool) ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, none, catalog_redirectState haltOn a.state (a.output.or r)⟩

/-- The source tapes and input head are unchanged; its last emitted bit is
remembered in control and the physical output is empty. -/
private def catalog_redirectCfg (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Cfg (redirectTM M haltOn).k Bool
      (redirectTM M haltOn).State x :=
  ⟨catalog_redirectState haltOn c.state c.output.getLast?, c.inputPos,
    c.workTapes, c.workTapePos, []⟩

/-- The stationary live loop is fixed by every subsequent transition. -/
private lemma catalog_redirect_loop (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg (redirectTM M haltOn).k Bool (redirectTM M haltOn).State x)
    (hs : c.state = some (.inr ())) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    apply Cfg.ext <;> simp [MultiTapeTM.step, hs, redirectTM, Action.apply]

/-- Capture and application commute because the last entry of an appended
singleton is the new bit, while no emission leaves the old register intact. -/
private lemma catalog_redirect_apply (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
    (catalog_redirectAction haltOn a c.output.getLast?).apply (catalog_redirectCfg M haltOn c) =
      catalog_redirectCfg M haltOn (a.apply c) := by
  have hlast : (c.output ++ a.output.toList).getLast? = a.output.or c.output.getLast? := by
    cases a.output <;> simp
  refine Cfg.ext ?_ rfl rfl rfl rfl
  dsimp only [catalog_redirectCfg, catalog_redirectAction, Action.apply]
  rw [hlast]

/-- The correspondence also holds after a source halt: a matching result
is absorbed as halted, and a mismatching result is absorbed in the live loop.
This adapts `acceptCfg_step` in the HALT reduction to an optional register. -/
private lemma catalog_redirect_step (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    (redirectTM M haltOn).tm.step (catalog_redirectCfg M haltOn c) =
      catalog_redirectCfg M haltOn (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    by_cases hr : c.output.getLast? = some haltOn
    · exact MultiTapeTM.step_of_halt (by simp [catalog_redirectCfg, catalog_redirectState, hs, hr])
    · exact catalog_redirect_loop M haltOn (catalog_redirectCfg M haltOn c)
        (by simp [catalog_redirectCfg, catalog_redirectState, hs, hr]) 1
  | some q =>
    have hi : (catalog_redirectCfg M haltOn c).inputSymbol = c.inputSymbol := rfl
    have hw : (catalog_redirectCfg M haltOn c).workTapeSymbols = c.workTapeSymbols := rfl
    have hstate : (catalog_redirectCfg M haltOn c).state = some (.inl (q, c.output.getLast?)) := by
      simp only [catalog_redirectCfg, catalog_redirectState, hs]
    simp only [MultiTapeTM.step, hstate, hs]
    rw [hi, hw]
    have htr : (redirectTM M haltOn).tm.tr (.inl (q, c.output.getLast?))
        c.inputSymbol c.workTapeSymbols =
        catalog_redirectAction haltOn (M.tm.tr q c.inputSymbol c.workTapeSymbols) c.output.getLast? := by
      cases hq : (M.tm.tr q c.inputSymbol c.workTapeSymbols).state <;>
        cases ho : (M.tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
          simp [redirectTM, catalog_redirectAction, catalog_redirectState, hq, ho]
    rw [htr]
    exact catalog_redirect_apply M haltOn c _

/-- Initialized runs commute with redirection at every time, including
after a source halt. This is the last-emission invariant for both clauses. -/
private lemma catalog_redirect_run (M : FinTM Bool) (haltOn : Bool) (x : List Bool) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t =
      catalog_redirectCfg M haltOn (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hi : (redirectTM M haltOn).tm.initCfg x = catalog_redirectCfg M haltOn (M.tm.initCfg x) := rfl
  rw [hi]
  exact MultiTapeTM.runFrom_comm_of_step (catalog_redirectCfg M haltOn) (catalog_redirect_step M haltOn)
    (M.tm.initCfg x) t


/-- **W2 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.redirectTM` beside its
`redirectTM_computes`/`redirectTM_live` contract pair). Redirection costs
no space, per tape and exactly: the redirected machine's tape actions are
the source's verbatim, before and after the source halt.

**Proof sketch.** `redirect_run`'s configuration correspondence preserves
work tapes and heads at every time (the live loop is stationary and the
simulation phase copies the source's tape actions), so the two head
trajectories coincide pointwise and the visited images agree. -/
theorem redirectTM_spaceUsedByTape (M : FinTM Bool) (haltOn : Bool)
    (x : List Bool) (t : ℕ) (i : Fin M.k) :
    (redirectTM M haltOn).tm.spaceUsedByTape
        ((redirectTM M haltOn).tm.initCfg x) t i
      = M.tm.spaceUsedByTape (M.tm.initCfg x) t i := by
  unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
  congr 1
  apply Finset.image_congr
  intro u _
  dsimp only
  rw [catalog_redirect_run]
  rfl

/-- Pad the decider with the fresh branch tapes. The added tapes are idle,
so the public left-block simulation supplies its complete run invariant. -/
private def f2_timedPadTM (D : FinTM Bool) (r : ℕ) : MultiTapeTM (D.k + r) Bool D.State where
  q₀ := D.tm.q₀
  tr q inp work := leftAction r id (D.tm.tr q inp (fun i => work (Fin.castAdd r i)))

/-- The conditional controller captures the decider on the last tape,
steps back to read its singleton verdict, rewinds the physical input, then
runs the selected branch on its untouched tape bank. In the administrative
states, the first Boolean distinguishes back/read and the second distinguishes
rewind-start/scan. The branch transition table is independent of its selector. -/
private def f2_timedCondTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := (D.k + (M₁.k + M₂.k)) + 1
  State := D.State ⊕ (Bool ⊕ ((Bool × Bool) ⊕ (M₁.State ⊕ M₂.State)))
  tm :=
    { q₀ := .inl D.tm.q₀
      tr := fun q inp work => match q with
        | .inl q => captureAction Sum.inl (.inr (.inl false))
            ((f2_timedPadTM D (M₁.k + M₂.k)).tr q inp (fun i => work i.castSucc))
        | .inr (.inl false) =>
          ⟨0, (fun i => if (i : ℕ) < D.k + (M₁.k + M₂.k) then (none, 0)
            else (none, .neg)), none, some (.inr (.inl true))⟩
        | .inr (.inl true) => controlAction 0
            (some (.inr (.inr (.inl ((work (Fin.last _)).getD false, false)))))
        | .inr (.inr (.inl (b, false))) =>
            controlAction .neg (some (.inr (.inr (.inl (b, true)))))
        | .inr (.inr (.inl (b, true))) => match inp with
          | some _ => controlAction .neg (some (.inr (.inr (.inl (b, true)))))
          | none => controlAction .pos
              (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
        | .inr (.inr (.inr q)) => leftAction 1 id
            (rightAction D.k (fun s => .inr (.inr (.inr s)))
              ((branchTM M₁ M₂ false).tm.tr q inp
                (fun i => work (Fin.natAdd D.k i).castSucc))) }

/-- The branch configuration retains the decider's finished work and the
captured verdict; its own state, input head, work tapes, and output are exact. -/
private def f2_timedBranchCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  leftCfg id (rightCfg (fun s => .inr (.inr (.inr s))) c tapes heads)
    (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)

/-- The decider's configuration inside its padded, captured simulation.
Both branch tape banks are blank throughout this phase. -/
private def f2_timedControlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  captureCfg Sum.inl (.inr (.inl false)) [] []
    (leftCfg id c (fun (_ : Fin (M₁.k + M₂.k)) _ => none) (fun _ => 0))

/-- The capture contract, instantiated on the padded decider, gives the
entire controller phase through its first halt. -/
private lemma f2_timed_capture (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (hlive : ∀ s < t, ¬(D.tm.runFrom c s).Halted) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) t =
      f2_timedControlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  have hpad (u : ℕ) := leftCfg_run D.tm (f2_timedPadTM D (M₁.k + M₂.k)) id
    (fun _ _ _ => rfl) c (fun _ _ => none) (fun _ => 0) u
  have h := capture_run (f2_timedPadTM D (M₁.k + M₂.k)) (f2_timedCondTM D M₁ M₂).tm
    Sum.inl (.inr (.inl false)) (fun _ _ _ => rfl) [] []
    (leftCfg id c (fun _ _ => none) (fun _ => 0)) t (fun s hs => by
      unfold Cfg.Halted
      rw [hpad s]
      simpa only [leftCfg, Option.map_id] using hlive s hs)
  simpa only [hpad t] using h

/-- The host's genuine initial configuration is the captured, padded
initial configuration: all three work-tape blocks are blank. -/
private lemma f2_timed_control_init (D M₁ M₂ : FinTM Bool) (x : List Bool) :
    (f2_timedCondTM D M₁ M₂).tm.initCfg x =
      f2_timedControlCfg D M₁ M₂ (D.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [f2_timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [f2_timedControlCfg, captureCfg, leftCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [f2_timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [f2_timedControlCfg, captureCfg, leftCfg, hi]

/-- Once dispatched, the selected branch runs in lockstep while the old
decider tapes and singleton capture tape remain idle.
**Proof sketch.** The branch action is a right-block embedding followed by
a left-block embedding; compose their application lemmas, then iterate. -/
private lemma f2_timed_branch_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) (t : ℕ) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedBranchCfg D M₁ M₂ c tapes heads b) t =
      f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.runFrom c t) tapes heads b := by
  apply MultiTapeTM.runFrom_comm_of_step (fun c => f2_timedBranchCfg D M₁ M₂ c tapes heads b)
  intro d
  cases hs : d.state with
  | none =>
    simp only [MultiTapeTM.step, f2_timedBranchCfg, leftCfg, rightCfg, hs, Option.map_none]
  | some q =>
    have hstate : (f2_timedBranchCfg D M₁ M₂ d tapes heads b).state =
        some (.inr (.inr (.inr q))) := by
      simp only [f2_timedBranchCfg, leftCfg, rightCfg, hs, Option.map_some, id_eq]
    have hi : (f2_timedBranchCfg D M₁ M₂ d tapes heads b).inputSymbol = d.inputSymbol := rfl
    have hw : (fun i => (f2_timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
        (Fin.natAdd D.k i).castSucc) = d.workTapeSymbols := by
      funext i
      simp only [f2_timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols,
        Fin.castSucc, Fin.addCases_left, Fin.addCases_right]
    simp only [MultiTapeTM.step, hstate, hs]
    dsimp only [f2_timedCondTM]
    let emb : (M₁.State ⊕ M₂.State) → (f2_timedCondTM D M₁ M₂).State :=
      fun s => .inr (.inr (.inr s))
    change (leftAction 1 id (rightAction D.k emb
      ((branchTM M₁ M₂ b).tm.tr q d.inputSymbol
        (fun i => (f2_timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
          (Fin.natAdd D.k i).castSucc)))).apply
        (leftCfg id (rightCfg emb d tapes heads)
          (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)) = _
    erw [hw, leftCfg_apply, rightCfg_apply]
    rfl

/-- After reading the verdict, all branch data are initialized; only the
input head still needs rewinding. The capture head is back at cell zero. -/
private def f2_timedReadyCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  { f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) c.workTapes c.workTapePos b with
    state := some (.inr (.inr (.inl (b, false))))
    inputPos := c.inputPos }

/-- Two silent transitions move the capture head left and read the completed
singleton verdict, without touching the input or either work bank.
**Proof sketch.** The final capture head is one past the singleton, hence at
one. Moving it left exposes exactly its bit at zero; the next transition
records that bit in the rewind state. -/
private lemma f2_timed_read (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) (hs : c.state = none) (ho : c.output = [b]) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) 2 =
      f2_timedReadyCfg D M₁ M₂ c b := by
  let ready := f2_timedReadyCfg D M₁ M₂ c b
  have hback : (f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c) =
      {ready with state := some (.inr (.inl true))} := by
    have hstate : (f2_timedControlCfg D M₁ M₂ c).state = some (.inr (.inl false)) := by
      simp [f2_timedControlCfg, captureCfg, leftCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, ho]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, ho]
  have hread : (f2_timedCondTM D M₁ M₂).tm.step
      {ready with state := some (.inr (.inl true))} = ready := by
    have hsym : ({ready with state := some (.inr (.inl true))} :
        Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _) = some b := by
      change (f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x)
        c.workTapes c.workTapePos b).workTapeSymbols
          (Fin.natAdd (D.k + (M₁.k + M₂.k)) (0 : Fin 1)) = some b
      simp [f2_timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols, bufferTape]
    unfold MultiTapeTM.step
    dsimp only
    change ((controlAction 0 (some (.inr (.inr (.inl
      ((({ready with state := some (.inr (.inl true))} :
        Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _)).getD false, false)))))) :
          Action (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State).apply _ = _
    rw [hsym, controlAction_apply]
    simp only [Option.getD_some, moveInputPos_zero]
    rfl
  change (f2_timedCondTM D M₁ M₂).tm.step
    ((f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c)) = _
  rw [hback, hread]

/-- A singleton-output decider reaches the selected branch's genuine
initial configuration in at most twice its budget plus five steps.
**Proof sketch.** Choose the first source halt, which is within the supplied
budget. Capture until that halt, read the singleton in two steps, and rewind
in at most the current input position plus two. The head-position bound
charges this rewind to the decider's elapsed steps, not the input length. -/
private lemma f2_timed_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∃ a ≤ 2 * T + 5, ∃ (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) a =
        f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads b := by
  classical
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hD).1⟩
  let t := Nat.find hh
  let c := D.tm.runFrom (D.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hD).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = [b] := hc.output_unique hD
  have hcap : (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) t =
      f2_timedControlCfg D M₁ M₂ c := by
    rw [f2_timed_control_init]
    exact f2_timed_capture D M₁ M₂ _ t (fun s hst => Nat.find_min hh hst)
  obtain ⟨r, hrle, hr⟩ := timed_rewind (f2_timedCondTM D M₁ M₂).tm
    (.inr (.inr (.inl (b, false)))) (.inr (.inr (.inl (b, true))))
    (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_timedReadyCfg D M₁ M₂ c b) rfl
  refine ⟨t + 2 + r, ?_, c.workTapes, c.workTapePos, ?_⟩
  · have hp : c.inputPos.val ≤ 1 + t := by
      simpa only [MultiTapeTM.initCfg, Cfg.init, Fin.val_one] using
        MultiTapeTM.timed_input_bound (tm := D.tm) (D.tm.initCfg x) t
    change r ≤ c.inputPos.val + 2 at hrle
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap,
      f2_timed_read D M₁ M₂ c b hs ho, hr]
    rfl

private lemma f2_cond_time {D M₁ M₂ : FinTM Bool} {p : List Bool → Bool}
    {f₁ f₂ : List Bool → List Bool} {T₀ T₁ T₂ : ℕ → ℕ}
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂) :
    (f2_timedCondTM D M₁ M₂).ComputesFunInTime
      (fun x => if p x then f₁ x else f₂ x)
      (fun n => 5 * (T₀ n + max (T₁ n) (T₂ n) + 1)) := by
  intro x
  let B := max (T₁ x.length) (T₂ x.length)
  have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x
      (if p x then f₁ x else f₂ x) B := by
    apply (branchTM_computes M₁ M₂ (p x) x _ B).mpr
    cases hp : p x with
    | false => exact (h₂ x).mono (Nat.le_max_right _ _)
    | true => exact (h₁ x).mono (Nat.le_max_left _ _)
  obtain ⟨a, ha, tapes, heads, hstart⟩ :=
    f2_timed_start D M₁ M₂ x (p x) (T₀ x.length) (hD x)
  have hc : (f2_timedCondTM D M₁ M₂).ComputesInTime x
      (if p x then f₁ x else f₂ x) (a + B) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, f2_timed_branch_run]
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ _ _ _).mp hb
    exact ⟨by simpa only [f2_timedBranchCfg, leftCfg, rightCfg, Option.map_eq_none_iff] using hs, ho⟩
  -- The controller prefix and selected branch fit one uniform coefficient.
  apply hc.mono
  dsimp only [B] at *
  omega

/-- A native input rewind keeps every work head fixed at every prefix,
including its dispatch step. -/
private lemma f2_rewind_scan_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      ∀ u ≤ j + 1, (tm.runFrom cfg u).workTapePos = cfg.workTapePos := by
  intro j
  induction j with
  | zero =>
    intro cfg hs hj hp u hu
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
    · rfl
    · have hz : cfg.inputPos = 0 := Fin.ext hj
      have hi : cfg.inputSymbol = none := by simp [Cfg.inputSymbol, hz]
      change (tm.step cfg).workTapePos = _
      simp only [MultiTapeTM.step, hs, htr, hi, controlAction_apply]
  | succ j ih =>
    intro cfg hs hj hp u hu
    cases u with
    | zero => rfl
    | succ u =>
      have hi : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have he : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        simp only [MultiTapeTM.step, hs, htr, hi, controlAction_apply]
      rw [MultiTapeTM.runFrom_succ_eq_step, he]
      apply ih _ rfl _ (by omega) u (by omega)
      simp only [moveInputPos_neg_val]
      omega

/-- The bounded rewind with the prefix work-head equality retained. -/
private lemma f2_rewind_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} ∧
      ∀ u ≤ r, (tm.runFrom c u).workTapePos = c.workTapePos := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    simp only [MultiTapeTM.step, hs, hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]
  · intro u hu
    cases u with
    | zero => rfl
    | succ u =>
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact f2_rewind_scan_heads tm scan dest hscan (moveInputPos c.inputPos .neg).val _ rfl rfl hp u (by omega)

/-- Explicit equivalence between a disjoint pair of banks and their concatenation. -/
private def f2_finSumEquiv (a b : ℕ) : Fin a ⊕ Fin b ≃ Fin (a + b) where
  toFun := Sum.elim (Fin.castAdd b) (Fin.natAdd a)
  invFun := fun i => if h : (i : ℕ) < a then Sum.inl ⟨i, h⟩
    else Sum.inr ⟨i - a, by have := i.isLt; omega⟩
  left_inv := by
    intro i
    cases i with
    | inl i => simp [i.isLt]
    | inr i =>
      simp only [Sum.elim_inr, Fin.coe_natAdd, not_lt.mpr (Nat.le_add_right _ _), ↓reduceDIte]
      congr 1
      apply Fin.ext
      simp
  right_inv := by
    intro i
    dsimp only
    split
    · rfl
    · apply Fin.ext
      dsimp only [Sum.elim_inr, Fin.coe_natAdd]
      omega

/-- Sum a finite tape bank by its two disjoint blocks. -/
private lemma f2_sum_add {a b : ℕ} (f : Fin (a + b) → ℕ) :
    (∑ i : Fin (a + b), f i) =
      (∑ i : Fin a, f (Fin.castAdd b i)) + ∑ i : Fin b, f (Fin.natAdd a i) := by
  rw [Fintype.sum_equiv (f2_finSumEquiv a b).symm f (fun i => f ((f2_finSumEquiv a b).toFun i))]
  · exact Finset.sum_disjSum Finset.univ Finset.univ _
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

/-- Disjoint branch banks give exact selected-space plus idle origins. -/
private lemma f2_branch_space (M₁ M₂ : FinTM Bool) (b : Bool) (x : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).tm.spaceUsed ((branchTM M₁ M₂ b).tm.initCfg x) t =
      if b then M₁.tm.spaceUsed (M₁.tm.initCfg x) t + M₂.k
      else M₂.tm.spaceUsed (M₂.tm.initCfg x) t + M₁.k := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    have hr (u : ℕ) := rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr
      (fun _ _ _ => rfl) (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) u
    simp only [Bool.false_eq_true, ↓reduceIte, MultiTapeTM.spaceUsed]
    change (∑ i : Fin (M₁.k + M₂.k),
      (branchTM M₁ M₂ false).tm.spaceUsedByTape ((branchTM M₁ M₂ false).tm.initCfg x) t i) = _
    rw [f2_sum_add (a := M₁.k) (b := M₂.k)]
    simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead]
    simp only [hi]
    simp only [hr]
    simp only [rightCfg, Fin.addCases_left, Fin.addCases_right]
    simp [Finset.image_const Finset.nonempty_range_add_one, Nat.add_comm]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    have hr (u : ℕ) := leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl
      (fun _ _ _ => rfl) (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) u
    simp only [↓reduceIte, MultiTapeTM.spaceUsed]
    change (∑ i : Fin (M₁.k + M₂.k),
      (branchTM M₁ M₂ true).tm.spaceUsedByTape ((branchTM M₁ M₂ true).tm.initCfg x) t i) = _
    rw [f2_sum_add (a := M₁.k) (b := M₂.k)]
    simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead]
    simp only [hi]
    simp only [hr]
    simp only [leftCfg, Fin.addCases_left, Fin.addCases_right]
    simp [Finset.image_const Finset.nonempty_range_add_one]

/-- Head layout of the timed controller, with one scalar capture position. -/
private def f2_condHeads (D M₁ M₂ : FinTM Bool) (d : Fin D.k → ℤ)
    (b : Fin (M₁.k + M₂.k) → ℤ) (z : ℤ) :
    Fin ((D.k + (M₁.k + M₂.k)) + 1) → ℤ :=
  Fin.addCases (Fin.addCases d b) (fun _ => z)

/-- The captured decider has its source positions, idle branches, and a
capture head at its output length. -/
private lemma f2_control_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) :
    (f2_timedControlCfg D M₁ M₂ c).workTapePos =
      f2_condHeads D M₁ M₂ c.workTapePos (fun _ => 0) c.output.length := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [f2_timedControlCfg, captureCfg, leftCfg, f2_condHeads, j.isLt]
  · simp [f2_timedControlCfg, captureCfg, leftCfg, f2_condHeads]

/-- A dispatched branch keeps the completed decider's heads and the
capture head fixed while simulating precisely its selected bank. -/
private lemma f2_branch_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) :
    (f2_timedBranchCfg D M₁ M₂ c tapes heads b).workTapePos =
      f2_condHeads D M₁ M₂ heads c.workTapePos 0 := rfl

/-- The mandatory back/read pair preserves both machine banks and moves
only the singleton capture head from one to zero. -/
private lemma f2_read_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) (hs : c.state = none) (ho : c.output = [b]) :
    ∀ u ≤ 2, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) u).workTapePos =
        f2_condHeads D M₁ M₂ c.workTapePos (fun _ => 0) z := by
  intro u hu
  have hu : u = 0 ∨ u = 1 ∨ u = 2 := by omega
  rcases hu with rfl | rfl | rfl
  · refine ⟨1, by omega, by omega, ?_⟩
    simpa [ho] using f2_control_heads D M₁ M₂ c
  · refine ⟨0, by omega, by omega, ?_⟩
    have hstate : (f2_timedControlCfg D M₁ M₂ c).state = some (.inr (.inl false)) := by
      simp [f2_timedControlCfg, captureCfg, leftCfg, hs]
    change ((f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c)).workTapePos = _
    simp only [MultiTapeTM.step, hstate]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [f2_timedCondTM, Action.apply, f2_control_heads, f2_condHeads, j.isLt]
    · simp [f2_timedCondTM, Action.apply, f2_control_heads, f2_condHeads, ho]
  · refine ⟨0, by omega, by omega, ?_⟩
    rw [f2_timed_read D M₁ M₂ c b hs ho]
    rfl

/-- The whole timed conditional has two unchanged source trajectories:
a decider prefix, then a branch prefix. The administrative stages repeat
endpoints; only the capture head has positions zero or one. -/
private lemma f2_cond_ledger (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∀ u, ∃ v ≤ T, ∃ w ≤ u, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) u).workTapePos =
        f2_condHeads D M₁ M₂ (D.tm.runFrom (D.tm.initCfg x) v).workTapePos
          ((branchTM M₁ M₂ b).tm.runFrom ((branchTM M₁ M₂ b).tm.initCfg x) w).workTapePos z := by
  classical
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hD).1⟩
  let d := Nat.find hh
  let c := D.tm.runFrom (D.tm.initCfg x) d
  have hd : d ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hD).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x c.output d := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = [b] := hc.output_unique hD
  have hcap (u : ℕ) (hu : u ≤ d) :
      (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) u =
        f2_timedControlCfg D M₁ M₂ (D.tm.runFrom (D.tm.initCfg x) u) := by
    rw [f2_timed_control_init]
    exact f2_timed_capture D M₁ M₂ _ u (fun s hsu => Nat.find_min hh (by omega))
  obtain ⟨r, hrle, hr, hrheads⟩ := f2_rewind_heads (f2_timedCondTM D M₁ M₂).tm
    (.inr (.inr (.inl (b, false)))) (.inr (.inr (.inl (b, true))))
    (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_timedReadyCfg D M₁ M₂ c b) rfl
  have hstart : (f2_timedCondTM D M₁ M₂).tm.runFrom
      ((f2_timedCondTM D M₁ M₂).tm.initCfg x) (d + 2 + r) =
      f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x)
        c.workTapes c.workTapePos b := by
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap d (le_refl _),
      f2_timed_read D M₁ M₂ c b hs ho, hr]
    rfl
  intro u
  by_cases hu : u ≤ d
  · refine ⟨u, hu.trans hd, 0, Nat.zero_le _,
      (D.tm.runFrom (D.tm.initCfg x) u).output.length, by omega, ?_, ?_⟩
    · have hp := (D.tm.output_prefix (D.tm.initCfg x) hu).length_le
      change (D.tm.runFrom (D.tm.initCfg x) u).output.length ≤ c.output.length at hp
      rw [ho] at hp
      simp only [List.length_singleton] at hp
      exact_mod_cast hp
    · rw [hcap u hu, f2_control_heads]
      rfl
  · refine ⟨d, hd, ?_⟩
    by_cases hread : u ≤ d + 2
    · obtain ⟨z, hz0, hz1, he⟩ := f2_read_heads D M₁ M₂ c b hs ho (u - d) (by omega)
      refine ⟨0, Nat.zero_le _, z, hz0, hz1, ?_⟩
      rw [show u = d + (u - d) by omega, MultiTapeTM.runFrom_add, hcap d (le_refl _)]
      exact he
    · by_cases hrew : u ≤ d + 2 + r
      · refine ⟨0, Nat.zero_le _, 0, by omega, by omega, ?_⟩
        rw [show u = d + 2 + (u - (d + 2)) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_add, hcap d (le_refl _), f2_timed_read D M₁ M₂ c b hs ho,
          hrheads _ (by omega)]
        rfl
      · refine ⟨u - (d + 2 + r), by omega, 0, by omega, by omega, ?_⟩
        rw [show u = d + 2 + r + (u - (d + 2 + r)) by omega,
          MultiTapeTM.runFrom_add, hstart, f2_timed_branch_run, f2_branch_heads]
        simp only [Nat.add_sub_cancel_left]
        rfl

/-- Cardinalities of the disjoint source banks, with the singleton verdict
occupying at most its two head positions. -/
private lemma f2_cond_space (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T t : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    (f2_timedCondTM D M₁ M₂).tm.spaceUsed ((f2_timedCondTM D M₁ M₂).tm.initCfg x) t ≤
      D.tm.spaceUsed (D.tm.initCfg x) T +
        (branchTM M₁ M₂ b).tm.spaceUsed ((branchTM M₁ M₂ b).tm.initCfg x) t + 2 := by
  let M := f2_timedCondTM D M₁ M₂
  let B := branchTM M₁ M₂ b
  have hDcard (i : Fin D.k) :
      M.tm.spaceUsedByTape (M.tm.initCfg x) t ((Fin.castAdd (M₁.k + M₂.k) i).castSucc) ≤
        D.tm.spaceUsedByTape (D.tm.initCfg x) T i := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_range.mpr (by omega), ?_⟩
    change _ = ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _
    rw [he]
    simp [f2_condHeads, Fin.castSucc]
  have hBcard (i : Fin (M₁.k + M₂.k)) :
      M.tm.spaceUsedByTape (M.tm.initCfg x) t ((Fin.natAdd D.k i).castSucc) ≤
        B.tm.spaceUsedByTape (B.tm.initCfg x) t i := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_range.mpr (by have := Finset.mem_range.mp hu; omega), ?_⟩
    change _ = ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _
    rw [he]
    simp [f2_condHeads, Fin.castSucc, B]
  have hcap : M.tm.spaceUsedByTape (M.tm.initCfg x) t (Fin.last _) ≤ 2 := by
    have hsub : M.tm.visitedByTapeHead (M.tm.initCfg x) t (Fin.last _) ⊆ Finset.Icc (0 : ℤ) 1 := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
      change ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _ ∈ _
      rw [he]
      simpa [f2_condHeads, Fin.last, Fin.addCases] using Finset.mem_Icc.mpr ⟨hz0, hz1⟩
    exact (Finset.card_le_card hsub).trans (by decide)
  change (∑ i : Fin ((D.k + (M₁.k + M₂.k)) + 1), M.tm.spaceUsedByTape (M.tm.initCfg x) t i) ≤ _
  rw [f2_sum_add, f2_sum_add]
  simp only [Fintype.sum_unique]
  exact Nat.add_le_add (Nat.add_le_add
    (Finset.sum_le_sum (fun i _ => hDcard i))
    (Finset.sum_le_sum (fun i _ => hBcard i))) hcap

/-- **W3 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.computesFunInTime_cond`). Given space bounds for
the decider and both branches, the conditional controller's space is the
decider's plus the selected branch's **max** — the unselected branch's
bank is idle (origin singletons) — plus a machine constant for the
capture tape and the idle banks' origin cells.

**Proof sketch.** The controller's tape banks are disjoint: the decider
bank is only touched in the capture phase (bounded by `sD` through the
W1 lockstep), the selected branch bank only after dispatch (bounded by
its own hypothesis on the same input `x` — no monotonicity needed), the
unselected bank and the capture tape contribute one cell per tape plus
the singleton verdict; sum the three groups. -/
theorem computesFunInTime_cond_spaceUsed {D M₁ M₂ : FinTM Bool}
    {p : List Bool → Bool} {f₁ f₂ : List Bool → List Bool}
    {T₀ T₁ T₂ : ℕ → ℕ} (sD s₁ s₂ : ℕ → ℕ)
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂)
    (hsD : ∀ (x : List Bool) (t : ℕ),
      D.tm.spaceUsed (D.tm.initCfg x) t ≤ sD x.length)
    (hs₁ : ∀ (x : List Bool) (t : ℕ),
      M₁.tm.spaceUsed (M₁.tm.initCfg x) t ≤ s₁ x.length)
    (hs₂ : ∀ (x : List Bool) (t : ℕ),
      M₂.tm.spaceUsed (M₂.tm.initCfg x) t ≤ s₂ x.length) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x)
        (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ sD x.length + max (s₁ x.length) (s₂ x.length) + c := by
  refine ⟨f2_timedCondTM D M₁ M₂, 7 + M₁.k + M₂.k, ?_, ?_⟩
  · intro x
    exact (f2_cond_time hD h₁ h₂ x).mono (Nat.mul_le_mul_right _ (by omega))
  · intro x t
    have h := f2_cond_space D M₁ M₂ x (p x) (T₀ x.length) t (hD x)
    rw [f2_branch_space] at h
    have hd := hsD x (T₀ x.length)
    have h1 := hs₁ x t
    have h2 := hs₂ x t
    have hm1 := Nat.le_max_left (s₁ x.length) (s₂ x.length)
    have hm2 := Nat.le_max_right (s₁ x.length) (s₂ x.length)
    split at h <;> omega

/-- **L space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.exists_loopTM`; the `exists_loopCfgTM` and
`exists_loopFindTM` siblings inherit the same host at fill time). Same
hypotheses as the decision loop, plus space bounds for the fuel machine
and for the body — from its initial configuration and from every
admissible seam, within the round budget. Conclusion: the loop host also
runs within a constant multiple of `S n + T n + 1` work-tape cells. The
key point is that space does **not** scale with the round count `R`:
rounds restart from seams with heads at the origin, so their footprints
overlap instead of accumulating.

**Proof sketch.** Per tape, each round's visited set is an interval
containing the seam origin (heads move by unit steps from the origin) of
cardinality at most `S n`, so the union over all rounds lies in
`[-(S n), S n]` — at most `2·S n + 1` cells, not `R·S n`. The counter
tape holds the fuel word, of length at most `T n`
(`Turing.MultiTapeTM.output_length_le` on the fuel machine), walked in
place by the debits; the capture tape records one verdict per round and
is rewound with the round, staying within a constant; the fuel machine's
own banks are bounded by `hFspace`. Sum the groups and absorb tape
counts into `c`.  **Scope note (round-1 note R10)**: this row annotates the
decision-loop export (`Turing.exists_loopTM`) only; the configuration- and
result-bearing siblings (`exists_loopCfgTM`, `exists_loopFindTM`) carry no
exported space clause here — same-witness conjunctions for them are a
recorded future addition, commissioned when a consumer needs them, not an
implied theorem. -/
theorem exists_loopTM_spaceUsed (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (s0 : List Bool → List Bool) (R T S : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s)))
    (hFspace : ∀ (x : List Bool) (t : ℕ),
      F.tm.spaceUsed (F.tm.initCfg x) t ≤ S x.length)
    (hstartSpace : ∀ (x : List Bool) (t : ℕ), t ≤ T x.length →
      body.tm.spaceUsed (body.tm.initCfg x) t ≤ S x.length)
    (hroundSpace : ∀ (x s : List Bool), Inv x s →
      ∀ t ≤ T x.length,
        body.tm.spaceUsed
          (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t
            ≤ S x.length) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF x ((stepF x)^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) ∧
      ∀ (x : List Bool) (t : ℕ),
        E.tm.spaceUsed (E.tm.initCfg x) t
          ≤ c * (S x.length + T x.length + 1) := by
  sorry

end Turing.FinTM
