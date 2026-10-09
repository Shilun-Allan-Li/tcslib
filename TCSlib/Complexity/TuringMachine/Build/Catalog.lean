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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
