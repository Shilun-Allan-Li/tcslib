/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger
import TCSlib.Complexity.ClassP.TimeConstructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines

A machine is *oblivious* if its head movements depend only on the input length, not on
the input itself [AB09, Remark 1.7 and Exercise 1.5]. Obliviousness will matter for
the Cook-Levin theorem (Chapter 2), where the tableau of an oblivious computation has
input-independent structure.

The construction is developed in the layer modules `ObliviousSchedule.lean`
(which now hosts `Turing.FinTM.Oblivious`), `ObliviousCandidate.lean`,
`ObliviousSetup.lean`, and `ObliviousLedger.lean` in this directory, split out
mechanically at the epoch-3→4 merge; this file proves the data machine's
correctness invariant and the final theorem.

## Design

* We state the quadratic version — Exercise 1.5's *first assertion*, adapted to this
  model; the exercise's final two-tape normal form is **not** included here. The
  `O(T log T)` sharpening (Exercise 1.6) is a stretch goal alongside §1.7, off the
  critical path.

## Main results

* `Complexity.oblivious_of_mem_DTIME` — [AB09, Exercise 1.5]: every language decidable
  in time-constructible time `T` is decided by an oblivious machine in `O((T + 1)²)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, p. 17; Exercise 1.5, p. 34.)
-/

namespace Complexity

open Turing

/-- Logical simulator before the fixed-duration binary representation. -/
private noncomputable def dataTM (W M : FinTM Bool) (a : ℕ) : FinTM OblSymbol := by
  classical
  exact decorateTM (obliviousSchedule W a) (M.k + 1) (Fin.natAdd W.k (2 : Fin 3))
    (obliviousDataInit M) (obliviousVisit W M a)

/-- Macrostep configurations with explicit finite data registers and tapes. -/
private def dataCfg (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : OblPhase W.State a) (u g : ℤ) (d : OblData M)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) :=
  decoratedCfg (Fin.natAdd W.k (2 : Fin 3)) (macroCfg W a base (some q) u g) d tapes out

/-- One data step over a macrostep configuration, retaining the exact schedule
configuration produced by the independently verified controller. -/
private lemma dataCfg_step (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : OblPhase W.State a) (u g : ℤ) (d : OblData M)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) :
    let c := macroCfg W a base (some q) u g
    let v := obliviousVisit W M a q d c.inputSymbol c.workTapeSymbols (fun i => tapes i g)
    (dataTM W M a).tm.step (dataCfg W M a base q u g d tapes out) =
      decoratedCfg (Fin.natAdd W.k (2 : Fin 3)) ((obliviousSchedule W a).tm.step c) v.1
        (fun i => setupWrite (tapes i) g (v.2.1 i)) (out ++ v.2.2.toList) := by
  classical
  simpa only [macroCfg, Fin.addCases_right, Fin.reduceFinMk, ↓reduceIte] using
    decoratedCfg_step (obliviousSchedule W a) (M.k + 1) (Fin.natAdd W.k (2 : Fin 3))
      (obliviousDataInit M) (obliviousVisit W M a)
      (macroCfg W a base (some q) u g) q rfl d tapes out

/-- An interior forward visit preserves every current payload and caches the
incoming left-neighbor register. Its movement is the schedule's right move. -/
private lemma dataCfg_forward_step (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u g : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hn : g ≠ (R : ℤ) + 1) :
    (dataTM W M a).tm.step (dataCfg W M a base .forward u g (q,b,read,carry) tapes out) =
      dataCfg W M a base .forward u (g + 1)
        (q,b,read,fun i => (dataCell (tapes i g)).1)
        (fun i => Function.update (tapes i) g (some (.cell (dataCell (tapes i g)).1 (carry i)))) out := by
  rw [dataCfg_step, macroCfg_forward W a base u g R hg, if_neg hn]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_right, hn, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]

/-- The forward turn clears the neighbor register without altering data tapes. -/
private lemma dataCfg_forward_turn (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (dataTM W M a).tm.step
      (dataCfg W M a base .forward u ((R : ℤ) + 1) (q,b,read,carry) tapes out) =
      dataCfg W M a base .backward u R (q,b,read,fun _ => blankPayload) tapes out := by
  rw [dataCfg_step, macroCfg_forward W a base u _ R hg, if_pos rfl]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_right, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]
  rw [show (R : ℤ) + 1 - 1 = R by omega]

/-- An interior backward visit chooses the requested neighbor and carries the
old current payload to the next cell on the left. -/
private lemma dataCfg_backward_step (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u g : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hn : g ≠ -(R : ℤ) - 1) :
    (dataTM W M a).tm.step (dataCfg W M a base .backward u g (q,b,read,carry) tapes out) =
      dataCfg W M a base .backward u (g - 1)
        (q,b,read,fun i => (dataCell (tapes i g)).1)
        (fun i => Function.update (tapes i) g (some (.cell
          (match obliviousSourceMove M q read i with
            | .neg => (dataCell (tapes i g)).2
            | .zero => (dataCell (tapes i g)).1
            | .pos => carry i) blankPayload))) out := by
  rw [dataCfg_step, macroCfg_backward W a base u g R hg, if_neg hn]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_left, hn, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]
  rfl

/-- The left boundary turn preserves the completed data sweep. -/
private lemma dataCfg_backward_turn (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (d : OblData M)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (dataTM W M a).tm.step
      (dataCfg W M a base .backward u (-(R : ℤ) - 1) d tapes out) =
      dataCfg W M a base .returnCenter u (-(R : ℤ)) d tapes out := by
  rw [dataCfg_step, macroCfg_backward W a base u _ R hg, if_pos rfl]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_left, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]
  rw [show -(R : ℤ) - 1 + 1 = -(R : ℤ) by omega]

/-- Every prefix of the actual forward scan preserves all current payloads
and installs the correct left-neighbor cache at every visited coordinate.
**Proof sketch.** Induct on the physical scan length. The next current payload
is unchanged, and updating one cell extends the cached interval by one. -/
private lemma dataCfg_forward_prefix (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read : Fin (M.k + 1) → OblPayload) (f : ℤ → Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = f z i) (n : ℕ) (hn : n ≤ 2 * R + 1) :
    ∃ tapes',
      (dataTM W M a).tm.runFrom
        (dataCfg W M a base .forward u (-(R : ℤ)) (q,b,read,f (-(R : ℤ) - 1)) tapes out) n =
        dataCfg W M a base .forward u (-(R : ℤ) + n)
          (q,b,read,f (-(R : ℤ) + n - 1)) tapes' out ∧
      (∀ i z, (dataCell (tapes' i z)).1 = f z i) ∧
      (∀ i z, -(R : ℤ) ≤ z → z < -(R : ℤ) + n → (dataCell (tapes' i z)).2 = f (z - 1) i) := by
  induction n with
  | zero =>
    refine ⟨tapes, ?_, hf, ?_⟩
    · simp only [Nat.cast_zero, add_zero, MultiTapeTM.runFrom_zero]
    · intro i z hl hr
      omega
  | succ n ih =>
    obtain ⟨ts, hrun, hfirst, hleft⟩ := ih (by omega)
    let g : ℤ := -(R : ℤ) + n
    let ts' := fun i => Function.update (ts i) g (some (.cell (f g i) (f (g - 1) i)))
    have hc : (fun i => (dataCell (ts i g)).1) = f g := funext (fun i => hfirst i g)
    refine ⟨ts', ?_, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', hrun,
        dataCfg_forward_step W M a base u _ R q b read _ ts out hg (by omega)]
      change dataCfg W M a base .forward u (g + 1)
        (q,b,read,fun i => (dataCell (ts i g)).1)
        (fun i => Function.update (ts i) g (some (.cell (dataCell (ts i g)).1 (f (g - 1) i)))) out = _
      simp only [hfirst, hc]
      have hp : -(R : ℤ) + (n + 1 : ℕ) = g + 1 := by omega
      rw [hp, show g + 1 - 1 = g by omega]
    · intro i z
      by_cases hz : z = g
      · subst z
        simp only [ts', Function.update_self, dataCell]
      · simp only [ts', Function.update_of_ne hz, hfirst]
    · intro i z hl hr
      by_cases hz : z = g
      · subst z
        simp only [ts', Function.update_self, dataCell]
      · simp only [ts', Function.update_of_ne hz]
        exact hleft i z hl (by dsimp only [g] at hz; omega)

/-- Every prefix of the actual backward scan shifts exactly the visited cells.
Unvisited current payloads and their cached left neighbors remain available.
**Proof sketch.** The carry is the old right neighbor. At the next cell the
three direction cases select the cached left, current, or carried right payload;
then the old current becomes the carry for the following cell. -/
private lemma dataCfg_backward_prefix (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read : Fin (M.k + 1) → OblPayload) (f : ℤ → Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = f z i)
    (hl : ∀ i z, -(R : ℤ) ≤ z → z ≤ R → (dataCell (tapes i z)).2 = f (z - 1) i)
    (n : ℕ) (hn : n ≤ 2 * R + 1) :
    ∃ tapes',
      (dataTM W M a).tm.runFrom
        (dataCfg W M a base .backward u R (q,b,read,f ((R : ℤ) + 1)) tapes out) n =
        dataCfg W M a base .backward u ((R : ℤ) - n)
          (q,b,read,f ((R : ℤ) - n + 1)) tapes' out ∧
      (∀ i z, (dataCell (tapes' i z)).1 =
        if (R : ℤ) - n < z ∧ z ≤ R then f (z + (obliviousSourceMove M q read i : ℤ)) i else f z i) ∧
      (∀ i z, -(R : ℤ) ≤ z → z ≤ (R : ℤ) - n → (dataCell (tapes' i z)).2 = f (z - 1) i) := by
  induction n with
  | zero =>
    refine ⟨tapes, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero, sub_zero, MultiTapeTM.runFrom_zero]
    · intro i z
      simp only [Nat.cast_zero, sub_zero, show ¬((R : ℤ) < z ∧ z ≤ R) by omega, if_false, hf]
    · simpa only [Nat.cast_zero, sub_zero] using hl
  | succ n ih =>
    obtain ⟨ts, hrun, hfirst, hleft⟩ := ih (by omega)
    let g : ℤ := (R : ℤ) - n
    let ts' := fun i => Function.update (ts i) g
      (some (.cell (f (g + (obliviousSourceMove M q read i : ℤ)) i) blankPayload))
    have hc (i) : (dataCell (ts i g)).1 = f g i := by
      rw [hfirst, if_neg (by omega)]
    have hc' : (fun i => (dataCell (ts i g)).1) = f g := funext hc
    have hnbr (i) : (match obliviousSourceMove M q read i with
        | .neg => (dataCell (ts i g)).2
        | .zero => (dataCell (ts i g)).1
        | .pos => f (g + 1) i) = f (g + (obliviousSourceMove M q read i : ℤ)) i := by
      have hleft' := hleft i g (by omega) (le_refl _)
      cases hd : obliviousSourceMove M q read i <;>
        simp only [hd, SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]
    refine ⟨ts', ?_, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', hrun,
        dataCfg_backward_step W M a base u _ R q b read _ ts out hg (by omega)]
      change dataCfg W M a base .backward u (g - 1)
        (q,b,read,fun i => (dataCell (ts i g)).1)
        (fun i => Function.update (ts i) g (some (.cell
          (match obliviousSourceMove M q read i with
            | .neg => (dataCell (ts i g)).2
            | .zero => (dataCell (ts i g)).1
            | .pos => f (g + 1) i) blankPayload))) out = _
      simp only [hc', hnbr]
      have hp : (R : ℤ) - (n + 1 : ℕ) = g - 1 := by omega
      rw [hp, show g - 1 + 1 = g by omega]
    · intro i z
      by_cases hz : z = g
      · subst z
        simp only [ts', Function.update_self, dataCell]
        rw [if_pos (show (R : ℤ) - (n + 1 : ℕ) < g ∧ g ≤ R by dsimp only [g]; omega)]
      · simp only [ts', Function.update_of_ne hz, hfirst]
        have he : ((R : ℤ) - n < z ∧ z ≤ R) ↔ ((R : ℤ) - (n + 1 : ℕ) < z ∧ z ≤ R) := by
          dsimp only [g] at hz
          omega
        simp only [he]
    · intro i z hlow hhigh
      have hz : z ≠ g := by omega
      simp only [ts', Function.update_of_ne hz]
      exact hleft i z hlow (by omega)

/-- The outward positioning scan leaves all data and saved source reads intact.
**Proof sketch.** Induct through the read-only positioning prefix, then take the
left-boundary turn, which resets the already blank neighbor register. -/
private lemma dataCfg_seek_run (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool) (read : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (dataTM W M a).tm.runFrom
      (dataCfg W M a base .seekLeft u 0 (q,b,read,fun _ => blankPayload) tapes out) (R + 2) =
      dataCfg W M a base .forward u (-(R : ℤ)) (q,b,read,fun _ => blankPayload) tapes out := by
  have hp : ∀ n, n ≤ R + 1 → (dataTM W M a).tm.runFrom
      (dataCfg W M a base .seekLeft u 0 (q,b,read,fun _ => blankPayload) tapes out) n =
      dataCfg W M a base .seekLeft u (-(n : ℤ)) (q,b,read,fun _ => blankPayload) tapes out := by
    intro n hn
    induction n with
    | zero => simp only [Nat.cast_zero, neg_zero, MultiTapeTM.runFrom_zero]
    | succ n ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), dataCfg_step,
        macroCfg_seek W a base u _ R hg, if_neg (by omega)]
      simp only [obliviousVisit, macroCfg_guide, hg, guideTape_left,
        show -(n : ℤ) ≠ -(R : ℤ) - 1 by omega, ↓reduceIte,
        setupWrite, Option.toList_none, List.append_nil, dataCfg]
      rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', hp _ (le_refl _), dataCfg_step,
    macroCfg_seek W a base u _ R hg, if_pos (by omega)]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_left,
    show -((R + 1 : ℕ) : ℤ) = -(R : ℤ) - 1 by omega, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]
  rw [show -(R : ℤ) - 1 + 1 = -(R : ℤ) by omega]

/-- Returning from the left boundary preserves the shifted tapes and commits
exactly the saved source transition at the marked origin.
**Proof sketch.** Every step before the origin preserves the registers and tapes;
at the origin the saved reads select the successor state and the counter advances. -/
private lemma dataCfg_center_run (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (dataTM W M a).tm.runFrom
      (dataCfg W M a base .returnCenter u (-(R : ℤ)) (q,b,read,carry) tapes out) (R + 1) =
      dataCfg W M a base .macroCheck (u + 1) 0
        ((obliviousSourceAction M q read).state,b,read,carry) tapes out := by
  have hp : ∀ n, n ≤ R → (dataTM W M a).tm.runFrom
      (dataCfg W M a base .returnCenter u (-(R : ℤ)) (q,b,read,carry) tapes out) n =
      dataCfg W M a base .returnCenter u (-(R : ℤ) + n) (q,b,read,carry) tapes out := by
    intro n hn
    induction n with
    | zero => simp only [Nat.cast_zero, add_zero, MultiTapeTM.runFrom_zero]
    | succ n ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), dataCfg_step,
        macroCfg_center W a base u _ R hg, if_neg (by omega)]
      simp only [obliviousVisit, macroCfg_guide, hg, guideTape_origin,
        show -(R : ℤ) + n ≠ 0 by omega, ↓reduceIte,
        setupWrite, Option.toList_none, List.append_nil, dataCfg]
      rw [show -(R : ℤ) + n + 1 = -(R : ℤ) + (n + 1 : ℕ) by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', hp _ (le_refl _),
    show -(R : ℤ) + R = 0 by omega, dataCfg_step,
    macroCfg_center W a base u _ R hg, if_pos rfl]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_origin, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]

/-- The initial counter test saves the source reads, performs its origin writes,
updates its answer register, and starts a full sweep without emitting output. -/
private lemma dataCfg_check (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (out : List OblSymbol)
    (hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u = some .unit) :
    let read := fun i => (dataCell (tapes i 0)).1
    let act := obliviousSourceAction M d.1 read
    (dataTM W M a).tm.step (dataCfg W M a base .macroCheck u 0 d tapes out) =
      dataCfg W M a base .seekLeft u 0 (d.1,act.output.getD d.2.1,read,fun _ => blankPayload)
        (fun i => setupWrite (tapes i) 0
          (Fin.addCases (fun j => (act.workTapes j).1.map (fun p => some (.cell (p,0) blankPayload)))
            (fun _ : Fin 1 => none) i)) out := by
  dsimp only
  rw [dataCfg_step, macroCfg_check, if_pos hu]
  simp only [obliviousVisit, macroCfg_unary, hu, ↓reduceIte,
    Option.toList_none, List.append_nil, dataCfg]

/-- Decoding the origin writes gives exactly the source's written payloads,
including an explicit blank write and the identity action of a halted source.
**Proof sketch.** Separate work lanes from the read-only input lane. On a work
lane only coordinate zero can change; the optional-write cases give exactly the
source write or the old payload. Every other coordinate is unchanged. -/
private lemma dataCfg_written (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = sourcePayload c z i) :
    ∀ i z, (dataCell (setupWrite (tapes i) 0
      (Fin.addCases (fun j => ((sourceTotalAction M c).workTapes j).1.map
        (fun p => some (.cell (p,0) blankPayload))) (fun _ : Fin 1 => none) i) z)).1 =
      sourceWrittenPayload c (sourceTotalAction M c) z i := by
  intro i z
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left, sourceWrittenPayload]
    by_cases hz : z = 0
    · subst z
      have h := hf (j.castAdd 1) 0
      simp only [sourcePayload, Fin.addCases_left, add_zero] at h
      cases hw : ((sourceTotalAction M c).workTapes j).1 <;>
        simp only [setupWrite, Option.map_none, Option.map_some, Function.update_self,
          if_true, Option.getD_none, Option.getD_some]
      · exact h
      · rfl
    · have h := hf (j.castAdd 1) z
      simp only [sourcePayload, Fin.addCases_left] at h
      cases hw : ((sourceTotalAction M c).workTapes j).1 <;>
        simp [setupWrite, hw, Function.update_of_ne hz, h, hz]
  · simpa only [Fin.addCases_right, setupWrite, sourceWrittenPayload, sourcePayload] using hf (j.natAdd M.k) z

/-- The two actual data sweeps implement the prescribed neighbor selection on
the whole marked interval. Positioning scans and turns only maintain registers.
**Proof sketch.** Compose the four exact scan paths. The forward invariant
supplies every cached left neighbor to the backward invariant; blank boundary
registers are justified by the two endpoint hypotheses. -/
private lemma dataCfg_sweeps (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read : Fin (M.k + 1) → OblPayload) (f : ℤ → Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = f z i)
    (hleft : f (-(R : ℤ) - 1) = fun _ => blankPayload)
    (hright : f ((R : ℤ) + 1) = fun _ => blankPayload) :
    ∃ tapes',
      (dataTM W M a).tm.runFrom
        (dataCfg W M a base .seekLeft u 0 (q,b,read,fun _ => blankPayload) tapes out) (6 * R + 7) =
        dataCfg W M a base .macroCheck (u + 1) 0
          ((obliviousSourceAction M q read).state,b,read,f (-(R : ℤ))) tapes' out ∧
      (∀ i z, (dataCell (tapes' i z)).1 =
        if -(R : ℤ) ≤ z ∧ z ≤ R then f (z + (obliviousSourceMove M q read i : ℤ)) i else f z i) := by
  obtain ⟨tf, hforward, hfirst, hcache⟩ :=
    dataCfg_forward_prefix W M a base u R q b read f tapes out hg hf (2 * R + 1) (le_refl _)
  have hfpos : -(R : ℤ) + (2 * R + 1 : ℕ) = (R : ℤ) + 1 := by omega
  rw [hfpos, hleft] at hforward
  have hcache' : ∀ i z, -(R : ℤ) ≤ z → z ≤ R → (dataCell (tf i z)).2 = f (z - 1) i := by
    intro i z hl hr
    exact hcache i z hl (by omega)
  obtain ⟨tb, hback, hshift, _⟩ :=
    dataCfg_backward_prefix W M a base u R q b read f tf out hg hfirst hcache'
      (2 * R + 1) (le_refl _)
  have hbpos : (R : ℤ) - (2 * R + 1 : ℕ) = -(R : ℤ) - 1 := by omega
  rw [hbpos, hright, show -(R : ℤ) - 1 + 1 = -(R : ℤ) by omega] at hback
  refine ⟨tb, ?_, ?_⟩
  · rw [show 6 * R + 7 = (R + 2) + ((2 * R + 1) + (((2 * R + 1) + ((R + 1) + 1)) + 1)) by omega,
      MultiTapeTM.runFrom_add, dataCfg_seek_run W M a base u R q b read tapes out hg,
      MultiTapeTM.runFrom_add, hforward, MultiTapeTM.runFrom_succ_eq_step,
      dataCfg_forward_turn W M a base u R q b read _ tf out hg,
      MultiTapeTM.runFrom_add, hback, MultiTapeTM.runFrom_succ_eq_step,
      dataCfg_backward_turn W M a base u R _ tb out hg,
      dataCfg_center_run W M a base u R q b read _ tb out hg]
  · intro i z
    rw [hshift]
    have he : ((R : ℤ) - (2 * R + 1 : ℕ) < z ∧ z ≤ R) ↔ (-(R : ℤ) ≤ z ∧ z ≤ R) := by omega
    simp only [he]

/-- An origin write cannot affect a different relative coordinate. -/
private lemma sourceWrittenPayload_away (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (z : ℤ) (hz : z ≠ 0) :
    sourceWrittenPayload c (sourceTotalAction M c) z = sourcePayload c z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [sourceWrittenPayload, sourcePayload, hz]

/-- One complete actual macrostep simulates one totalized source step. Its
output stream is unchanged, even when the source emits or has already halted.
**Proof sketch.** The origin update selects the source action from the represented
reads. The operational sweep theorem shifts its written payloads by the native
head displacements. Both old and new source support are inside the marked zone,
so the unchanged exterior is also correct. The return scan commits the successor
state, and the finite answer register remembers the source's last output. -/
private lemma dataCfg_simulates (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) {word : List Bool} (c : Cfg M.k Bool M.State word)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u = some .unit)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = sourcePayload c z i)
    (hs : ∀ z, z < -(R : ℤ) ∨ (R : ℤ) < z → sourcePayload c z = fun _ => blankPayload)
    (hs' : ∀ z, z < -(R : ℤ) ∨ (R : ℤ) < z → sourcePayload (M.tm.step c) z = fun _ => blankPayload) :
    ∃ read' carry' tapes',
      (dataTM W M a).tm.runFrom
        (dataCfg W M a base .macroCheck u 0 (c.state,c.output.getLast?.getD false,read,carry) tapes out)
        (6 * R + 8) =
        dataCfg W M a base .macroCheck (u + 1) 0
          ((M.tm.step c).state,(M.tm.step c).output.getLast?.getD false,read',carry') tapes' out ∧
      (∀ i z, (dataCell (tapes' i z)).1 = sourcePayload (M.tm.step c) z i) := by
  let act := sourceTotalAction M c
  let f := sourceWrittenPayload c act
  let written := fun i => setupWrite (tapes i) 0
    (Fin.addCases (fun j => (act.workTapes j).1.map (fun p => some (.cell (p,0) blankPayload)))
      (fun _ : Fin 1 => none) i)
  have hread : (fun i => (dataCell (tapes i 0)).1) = sourcePayload c 0 := funext (fun i => hf i 0)
  have hboundary (z : ℤ) (hz : z < -(R : ℤ) ∨ (R : ℤ) < z) : f z = fun _ => blankPayload := by
    dsimp only [f, act]
    rw [sourceWrittenPayload_away M c z (by omega)]
    exact hs z hz
  obtain ⟨ts, hrun, hts⟩ := dataCfg_sweeps W M a base u R c.state
    (act.output.getD (c.output.getLast?.getD false)) (sourcePayload c 0) f written out hg
    (dataCfg_written M c tapes hf)
    (hboundary _ (by omega)) (hboundary _ (by omega))
  have hstate : act.state = (M.tm.step c).state :=
    congrArg Cfg.state (sourceTotalAction_apply M c)
  have hanswer : act.output.getD (c.output.getLast?.getD false) =
      (M.tm.step c).output.getLast?.getD false := by
    rw [← sourceTotalAction_apply M c]
    exact (lastOutput_append c.output act.output).symm
  refine ⟨sourcePayload c 0, f (-(R : ℤ)), ts, ?_, ?_⟩
  · rw [show 6 * R + 8 = (6 * R + 7) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step, dataCfg_check W M a base u _ tapes out hu]
    dsimp only
    rw [hread, obliviousSourceAction_correct]
    change (dataTM W M a).tm.runFrom
      (dataCfg W M a base .seekLeft u 0
        (c.state,act.output.getD (c.output.getLast?.getD false),sourcePayload c 0,fun _ => blankPayload)
        written out) (6 * R + 7) = _
    rw [hrun, obliviousSourceAction_correct, hstate, hanswer]
  · intro i z
    rw [hts, obliviousSourceMove_correct]
    by_cases hz : -(R : ℤ) ≤ z ∧ z ≤ R
    · rw [if_pos hz]
      dsimp only [f, act]
      rw [← sourcePayload_apply c (sourceTotalAction M c) z i, sourceTotalAction_apply M c]
    · rw [if_neg hz]
      have ho : z < -(R : ℤ) ∨ (R : ℤ) < z := by omega
      rw [hboundary z ho, hs' z ho]

/-- Payloads after copying the left input boundary and `j` following cells. -/
private def copiedPayload (M : FinTM Bool) (x : List Bool) (j : ℕ) (z : ℤ) :
    Fin (M.k + 1) → OblPayload :=
  Fin.addCases (fun _ => blankPayload) (fun _ =>
    if z = -1 ∨ (0 ≤ z ∧ z < j) then inputPayload x z else blankPayload)

/-- The copied input, including both blank boundary tags, represents the initial
source configuration exactly; every source work tape is still blank. -/
private lemma copiedPayload_full (M : FinTM Bool) (x : List Bool) :
    copiedPayload M x (x.length + 1) = sourcePayload (M.tm.initCfg x) := by
  funext z i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [copiedPayload, sourcePayload, blankPayload]
  · simp only [copiedPayload, sourcePayload, Fin.addCases_right, MultiTapeTM.initCfg,
      Cfg.init, Fin.val_one, Int.natCast_one, sub_self, zero_add]
    split_ifs with h
    · rfl
    · exact (inputPayload_outside x z (by omega)).symm

/-- The input-lane write used by every copy transition. -/
private def copyDataWrite (M : FinTM Bool) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (z : ℤ) (p : OblPayload) : Fin (M.k + 1) → ℤ → Option OblSymbol :=
  fun i => setupWrite (tapes i) z
    (Fin.addCases (fun _ => none) (fun _ : Fin 1 => some (some (.cell p blankPayload))) i)

/-- Copying the left boundary creates precisely the zero-length copy prefix. -/
private lemma copyDataWrite_left (M : FinTM Bool) (x : List Bool)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = blankPayload) :
    ∀ i z, (dataCell (copyDataWrite M tapes (-1) (none,1) i z)).1 = copiedPayload M x 0 z i := by
  intro i z
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [copyDataWrite, copiedPayload, Fin.addCases_left, setupWrite, hf]
  · simp only [copyDataWrite, copiedPayload, Fin.addCases_right, setupWrite]
    by_cases hz : z = -1
    · subst z
      simp [Function.update_self, dataCell, inputPayload, FinTM.bufferTape]
    · rw [Function.update_of_ne hz, hf]
      rw [if_neg (by omega)]

/-- A copy transition extends the represented prefix by exactly one cell. -/
private lemma copyDataWrite_next (M : FinTM Bool) (x : List Bool) (j : ℕ)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = copiedPayload M x j z i) :
    ∀ i z, (dataCell (copyDataWrite M tapes j (inputPayload x j) i z)).1 =
      copiedPayload M x (j + 1) z i := by
  intro i z
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simpa only [copyDataWrite, copiedPayload, Fin.addCases_left, setupWrite] using hf (k.castAdd 1) z
  · simp only [copyDataWrite, copiedPayload, Fin.addCases_right, setupWrite]
    by_cases hz : z = (j : ℤ)
    · subst z
      simp only [Function.update_self, dataCell, if_pos (show (j : ℤ) = -1 ∨ (0 ≤ (j : ℤ) ∧ (j : ℤ) < (j + 1 : ℕ)) by omega)]
    · rw [Function.update_of_ne hz, hf]
      simp only [copiedPayload, Fin.addCases_right]
      have he : (z = -1 ∨ 0 ≤ z ∧ z < (j : ℤ)) ↔ (z = -1 ∨ 0 ≤ z ∧ z < (j + 1 : ℕ)) := by omega
      simp only [he]

/-- Data assertions used during initialization: the finite registers and output
remain initial, while the first payloads have the supplied tape interpretation. -/
private def initialContent (M : FinTM Bool) (f : ℤ → Fin (M.k + 1) → OblPayload)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) : Prop :=
  d = obliviousDataInit M ∧ out = [] ∧ ∀ i z, (dataCell (tapes i z)).1 = f z i

/-- The initialization invariant retains full data information until the first
macrostep. Later macrosteps have a strictly larger unary-head position, so they
cannot re-enter the first-macrostep clause. The unary origin is unique. -/
private def prepCondition {S : Type} {a : ℕ} (M : FinTM Bool) (x : List Bool)
    (phase : Option (OblPhase S a)) (p : ℕ) (u g : ℤ) (ut : ℤ → Option OblSymbol)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) : Prop :=
  let sentinel := ∀ z, ut z = some .origin ↔ z = 0
  let blank := initialContent M (fun _ _ => blankPayload) d tapes out
  let full := initialContent M (copiedPayload M x (x.length + 1)) d tapes out
  match phase with
  | none => True
  | some .init => u = 0 ∧ g = 0 ∧ (∀ z, ut z = none) ∧ blank
  | some (.clock _) | some .resetStart => sentinel ∧ u = 1 ∧ g = 0 ∧ blank
  | some .resetScan => sentinel ∧ u = 1 ∧ g = 0 ∧ p ≤ x.length ∧ blank
  | some .copyLeft => sentinel ∧ u = 1 ∧ g = 0 ∧ p = 1 ∧ blank
  | some .copyLeftWrite => sentinel ∧ u = 1 ∧ g = -1 ∧ p = 1 ∧ blank
  | some .copyFirst | some .copyMore => sentinel ∧ u = 1 ∧
      ∃ j, j ≤ x.length ∧ p = j + 1 ∧ g = j ∧ initialContent M (copiedPayload M x j) d tapes out
  | some .copyReturn | some .budgetStart | some .budgetBack | some (.append _) | some (.borrow _) =>
      sentinel ∧ 1 ≤ u ∧ full
  | some .startCenter => sentinel ∧ u = 1 ∧ full
  | some .macroCheck => sentinel ∧ 1 ≤ u ∧ (u = 1 → full)
  | some .seekLeft | some .forward | some .backward | some .returnCenter => sentinel ∧ 1 ≤ u
  | _ => sentinel ∧ full

/-- Configuration form of the initialization invariant. -/
private def prepInvariant (W M : FinTM Bool) (a : ℕ) (x : List Bool)
    (c : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed))
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) : Prop :=
  prepCondition M x c.state c.inputPos.val
    (c.workTapePos (Fin.natAdd W.k (1 : Fin 3))) (c.workTapePos (Fin.natAdd W.k (2 : Fin 3)))
    (c.workTapes (Fin.natAdd W.k (1 : Fin 3))) d tapes out

/-- The input reads blank exactly at one of the two native boundaries. -/
private lemma inputSymbol_blank {A S : Type} {k : ℕ} {x : List A} (c : Cfg k A S x) :
    c.inputSymbol = none ↔ c.inputPos.val = 0 ∨ c.inputPos.val = x.length + 1 := by
  unfold Cfg.inputSymbol
  simp only [Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

/-- At the copy position, an embedded native input read gives the next bit or
its right blank boundary. This includes an empty input. -/
private lemma copy_input_read {S : Type} {k : ℕ} (x : List Bool)
    (c : Cfg k OblSymbol S (x.map oblEmbed)) (j : ℕ) (hj : j ≤ x.length)
    (hp : c.inputPos.val = j + 1) :
    c.inputSymbol = (x[j]?).map OblSymbol.bit := by
  by_cases h : j < x.length
  · rw [inputSymbolInner j (by omega) (by simpa only [List.length_map] using h)]
    simp only [List.getElem_map, oblEmbed, Function.Embedding.coeFn_mk, List.getElem?_eq_getElem h,
      Option.map_some]
  · have he : j = x.length := by omega
    have hb := (inputSymbol_blank c).mpr (Or.inr (by simp only [List.length_map]; omega))
    rw [hb, List.getElem?_eq_none (by omega), Option.map_none]

/-- Copying an embedded read writes the exact virtual input payload. -/
private lemma copy_input_payload {S : Type} {k : ℕ} (x : List Bool)
    (c : Cfg k OblSymbol S (x.map oblEmbed)) (j : ℕ) (hj : j ≤ x.length)
    (hp : c.inputPos.val = j + 1) :
    (clockBit c.inputSymbol, if c.inputSymbol.isNone then 2 else 0) = inputPayload x j := by
  rw [copy_input_read x c j hj hp]
  by_cases h : j < x.length
  · rw [List.getElem?_eq_getElem h]
    simp [clockBit, inputPayload, FinTM.bufferTape, show (j : ℤ) ≠ -1 by omega, show j ≠ x.length by omega]
  · have he : j = x.length := by omega
    subst j
    simp [clockBit, inputPayload, FinTM.bufferTape, show (x.length : ℤ) ≠ -1 by omega]

/-- Evaluating the preparation invariant after a non-clock schedule action
exposes only its input move, unary tape update, and two distinguished heads. -/
private lemma prepInvariant_action (W M : FinTM Bool) (a : ℕ) (x : List Bool)
    (c : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed))
    (q : Option (OblPhase W.State a)) (inp : SignType)
    (b u g : Option (Option OblSymbol) × SignType)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) :
    prepInvariant W M a x ((oblAction q inp b u g).apply c) d tapes out =
      prepCondition M x q (moveInputPos c.inputPos inp).val
        (c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) + u.2)
        (c.workTapePos (Fin.natAdd W.k (2 : Fin 3)) + g.2)
        (setupWrite (c.workTapes (Fin.natAdd W.k (1 : Fin 3)))
          (c.workTapePos (Fin.natAdd W.k (1 : Fin 3))) u.1) d tapes out := by
  cases hu : u.1 <;> simp [prepInvariant, oblAction, setupWrite, hu]

/-- The unique unary origin survives writing a unit at a positive coordinate. -/
private lemma unaryOrigin_update (ut : ℤ → Option OblSymbol) (u : ℤ) (hu : 1 ≤ u)
    (h : ∀ z, ut z = some .origin ↔ z = 0) :
    ∀ z, Function.update ut u (some .unit) z = some .origin ↔ z = 0 := by
  intro z
  by_cases hz : z = u
  · subst z
    simp [show u ≠ 0 by omega]
  · rw [Function.update_of_ne hz, h]

/-- Preparation is invariant under every decorated transition. Once simulation
has begun, the unary head only increases, so the first macrostep still carries
the completely copied input when initialization's schedule theorem reaches it.
**Proof sketch.** Clock and reset phases preserve blank data. Copy phases extend
the represented input prefix; allocation preserves that complete copy. The
unique unary origin forces entry at counter position one. Each later return to
the macrostep controller increments that position. -/
private lemma prepInvariant_step (W M : FinTM Bool) (a : ℕ) (x : List Bool)
    (c : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed))
    (q : OblPhase W.State a) (hs : c.state = some q)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (h : prepInvariant W M a x c d tapes out) :
    let v := obliviousVisit W M a q d c.inputSymbol c.workTapeSymbols
      (fun i => tapes i (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))))
    prepInvariant W M a x ((obliviousSchedule W a).tm.step c) v.1
      (fun i => setupWrite (tapes i) (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))) (v.2.1 i))
      (out ++ v.2.2.toList) := by
  dsimp only
  simp only [MultiTapeTM.step, hs]
  simp only [prepInvariant, hs] at h
  cases q with
  | init =>
    rcases h with ⟨hu, hg, hut, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    simp only [prepCondition, setupWrite, hu, hg, SignType.cast, zero_add, add_zero]
    refine ⟨?_, trivial, trivial, hd⟩
    intro z
    change (Function.update (c.workTapes (Fin.natAdd W.k (1 : Fin 3)))
      (c.workTapePos (Fin.natAdd W.k (1 : Fin 3))) (some .origin) z = some .origin) ↔ z = 0
    rw [hu]
    by_cases hz : z = 0
    · subst z
      exact ⟨fun _ => rfl, fun _ => Function.update_self _ _ _⟩
    · rw [Function.update_of_ne hz, hut]
      simp [hz]
  | clock s =>
    rcases h with ⟨hut, hu, hg, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one, Nat.one_ne_zero, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
      SignType.coe_zero, add_zero]
    cases hn : (W.tm.tr s (c.inputSymbol.map (fun _ => false))
      (fun i => clockBit (c.workTapeSymbols (i.castAdd 3)))).state <;>
      simpa [hn, prepCondition] using
        (show (∀ z, c.workTapes (Fin.natAdd W.k (1 : Fin 3)) z = some .origin ↔ z = 0) ∧
          c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) = 1 ∧
          c.workTapePos (Fin.natAdd W.k (2 : Fin 3)) = 0 ∧
          initialContent M (fun _ _ => blankPayload) d tapes out from ⟨hut,hu,hg,hd⟩)
  | resetStart =>
    rcases h with ⟨hut, hu, hg, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    simp only [prepCondition, setupWrite, SignType.coe_zero, add_zero, FinTM.moveInputPos_neg_val]
    refine ⟨hut, hu, hg, ?_, hd⟩
    have hp := c.inputPos.isLt
    simp only [List.length_map] at hp
    omega
  | resetScan =>
    rcases h with ⟨hut, hu, hg, hp, hd⟩
    cases hi : c.inputSymbol with
    | none =>
      have hp0 : c.inputPos.val = 0 := by
        have hb := (inputSymbol_blank c).mp hi
        simp only [List.length_map] at hb
        omega
      have hmove : (moveInputPos c.inputPos .pos).val = 1 := by
        rw [moveInputPos_pos_of_ne_right _ (by simp only [List.length_map]; omega)]
        change c.inputPos.val + 1 = 1
        omega
      simp only [obliviousSchedule, obliviousVisit, hi, setupWrite, Option.toList_none, List.append_nil]
      rw [prepInvariant_action]
      exact ⟨hut, by simpa using hu, by simpa using hg, hmove, hd⟩
    | some bit =>
      simp only [obliviousSchedule, obliviousVisit, hi, setupWrite, Option.toList_none, List.append_nil]
      rw [prepInvariant_action]
      exact ⟨hut, by simpa using hu, by simpa using hg,
        by simpa only [FinTM.moveInputPos_neg_val] using (Nat.sub_le c.inputPos.val 1).trans hp, hd⟩
  | copyLeft =>
    rcases h with ⟨hut, hu, hg, hp, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    exact ⟨hut, by simpa using hu, by simpa [hg, SignType.cast], by simpa using hp, hd⟩
  | copyLeftWrite =>
    rcases h with ⟨hut, hu, hg, hp, hd, ho, ht⟩
    simp only [obliviousSchedule, obliviousVisit, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    refine ⟨hut, by simpa using hu, 0, Nat.zero_le _, by simpa using hp, ?_, hd, ho, ?_⟩
    · simpa [hg, SignType.cast]
    · simpa only [hg, copyDataWrite] using copyDataWrite_left M x tapes ht
  | copyFirst | copyMore =>
    all_goals
      rcases h with ⟨hut, hu, j, hj, hp, hg, hd, ho, ht⟩
      have hpay := copy_input_payload x c j hj hp
      have hwrite := copyDataWrite_next M x j tapes ht
      by_cases hjn : j = x.length
      · have hi : c.inputSymbol = none := by
          rw [copy_input_read x c j hj hp, List.getElem?_eq_none (by omega), Option.map_none]
        simp only [obliviousSchedule, obliviousVisit, hi, Option.isNone_none, ↓reduceIte,
          Option.toList_none, List.append_nil]
        rw [prepInvariant_action]
        refine ⟨hut, by simpa [hu], hd, ho, ?_⟩
        rw [hi] at hpay
        simp only [Option.isNone_none, ite_true] at hpay
        rw [← hpay] at hwrite
        simpa only [hg, hjn, copyDataWrite] using hwrite
      · have hjlt : j < x.length := by omega
        have hi : c.inputSymbol = some (.bit (x[j]'hjlt)) := by
          rw [copy_input_read x c j hj hp, List.getElem?_eq_getElem hjlt, Option.map_some]
        have hmove : (moveInputPos c.inputPos .pos).val = j + 1 + 1 := by
          rw [moveInputPos_pos_of_ne_right _ (by simp only [List.length_map]; omega)]
          change c.inputPos.val + 1 = j + 1 + 1
          omega
        simp only [obliviousSchedule, obliviousVisit, hi, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
          Option.toList_none, List.append_nil]
        rw [prepInvariant_action]
        refine ⟨hut, by simpa using hu, j + 1, by omega, hmove, ?_, hd, ho, ?_⟩
        · simp [hg, SignType.cast]
        · rw [hi] at hpay
          simp only [Option.isNone_some, Bool.false_eq_true, ite_false] at hpay
          rw [← hpay] at hwrite
          simpa only [hg, copyDataWrite] using hwrite
  | copyReturn =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split <;> rw [prepInvariant_action] <;> exact ⟨hut, by simpa using hu, hd⟩
  | budgetStart =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    exact ⟨hut, by simpa using hu, hd⟩
  | budgetBack =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split <;> rw [prepInvariant_action] <;> exact ⟨hut, by simpa using hu, hd⟩
  | append i =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split
    · rw [prepInvariant_action]
      exact ⟨unaryOrigin_update _ _ hu hut, by simpa [SignType.cast] using (by omega : 1 ≤ c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) + 1), hd⟩
    · rw [prepInvariant_action]
      exact ⟨hut, by simpa using hu, hd⟩
  | borrow carry =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split
    · rw [prepInvariant_action]
      exact ⟨hut, by simpa using hu, hd⟩
    · split <;> rw [prepInvariant_action]
      · exact ⟨hut, hd⟩
      · exact ⟨hut, by simpa using hu, hd⟩
  | unaryStart =>
    rcases h with ⟨hut, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    exact ⟨hut, hd⟩
  | unaryBack | layoutRight i | layoutReturn i | layoutLeft i =>
    all_goals
      rcases h with ⟨hut, hd⟩
      simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
      split <;> rw [prepInvariant_action] <;> exact ⟨hut, hd⟩
  | rightEdge | leftEdge =>
    all_goals
      rcases h with ⟨hut, hd⟩
      simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
      rw [prepInvariant_action]
      exact ⟨hut, hd⟩
  | unaryReset =>
    rcases h with ⟨hut, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split
    · rename_i he
      rw [prepInvariant_action]
      refine ⟨hut, ?_, hd⟩
      have hu := (hut _).mp he
      simp [hu, SignType.cast]
    · rw [prepInvariant_action]
      exact ⟨hut, hd⟩
  | startCenter =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split <;> rw [prepInvariant_action]
    · exact ⟨hut, by simp [hu], fun _ => hd⟩
    · exact ⟨hut, by simpa using hu, hd⟩
  | macroCheck =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit]
    split <;> rw [prepInvariant_action]
    · exact ⟨hut, by simpa using hu⟩
    · trivial
  | seekLeft | forward | backward =>
    all_goals
      rcases h with ⟨hut, hu⟩
      simp only [obliviousSchedule, obliviousVisit]
      split <;> rw [prepInvariant_action] <;> exact ⟨hut, by simpa using hu⟩
  | returnCenter =>
    rcases h with ⟨hut, hu⟩
    simp only [obliviousSchedule, obliviousVisit]
    split <;> rw [prepInvariant_action]
    · refine ⟨hut, by simpa [SignType.cast] using (by omega : 1 ≤ c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) + 1), ?_⟩
      intro he
      simp only [SignType.cast] at he
      omega
    · exact ⟨hut, by simpa using hu⟩

/-- The preparation invariant holds at every actual logical time. This also
retains an exact decomposition into schedule, data registers, tapes, and output.
**Proof sketch.** The initial configuration has blank data. Each live transition
uses the local invariant and the exact decorated-step identity. A halted
configuration is fixed, so the same representation remains valid thereafter. -/
private lemma prepInvariant_run (W M : FinTM Bool) (a : ℕ) (x : List Bool) (t : ℕ) :
    ∃ d tapes out,
      (dataTM W M a).tm.runFrom ((dataTM W M a).tm.initCfg (x.map oblEmbed)) t =
        decoratedCfg (Fin.natAdd W.k (2 : Fin 3))
          ((obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t)
          d tapes out ∧
      prepInvariant W M a x
        ((obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t)
        d tapes out := by
  classical
  induction t with
  | zero =>
    refine ⟨obliviousDataInit M, fun _ _ => none, [], ?_, ?_⟩
    · exact decoratedCfg_init _ _ _ _ _ _
    · simp [prepInvariant, prepCondition, obliviousSchedule, initialContent, dataCell]
  | succ t ih =>
    obtain ⟨d, tapes, out, hrun, hinv⟩ := ih
    let c := (obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t
    change prepInvariant W M a x c d tapes out at hinv
    cases hs : c.state with
    | none =>
      refine ⟨d, tapes, out, ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_succ_eq_step', hrun, MultiTapeTM.runFrom_succ_eq_step']
        change (dataTM W M a).tm.step (decoratedCfg _ c d tapes out) =
          decoratedCfg _ ((obliviousSchedule W a).tm.step c) d tapes out
        rw [MultiTapeTM.step_of_halt (show (decoratedCfg _ c d tapes out).state = none by simp [decoratedCfg, hs]),
          MultiTapeTM.step_of_halt hs]
      · rw [MultiTapeTM.runFrom_succ_eq_step']
        change prepInvariant W M a x ((obliviousSchedule W a).tm.step c) d tapes out
        rw [MultiTapeTM.step_of_halt hs]
        exact hinv
    | some q =>
      let v := obliviousVisit W M a q d c.inputSymbol c.workTapeSymbols
        (fun i => tapes i (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))))
      refine ⟨v.1, fun i => setupWrite (tapes i) (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))) (v.2.1 i),
        out ++ v.2.2.toList, ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_succ_eq_step', hrun, MultiTapeTM.runFrom_succ_eq_step']
        exact decoratedCfg_step (obliviousSchedule W a) _ _ _ _ c q hs d tapes out
      · rw [MultiTapeTM.runFrom_succ_eq_step']
        exact prepInvariant_step W M a x c q hs d tapes out hinv

/-- Restating a configuration using its current macrostep heads changes nothing. -/
private lemma macroCfg_self (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (c : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) :
    macroCfg W a c c.state (c.workTapePos (Fin.natAdd W.k (1 : Fin 3)))
      (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))) = c := by
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [macroCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [macroCfg]
  · rfl

/-- The initialized schedule reaches a fully allocated first macrostep. This
extracts the endpoint of clock capture and the exact initialization ledger.
**Proof sketch.** The captured bits have value `T(n)`. The input-length bound
justifies allocation, and composition of the clock and initialization run identities
gives the required unary tape, guide, state, and initial macrostep head positions. -/
private lemma obliviousSchedule_ready (W : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (x : List Bool) :
    ∃ t,
      let c := (obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t
      c.state = some .macroCheck ∧
      c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) = 1 ∧
      c.workTapePos (Fin.natAdd W.k (2 : Fin 3)) = 0 ∧
      c.workTapes (Fin.natAdd W.k (1 : Fin 3)) = unaryTape ((a + 1) * (T x.length + 1)) ∧
      c.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape (3 * ((a + 1) * (T x.length + 1))) := by
  obtain ⟨τ, _, c, hs, ho, hclock⟩ := clockStageCfg_captures W a b T hW x
  have hv : budgetValue c.output = T x.length := by rw [ho, budgetValue_bits]
  have hn : (x.map oblEmbed).length + 1 ≤ (a + 1) * (T x.length + 1) := by
    simp only [List.length_map]
    exact (Nat.add_le_add_right (hT x.length) 1).trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right (T x.length + 1) (show 1 ≤ a + 1 by omega))
  obtain ⟨w', _, hinit⟩ := setupCfg_initializes W a (clockStageCfg W a c)
    (clockStageCfg W a c).inputPos c.output (T x.length) hv hn
  rw [← clockStageCfg_setup W a c hs] at hinit
  refine ⟨(τ + 1) + (((clockStageCfg W a c).inputPos.val - 1 + 2) +
    ((2 * (x.map oblEmbed).length + 4) + ((T x.length + 1) * (2 * c.output.length + (a + 1) + 4) +
      (14 * ((a + 1) * (T x.length + 1)) + 10)))), ?_⟩
  dsimp only
  rw [MultiTapeTM.runFrom_add, hclock, hinit]
  simp [setupCfg]

/-- The actual logical machine reaches the first macrostep with the initial
source configuration represented on its data tapes and with no output yet.
**Proof sketch.** Apply the invariant at the time supplied by the schedule endpoint.
The unary head is at one, so the first-macrostep clause yields the original source
state and complete input copy. Re-express the same schedule configuration in the
macrostep representation. -/
private lemma dataTM_ready (W M : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (x : List Bool) :
    ∃ (t : ℕ) (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed))
      (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol),
      base.workTapes (Fin.natAdd W.k (1 : Fin 3)) = unaryTape ((a + 1) * (T x.length + 1)) ∧
      base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape (3 * ((a + 1) * (T x.length + 1))) ∧
      (dataTM W M a).tm.runFrom ((dataTM W M a).tm.initCfg (x.map oblEmbed)) t =
        dataCfg W M a base .macroCheck 1 0 (obliviousDataInit M) tapes [] ∧
      (∀ i z, (dataCell (tapes i z)).1 = sourcePayload (M.tm.initCfg x) z i) := by
  obtain ⟨t, hs, hu, hg, hut, hgt⟩ := obliviousSchedule_ready W a b T hW hT x
  obtain ⟨d, tapes, out, hrun, hinv⟩ := prepInvariant_run W M a x t
  let base := (obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t
  change prepInvariant W M a x base d tapes out at hinv
  change base.state = some .macroCheck at hs
  change base.workTapePos (Fin.natAdd W.k (1 : Fin 3)) = 1 at hu
  change base.workTapePos (Fin.natAdd W.k (2 : Fin 3)) = 0 at hg
  simp only [prepInvariant, hs, hu, prepCondition] at hinv
  obtain ⟨hd, ho, ht⟩ := hinv.2.2 trivial
  subst d
  subst out
  refine ⟨t, base, tapes, hut, hgt, ?_, ?_⟩
  · rw [hrun]
    have hm := macroCfg_self W a base
    rw [hs, hu, hg] at hm
    simp only [dataCfg, hm]
    rfl
  · simpa only [copiedPayload_full] using ht

/-- The padded sequence of actual macrosteps represents the source run at every
macrostep boundary, while emitting no output. Early source halting is handled
by the same totalized one-step simulation at every remaining budget cell.
**Proof sketch.** Induct on the macrostep index. The unary tape supplies a live
budget cell, source bounds justify both old and new support, and the operational
macrostep theorem advances exactly one source step at the fixed cost. -/
private lemma dataCfg_iterates (W M : FinTM Bool) (a : ℕ) (x : List Bool)
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed)) (B : ℕ)
    (hn : x.length + 1 ≤ B)
    (hut : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) = unaryTape B)
    (hgt : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape (3 * B))
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = sourcePayload (M.tm.initCfg x) z i)
    (j : ℕ) (hj : j ≤ B) :
    ∃ read carry tapes',
      (dataTM W M a).tm.runFrom (dataCfg W M a base .macroCheck 1 0 (obliviousDataInit M) tapes [])
        (j * (6 * (3 * B) + 8)) =
        dataCfg W M a base .macroCheck ((j : ℤ) + 1) 0
          ((M.tm.runFrom (M.tm.initCfg x) j).state,
            (M.tm.runFrom (M.tm.initCfg x) j).output.getLast?.getD false,read,carry) tapes' [] ∧
      (∀ i z, (dataCell (tapes' i z)).1 = sourcePayload (M.tm.runFrom (M.tm.initCfg x) j) z i) := by
  induction j with
  | zero =>
    refine ⟨fun _ => blankPayload, fun _ => blankPayload, tapes, ?_, hf⟩
    simp [obliviousDataInit]
  | succ j ih =>
    obtain ⟨read, carry, ts, hrun, hrep⟩ := ih (by omega)
    have hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((j : ℤ) + 1) = some .unit := by
      rw [hut]
      exact unaryTape_unit B j (by omega)
    have hs (t : ℕ) (ht : t ≤ B) (z : ℤ) (hz : z < -((3 * B : ℕ) : ℤ) ∨ ((3 * B : ℕ) : ℤ) < z) :
        sourcePayload (M.tm.runFrom (M.tm.initCfg x) t) z = fun _ => blankPayload := by
      funext i
      exact sourcePayload_support M x t B ht hn z (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hz) i
    obtain ⟨read', carry', ts', hstep, hrep'⟩ := dataCfg_simulates W M a base ((j : ℤ) + 1)
      (3 * B) (M.tm.runFrom (M.tm.initCfg x) j) read carry ts [] hgt hu hrep
      (hs j (by omega)) (by simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hs (j + 1) hj)
    refine ⟨read', carry', ts', ?_, ?_⟩
    · rw [Nat.succ_mul, MultiTapeTM.runFrom_add, hrun, hstep, MultiTapeTM.runFrom_succ_eq_step']
      rw [show ((j + 1 : ℕ) : ℤ) + 1 = (j : ℤ) + 1 + 1 by omega]
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hrep'

/-- A failed final counter test emits exactly the saved answer and halts in one
transition; it does not inspect the represented source's acceptance state. -/
private lemma dataCfg_finish (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u ≠ some .unit) :
    ((dataTM W M a).tm.step (dataCfg W M a base .macroCheck u 0 d tapes [])).state = none ∧
    ((dataTM W M a).tm.step (dataCfg W M a base .macroCheck u 0 d tapes [])).output = [.bit d.2.1] := by
  rw [dataCfg_step, macroCfg_check, if_neg hu]
  simp only [obliviousVisit, macroCfg_unary, if_neg hu]
  simp only [decoratedCfg, macroCfg, Option.map_none, Option.toList_some, List.nil_append, and_self]

/-- The logical simulator eventually produces precisely the decision bit.
Its separately proved schedule ledger will supply the quadratic time bound.
**Proof sketch.** Compose initialization with all `B` operational macrosteps and
the final counter test. The padded source run has already halted with its decision
bit, so the last-output register makes the sole emitted bit correct. -/
private lemma dataTM_computes (W M : FinTM Bool) (L : Language Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (hM : M.DecidesInTime L (fun n => a * T n)) (x : List Bool) :
    ∃ t, (dataTM W M a).ComputesInTime (x.map oblEmbed)
      [OblSymbol.bit (MultiTapeTM.indicator (L : Set (List Bool)) x)] t := by
  obtain ⟨t, base, tapes, hut, hgt, hready, hrep⟩ := dataTM_ready W M a b T hW hT x
  let B := (a + 1) * (T x.length + 1)
  have hn : x.length + 1 ≤ B := by
    apply (Nat.add_le_add_right (hT x.length) 1).trans
    simpa only [one_mul] using Nat.mul_le_mul_right (T x.length + 1) (show 1 ≤ a + 1 by omega)
  obtain ⟨read, carry, ts, hrun, _⟩ := dataCfg_iterates W M a x base B hn hut hgt tapes hrep B (le_refl _)
  have hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((B : ℤ) + 1) ≠ some .unit := by
    rw [hut, unaryTape_end]
    exact Option.noConfusion
  have hfinish := dataCfg_finish W M a base ((B : ℤ) + 1)
    ((M.tm.runFrom (M.tm.initCfg x) B).state,
      (M.tm.runFrom (M.tm.initCfg x) B).output.getLast?.getD false,read,carry) ts hu
  refine ⟨(t + B * (6 * (3 * B) + 8)) + 1, ?_⟩
  rw [FinTM.computesInTime_iff, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hready, hrun]
  exact ⟨hfinish.1, hfinish.2.trans (congrArg (fun bit => [OblSymbol.bit bit])
    (sourceAnswer_at_budget M L T a hM x))⟩

/-- Correctness and the independent quadratic halting certificate refer to the
same deterministic binary simulator, so they give the decision bit at the
quadratic deadline. No unproved simulation theorem enters this argument. -/
private lemma obliviousCandidate_decides (W M : FinTM Bool) (L : Language Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (hM : M.DecidesInTime L (fun n => a * T n)) :
    (obliviousCandidate W M a).DecidesInTime L
      (fun n => (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (T n + 1) ^ 2) := by
  classical
  intro x
  obtain ⟨t, ht⟩ := dataTM_computes W M L a b T hW hT hM x
  have hcorrect : (obliviousCandidate W M a).ComputesInTime x
      [MultiTapeTM.indicator (L : Set (List Bool)) x] t :=
    parallelTM_computes (dataTM W M a) oblEmbed x [_] t ht
  obtain ⟨s, hs, hhalt⟩ := obliviousCandidate_halts W M a b T hW hT x
  have hbounded : (obliviousCandidate W M a).ComputesInTime x
      ((obliviousCandidate W M a).tm.runFrom ((obliviousCandidate W M a).tm.initCfg x) s).output s :=
    (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩
  rw [hbounded.output_unique hcorrect] at hbounded
  exact hbounded.mono hs

/-- **Oblivious simulation** — the first assertion of [AB09, Exercise 1.5], adapted
to this model: for time-constructible `T`, every language in `DTIME T` is decided by
an *oblivious* machine within `c · (T n + 1)²`. (The exercise's additional two-tape
normal form is not part of this statement.)

**Proof sketch** (corrected per the phase-2 audit, finding 2: the construction must
not invoke `one_work_tape_binary` per simulated step — that composes quadratics into
a quartic — must not run the constructibility witness verbatim, which need not be
oblivious, and must park the real input head). Take a decider for `L` within
`a · T n` and a constructibility witness within `b · (T n + 1)`.

1. Run the witness with every non-blank input symbol *read as `false`* (substituted
   in its transition table): its entire run — trajectories, emissions, halting time —
   then coincides with its run on the all-`false` input of length `n`, hence depends
   only on `n`, and it still computes `⌞T n⌟`; store the budget on a work tape.
2. Copy the real input to a work tape in one fixed scan and rewind (cost
   `O(n + 1)`, absorbed since `n ≤ T n`), then park the real input head for good.
3. Set `B n = (a + 1) · (T n + 1)` macrosteps and prepare a marked layout of size
   `O(B n)` holding the decider's work tapes, the virtual input copy, virtual head
   markers, and a step counter.
4. Each macrostep simulates one step of the decider by a fixed number of full sweeps
   of the layout — tape data affects writes, simulated state, and markers, never the
   sweep path or its duration — idling identically once the simulated machine halts,
   for exactly `B n` macrosteps (counter maintenance within the per-macrostep linear
   allowance; fixed-duration binary block coding throughout, so no appeal to the
   existential `alphabet_reduction` is needed to stay binary and oblivious).
5. Emit the stored answer bit at a fixed final time and halt.

Every head trajectory and the halting time are then functions of `n` and `t` alone,
and the total cost is `O(b · (T n + 1) + (B n)²) = O((T n + 1)²)`.

**Implementation notes — Epoch 3, Batch C.** The private construction above
provides the concrete binary simulator and its complete computation, trajectory,
and quadratic-time certificates. Logical alphabet codes are transverse fixed-width
binary blocks on synchronized tracks, so each logical transition costs one physical
transition. Virtual tapes are represented relative to their heads at the marked
origin; the two data sweeps implement virtual movement by shifting payloads. These
choices use the statement's unrestricted finite work-tape count.

The preparation invariant preserves the copied input through initialization. Its
first-macrostep clause is protected by the unique unary origin and the strictly
increasing macrostep counter. The operational forward and backward scan invariants
prove the source simulation, including blank writes, clamped input moves, and idle
steps after source halting. Exactly the prescribed budget is simulated, followed
by one answer emission. Determinism connects this complete output certificate to
the independent quadratic halting ledger, with constant
`18(a+1)^2 + 23(a+1) + 3b + 25`. -/
theorem oblivious_of_mem_DTIME {L : Language Bool} {T : ℕ → ℕ}
    (hT : TimeConstructible T) (hL : L ∈ DTIME T) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.Oblivious ∧ M.DecidesInTime L fun n => c * (T n + 1) ^ 2 := by
  classical
  rcases hT with ⟨hlinear, b, _, W, hW⟩
  rcases hL with ⟨a, M, hM⟩
  exact ⟨obliviousCandidate W M a, 18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25,
    obliviousCandidate_oblivious W M a, obliviousCandidate_decides W M L a b T hW hlinear hM⟩

end Complexity
