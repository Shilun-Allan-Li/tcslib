/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCore
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framing and placement of instruction rows

The word and keyed-table rows run on five selected tapes. Their native endpoints preserve all
other data. These lemmas read the tape predicates through their published characterizations
and place the bounded runs on the simulation's eight tapes.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_wordAt_congr`: word layout depends only on the selected tape and head.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A word layout is unchanged when its tape and head are unchanged, regardless of control,
input head and output. -/
theorem phase_wordAt_congr {K : ℕ} {S S' : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (e : Turing.Cfg K Bool S' x) (r : Fin K) (w : List Bool)
    (ht : d.workTapes r = e.workTapes r) (hp : d.workTapePos r = e.workTapePos r) :
    WordAt d r w ↔ WordAt e r w := by
  rw [wordAt_iff, wordAt_iff, ht, hp]

/-- A keyed-table layout depends only on its physical tape, including the blank right tail. -/
theorem phase_keyTableAt_congr {K : ℕ} {S S' : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (e : Turing.Cfg K Bool S' x) (r : Fin K) (o : ℤ)
    (es : List (List Bool × List Bool)) (ht : d.workTapes r = e.workTapes r) :
    KeyTableAt d r o es ↔ KeyTableAt e r o es := by
  rw [keyTableAt_iff, keyTableAt_iff, tableAt_iff, tableAt_iff, ht]

/-- Encoding depends on the memory and output of the RAM configuration and the work tapes,
work heads and output of the Turing configuration, independently of both controls and the input
head. -/
theorem phase_encodes_congr {K a W : ℕ} {S S' : Type} {x : List Bool} (fn : Bool)
    (T : Finset ℤ) (c c' : XCfg W) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ)
    (d : Turing.Cfg K Bool S x) (e : Turing.Cfg K Bool S' x)
    (ht : d.workTapes = e.workTapes) (hp : d.workTapePos = e.workTapePos)
    (ho : d.output = e.output) (hm : c.mem = c'.mem) (hc : c.out = c'.out) :
    Encodes a fn T c σ o d ↔ Encodes a fn T c' σ o e := by
  simp only [encodes_iff, keyTableAt_iff, tableAt_iff, wordAt_iff, ht, hp, ho, hm, hc]

/-- Placing a bounded source run on selected tapes preserves its time and radius bounds and
frames every unselected tape. The source starts at the host's selection, with empty output.

**Proof sketch.** `embedEmitCfg_select` identifies the host start. The lockstep
`embedEmitTM_runFrom` then transfers the run and cut; selected head positions are the source's
by `embedEmitCfg_selected_pos`, and the other heads stay fixed by
`embedEmitCfg_unselected`. -/
theorem phase_reaches_embed {m : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin 8) (M : MultiTapeTM m Bool S) (d : Turing.Cfg 8 Bool S x)
    (X : Set (Option S)) (B E : ℕ) (post : Turing.Cfg m Bool S x)
    (h : ReachesWithin M (d.select σ) X B E post) :
    ReachesWithin (embedEmitTM σ M) d X B E
      (embedEmitCfg σ d.workTapes d.workTapePos d.output post) := by
  obtain ⟨t, ht, hcut, henv, hrun⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h
  have transport (s : ℕ) : (embedEmitTM σ M).runFrom d s =
      embedEmitCfg σ d.workTapes d.workTapePos d.output (M.runFrom (d.select σ) s) := by
    have hh := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) s
    rwa [embedEmitCfg_select] at hh
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro s hs
    rw [transport, embedEmitCfg_state]
    exact hcut s hs
  · intro s hs j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨r, rfl⟩ := hj
      rw [transport, embedEmitCfg_selected_pos]
      simpa only [Cfg.select_eq] using henv s hs r
    · rw [transport, (embedEmitCfg_unselected σ d.workTapes d.workTapePos d.output
        (M.runFrom (d.select σ) s) j hj).2, sub_self, abs_zero]
      exact Int.natCast_nonneg E
  · rw [transport, hrun]

/-- Rewriting a delimited word with another word of the same length preserves its delimiters
and establishes the new word layout.

**Proof sketch.** Read `wordWrite_apply` inside the word interval and `wordAt_iff` at its
unchanged boundaries. Off the interval, the allowed offsets are just `-1` and the word length;
`bufferTape_left` and `bufferTape_nat` identify both boundary cells as blank. -/
theorem phase_wordAt_write {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (r : Fin K) (w v : List Bool)
    (hw : WordAt d r w) (hv : v.length = w.length) :
    WordAt { d with workTapes := wordWrite d r v } r v := by
  apply (wordAt_iff _ r v).mpr
  intro p hp hp'
  change wordWrite d r v r (d.workTapePos r + p) = FinTM.bufferTape v p
  rw [wordWrite_apply]
  by_cases h : 0 ≤ p ∧ p < (v.length : ℤ)
  · rw [if_pos ⟨rfl, by omega, by omega⟩, add_sub_cancel_left]
  · rw [if_neg (by omega), (wordAt_iff d r w).mp hw p hp (by omega)]
    have hb : p = -1 ∨ p = (v.length : ℤ) := by omega
    rcases hb with rfl | rfl
    · rw [FinTM.bufferTape_left, FinTM.bufferTape_left]
    · rw [FinTM.bufferTape_nat, FinTM.bufferTape_nat,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- A simultaneous control/input-head update and replacement of one selected tape commutes
with forwarding embedding; all unselected tapes remain the host frame.

**Proof sketch.** Apply `embedEmitCfg_eq`. Selection preserves each selected tape and head by
`Cfg.select_eq`; the update at a selected index agrees by injectivity of the tape embedding.
At every unselected index the update is absent, by `Function.update_of_ne`. -/
theorem phase_embed_update {m : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin 8) (d : Turing.Cfg 8 Bool S x) (q : Option S)
    (ip : Fin (x.length + 2)) (r : Fin m) (u : ℤ → Option Bool) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output
      { (d.select σ) with
        state := q
        inputPos := ip
        workTapes := Function.update (d.select σ).workTapes r u } =
      { d with state := q, inputPos := ip, workTapes := Function.update d.workTapes (σ r) u } := by
  apply embedEmitCfg_eq
  · rfl
  · rfl
  · simp only [Cfg.select_eq, List.append_nil]
  · intro i
    constructor
    · change Function.update (d.select σ).workTapes r u i =
        Function.update d.workTapes (σ r) u (σ i)
      rw [Function.update_apply, Function.update_apply]
      simp only [σ.injective.eq_iff, Cfg.select_eq]
    · simp only [Cfg.select_eq]
  · intro j hj
    have hne : j ≠ σ r := fun h => hj ⟨r, h.symm⟩
    exact ⟨(Function.update_of_ne hne u d.workTapes).symm, rfl⟩

/-! ## Single-tape replacement -/

/-- A conditional patch confined to one tape is a function update of that tape. -/
private theorem phase_single_tape_update {K : ℕ} (tapes : Fin K → ℤ → Option Bool)
    (r : Fin K) (p : Fin K → ℤ → Prop) [∀ j q, Decidable (p j q)]
    (v : Fin K → ℤ → Option Bool) :
    (fun j q => if j = r ∧ p j q then v j q else tapes j q) =
      Function.update tapes r (fun q => if p r q then v r q else tapes r q) := by
  funext j q
  rw [Function.update_apply]
  by_cases hj : j = r
  · subst j
    simp only [if_true, true_and]
  · simp only [hj, false_and, if_false]

/-- A word write is replacement of just its destination tape; the replacement keeps that
tape's outer frame and writes the new word over its length. -/
theorem phase_wordWrite_as_update {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (r : Fin K) (w : List Bool) :
    wordWrite d r w = Function.update d.workTapes r (fun q =>
      if d.workTapePos r ≤ q ∧ q < d.workTapePos r + (w.length : ℤ)
      then FinTM.bufferTape w (q - d.workTapePos r) else d.workTapes r q) := by
  exact (funext fun j => funext fun q => wordWrite_apply d r w j q).trans
    (phase_single_tape_update d.workTapes r
      (fun j q => d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ))
      (fun j q => FinTM.bufferTape w (q - d.workTapePos j)))

/-- A word on a selected source tape is exactly the word on its corresponding host tape. -/
theorem phase_wordAt_select {m : ℕ} {S : Type} {x : List Bool} (σ : Fin m ↪ Fin 8)
    (d : Turing.Cfg 8 Bool S x) (r : Fin m) (w : List Bool) :
    WordAt (d.select σ) r w ↔ WordAt d (σ r) w := by
  simp only [wordAt_iff, Cfg.select_eq]

/-- A keyed table on a selected source tape is exactly that table on the corresponding host
tape, with the same origin and blank tail. -/
theorem phase_keyTableAt_select {m : ℕ} {S : Type} {x : List Bool} (σ : Fin m ↪ Fin 8)
    (d : Turing.Cfg 8 Bool S x) (r : Fin m) (o : ℤ) (es : List (List Bool × List Bool)) :
    KeyTableAt (d.select σ) r o es ↔ KeyTableAt d (σ r) o es := by
  simp only [keyTableAt_iff, tableAt_iff, Cfg.select_eq]

/-- A native word-write endpoint embeds as the same word write on the corresponding host
tape, with its state and input-head updates preserved. -/
theorem phase_embed_wordWrite {m : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin 8) (d : Turing.Cfg 8 Bool S x) (q : Option S)
    (ip : Fin (x.length + 2)) (r : Fin m) (w : List Bool) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output
      { (d.select σ) with
        state := q
        inputPos := ip
        workTapes := wordWrite (d.select σ) r w } =
      { d with state := q, inputPos := ip, workTapes := wordWrite d (σ r) w } := by
  simpa only [phase_wordWrite_as_update, Cfg.select_eq] using
    phase_embed_update σ d q ip r (fun z =>
      if d.workTapePos (σ r) ≤ z ∧ z < d.workTapePos (σ r) + (w.length : ℤ)
      then FinTM.bufferTape w (z - d.workTapePos (σ r)) else d.workTapes (σ r) z)

/-- A keyed-table write is replacement of its single destination tape, retaining that tape's
outer frame beyond the written layout. -/
theorem phase_keyTableWrite_as_update {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (r : Fin K) (o : ℤ) (es : List (List Bool × List Bool)) :
    keyTableWrite d r o es = Function.update d.workTapes r (fun q =>
      if o ≤ q ∧ q < o + (keyTableLength es : ℤ)
      then fieldsTape (tableFields [true] (keyFields es)) (q - o) else d.workTapes r q) :=
  (funext fun j => funext fun q => keyTableWrite_apply d r o es j q).trans
    (phase_single_tape_update d.workTapes r
      (fun _ q => o ≤ q ∧ q < o + (keyTableLength es : ℤ))
      (fun _ q => fieldsTape (tableFields [true] (keyFields es)) (q - o)))

/-- A native keyed-table write embeds as the same layout write on its corresponding host tape,
with its state and input-head updates preserved. -/
theorem phase_embed_keyTableWrite {m : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin 8) (d : Turing.Cfg 8 Bool S x) (q : Option S)
    (ip : Fin (x.length + 2)) (r : Fin m) (o : ℤ) (es : List (List Bool × List Bool)) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output
      { (d.select σ) with
        state := q
        inputPos := ip
        workTapes := keyTableWrite (d.select σ) r o es } =
      { d with state := q, inputPos := ip, workTapes := keyTableWrite d (σ r) o es } := by
  simpa only [phase_keyTableWrite_as_update, Cfg.select_eq] using
    phase_embed_update σ d q ip r (fun z =>
      if o ≤ z ∧ z < o + (keyTableLength es : ℤ)
      then fieldsTape (tableFields [true] (keyFields es)) (z - o) else d.workTapes (σ r) z)

end WordRAM.Sim
