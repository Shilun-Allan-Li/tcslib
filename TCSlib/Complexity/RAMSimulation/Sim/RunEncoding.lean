/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Transporting the RAM encoding through the simulation host

The phase host changes the control-state type and places an instruction's eight tapes among
the start-up's tapes. The encoding depends only on the selected tapes, heads and output.
These lemmas transport it through those changes using the published layout equations.

## Main definitions

* `WordRAM.Sim.runBank`: select eight tapes and install an entry state, keeping the output.

## Main results

* `WordRAM.Sim.encodes_congr`: equal selected tapes, heads and output preserve the encoding.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9: simulation of random-access memory.)
-/

namespace WordRAM.Sim

open Turing

/-- Equal selected tapes, head positions and outputs give the same RAM encoding, even when
the configurations have different tape counts or control-state types. -/
theorem encodes_congr {K L : ℕ} {S H : Type} {x : List Bool} {W : ℕ}
    (a : ℕ) (fn : Bool) (T : Finset ℤ) (c : XCfg W)
    (σ : Fin 8 ↪ Fin K) (τ : Fin 8 ↪ Fin L) (o : Fin 8 → ℤ)
    (d : Turing.Cfg K Bool S x) (e : Turing.Cfg L Bool H x)
    (htapes : ∀ j, d.workTapes (σ j) = e.workTapes (τ j))
    (hheads : ∀ j, d.workTapePos (σ j) = e.workTapePos (τ j))
    (hout : d.output = e.output) :
    Encodes a fn T c σ o d ↔ Encodes a fn T c τ o e := by
  simp only [encodes_iff, keyTableAt_iff, tableAt_iff, wordAt_iff, htapes, hheads, hout]

/-- The selected eight-tape bank at entry `q`, with the ambient input head and output.
Unlike `Turing.Cfg.select`, this selection preserves output already emitted in function mode. -/
@[simps (config := { isSimp := false })]
def runBank {K : ℕ} {S H : Type} {x : List Bool} (σ : Fin 8 ↪ Fin K) (q : H)
    (d : Turing.Cfg K Bool S x) : Turing.Cfg 8 Bool H x where
  state := some q
  inputPos := d.inputPos
  workTapes := fun j => d.workTapes (σ j)
  workTapePos := fun j => d.workTapePos (σ j)
  output := d.output

/-- Selecting the eight tapes with `runBank` preserves the encoding, including the accumulated
function-mode output. The entry state has no effect on the encoding. -/
theorem runBank_encodes {K : ℕ} {S H : Type} {x : List Bool} {W : ℕ}
    (a : ℕ) (fn : Bool) (T : Finset ℤ) (c : XCfg W) (σ : Fin 8 ↪ Fin K)
    (o : Fin 8 → ℤ) (q : H) (d : Turing.Cfg K Bool S x) :
    Encodes a fn T c σ o d ↔
      Encodes a fn T c (Function.Embedding.refl _) o (runBank σ q d) :=
  encodes_congr a fn T c σ (Function.Embedding.refl _) o d (runBank σ q d)
    (fun _ => rfl) (fun _ => rfl) rfl

/-- Changing only the control-state labels preserves the encoding. -/
theorem encodes_mapState {K : ℕ} {S H : Type} {x : List Bool} {W : ℕ}
    (a : ℕ) (fn : Bool) (T : Finset ℤ) (c : XCfg W) (σ : Fin 8 ↪ Fin K)
    (o : Fin 8 → ℤ) (d : Turing.Cfg K Bool S x) (f : S → H) :
    Encodes a fn T c σ o d ↔ Encodes a fn T c σ o (d.mapState f) := by
  apply encodes_congr
  · intro j
    funext p
    rw [Cfg.mapState_workTapes]
  · intro j
    rw [Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output]

/-- Forwarding embedding into any ambient frame preserves the eight-tape encoding when the
output prefix is empty. Unselected tapes are unrestricted by the encoding. -/
theorem encodes_embed {K : ℕ} {S : Type} {x : List Bool} {W : ℕ}
    (a : ℕ) (fn : Bool) (T : Finset ℤ) (c : XCfg W) (σ : Fin 8 ↪ Fin K)
    (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x)
    (tapes : Fin K → ℤ → Option Bool) (heads : Fin K → ℤ) :
    Encodes a fn T c (Function.Embedding.refl _) o d ↔
      Encodes a fn T c σ o (embedEmitCfg σ tapes heads [] d) := by
  apply encodes_congr
  · intro j
    exact (embedEmitCfg_selected_tape σ tapes heads [] d j).symm
  · intro j
    exact (embedEmitCfg_selected_pos σ tapes heads [] d j).symm
  · rw [embedEmitCfg_output, List.nil_append]

/-- Re-embedding the selected bank and tagging its entry reconstructs a live ambient
configuration whose control already has that tag. -/
theorem runBank_reconstruct {K : ℕ} {S H : Type} {x : List Bool}
    (σ : Fin 8 ↪ Fin K) (q : S) (f : S → H) (d : Turing.Cfg K Bool H x)
    (hd : d.state = some (f q)) :
    (embedEmitCfg σ d.workTapes d.workTapePos [] (runBank σ q d)).mapState f = d := by
  apply embedEmitCfg_mapState_eq
  · rw [runBank_state, Option.map_some, hd]
  · exact runBank_inputPos σ q d
  · rw [runBank_output, List.nil_append]
  · intro j
    exact ⟨rfl, rfl⟩
  · intro j _
    exact ⟨rfl, rfl⟩

/-- Re-embedding the selected bank in the same state type reconstructs an ambient
configuration at that bank's entry, without changing its state type. -/
theorem runBank_embed {K : ℕ} {S : Type} {x : List Bool}
    (σ : Fin 8 ↪ Fin K) (q : S) (d : Turing.Cfg K Bool S x)
    (hd : d.state = some q) :
    embedEmitCfg σ d.workTapes d.workTapePos [] (runBank σ q d) = d := by
  apply embedEmitCfg_eq
  · rw [runBank_state, hd]
  · exact runBank_inputPos σ q d
  · rw [runBank_output, List.nil_append]
  · intro j
    exact ⟨rfl, rfl⟩
  · intro j _
    exact ⟨rfl, rfl⟩

/-- Replacing a live control by an entry and then restoring its known tag reconstructs the
whole configuration. The published state-renaming field equations preserve all other fields. -/
theorem runEntry_reconstruct {K : ℕ} {S H : Type} {x : List Bool}
    (q : S) (f : S → H) (d : Turing.Cfg K Bool H x) (hd : d.state = some (f q)) :
    (d.mapState (fun _ => q)).mapState f = d := by
  apply Turing.Cfg.ext
  · rw [Cfg.mapState_state, Cfg.mapState_state, hd, Option.map_some, Option.map_some]
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j p
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

end WordRAM.Sim
