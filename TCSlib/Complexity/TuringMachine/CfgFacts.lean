/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Elementary facts about configurations

Four small facts that machine constructions over several phases use repeatedly: the input read
depends on the input head only; a live configuration redirected to a state of phase `i` is the
tagged configuration of phase `i`; a configuration tagged by one phase is never at a state of
another; and a list of equal-length chunks has the expected length.

## Main definitions

No new definitions.

## Main results

* `Turing.Cfg.inputSymbol_congr` — configurations whose input heads agree read the same input
  symbol, across machines.
* `Turing.Cfg.mapState_const_eq_mapState_sigma` — redirecting a live configuration to `⟨i, q⟩`
  gives phase `i`'s tagged configuration at `q`.
* `Turing.Cfg.mapState_sigma_state_ne` — a configuration tagged by phase `i` is at no state of
  another phase.
* `Turing.length_flatMap_const` — a list of equal-length chunks has length count × chunk length.
-/

namespace Turing

/-- **The input read depends on the input head only.** Two configurations on the same input,
of machines with any numbers of work tapes and any states, read the same input symbol when their
input heads are at the same position.

**Proof sketch.** At position `0` and at `|input| + 1` both read blank
(`Turing.Cfg.inputSymbol_of_zero`, `Turing.Cfg.inputSymbol_of_end`); at an inner position `1 + p`
both read `input[p]` (`Turing.inputSymbolInner`). -/
theorem Cfg.inputSymbol_congr {Symbol : Type*} {k k' : ℕ} {S S' : Type*} {input : List Symbol}
    (c : Cfg k Symbol S input) (c' : Cfg k' Symbol S' input)
    (h : c.inputPos.val = c'.inputPos.val) : c.inputSymbol = c'.inputSymbol := by
  by_cases h0 : c.inputPos.val = 0
  · have h0' : c'.inputPos = 0 := Fin.ext (by rw [← h]; exact h0)
    rw [Cfg.inputSymbol_of_zero (Fin.ext h0), Cfg.inputSymbol_of_zero h0']
  · by_cases he : c.inputPos.val = input.length + 1
    · rw [Cfg.inputSymbol_of_end he, Cfg.inputSymbol_of_end (by omega)]
    · have hlt := c.inputPos.isLt
      rw [inputSymbolInner (c.inputPos.val - 1) (by omega) (by omega),
        inputSymbolInner (cfg := c') (c.inputPos.val - 1) (by omega) (by omega)]

/-- **Redirecting a live configuration to a phase's state.** If `c` is live and `c₂` is a
configuration of phase `i` at state `q` with `c`'s tapes, heads and output, then sending every
state of `c` to `⟨i, q⟩` gives `c₂` tagged by `i`.

**Proof sketch.** Compare the five fields through the state-renaming equations
(`Turing.Cfg.mapState_state` and the others): the states are both `some ⟨i, q⟩` since `c` is
live, and the remaining fields are the hypotheses. -/
theorem Cfg.mapState_const_eq_mapState_sigma {k : ℕ} {Γ I S : Type*} {Ph : I → Type*}
    {x : List Γ} {i : I} (c : Cfg k Γ S x) (c₂ : Cfg k Γ (Ph i) x) {q : Ph i}
    (hc : c.state.isSome) (hstate : c₂.state = some q) (hin : c.inputPos = c₂.inputPos)
    (hw : c.workTapes = c₂.workTapes) (hp : c.workTapePos = c₂.workTapePos)
    (ho : c.output = c₂.output) :
    c.mapState (fun _ => (⟨i, q⟩ : Σ j, Ph j)) = c₂.mapState (Sigma.mk i) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hc
  apply Cfg.ext
  · rw [Cfg.mapState_state, Cfg.mapState_state, hs, hstate, Option.map_some, Option.map_some]
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, hin]
  · funext j p; rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, hw]
  · funext j; rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, hp]
  · rw [Cfg.mapState_output, Cfg.mapState_output, ho]

/-- **A tagged configuration is at no other phase's state.** A configuration tagged by phase `i`
(its states sent into the sum by `Sigma.mk i`) is never at a state `v` of a phase `v.1 ≠ i`. -/
theorem Cfg.mapState_sigma_state_ne {k : ℕ} {Γ I : Type*} {Ph : I → Type*} {x : List Γ}
    (i : I) (v : Σ j, Ph j) (hi : i ≠ v.1) (c : Cfg k Γ (Ph i) x) :
    (c.mapState (Sigma.mk i)).state ≠ some v := by
  rw [Cfg.mapState_state]
  cases hs : c.state with
  | none => exact Option.noConfusion
  | some s =>
    intro h
    exact hi (congrArg Sigma.fst (Option.some.inj h))

/-- **Equal-length chunks.** If every chunk `f a` has length `c`, the concatenation of the chunks
of a list `l` has length `|l| · c`. -/
theorem length_flatMap_const {α β : Type*} (l : List α) (f : α → List β) {c : ℕ}
    (hf : ∀ a, (f a).length = c) : (l.flatMap f).length = l.length * c := by
  rw [List.length_flatMap, List.map_congr_left (fun a _ => hf a), List.map_const',
    List.sum_replicate]
  rfl

end Turing
