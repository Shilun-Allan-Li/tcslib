/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State renaming

Raw-layer transport of actions, configurations, and machines along maps of the
state type. This is the generic component shared by the oracle embedding
(`TCSlib.Complexity.TuringMachine.Oracle`, which renames states into
`State ⊕ Fin 3`) and the code normal form
(`TCSlib.Complexity.TuringMachine.Encoding`, which relabels states into
`Fin (numStates + 1)`), factored out per the epoch-1 audit (finding 5).

## Design

* `Turing.Action.mapState` and `Turing.Cfg.mapState` take an **arbitrary
  function** of the state types: mapping an action or configuration needs no
  injectivity, and the application lemma `Turing.Cfg.mapState_apply` holds for
  any function.
* `Turing.MultiTapeTM.relabelState` takes an **equivalence**: renaming a whole
  transition table along a non-injective map is not well defined (two states
  identified by the map may disagree on their transitions — epoch-1 audit,
  finding 5), and the inverse is used to read the table.
* The run-correspondence lemma is deliberately an **initialized-run** statement
  (`Turing.MultiTapeTM.relabelState_runFrom_init`), as the epoch-1 audit
  specified; an arbitrary-starting-configuration version can be added, with its
  own checked statement, if a result needs it.
* No finiteness assumptions anywhere: this is the raw parametric layer.

## Main definitions

* `Turing.Action.mapState` — rename an action's optional successor state
  (moved here from the oracle module; the definition is unchanged).
* `Turing.Cfg.mapState` — rename a configuration's optional state.
* `Turing.MultiTapeTM.relabelState` — transport a machine along a state
  equivalence.

## Main results

* `Turing.Cfg.mapState_apply` — renaming commutes with applying an action.
* `Turing.MultiTapeTM.relabelState_step` — renaming commutes with one step,
  including the absorbing halted case.
* `Turing.MultiTapeTM.relabelState_runFrom_init` — initialized runs correspond
  at every time.
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

/-- Rename the states of an action along a function. -/
def Action.mapState {State' : Type*} (f : State → State') (a : Action k Symbol State) :
    Action k Symbol State' where
  inputTape := a.inputTape
  workTapes := a.workTapes
  output := a.output
  state := a.state.map f

/-- Rename a configuration's optional state along a function, preserving the
input position, work tapes, head positions, and output. -/
def Cfg.mapState {State' : Type*} {input : List Symbol} (f : State → State')
    (cfg : Cfg k Symbol State input) : Cfg k Symbol State' input :=
  { cfg with state := cfg.state.map f }

/-- State renaming commutes with applying an action (any function; no
injectivity needed, since the action is supplied explicitly). -/
lemma Cfg.mapState_apply {State' : Type*} {input : List Symbol} (f : State → State')
    (a : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    (a.mapState f).apply (cfg.mapState f) = (a.apply cfg).mapState f := rfl

/-- Transport a machine along a state **equivalence**: the initial state is
mapped forward, and each transition reads the table through the inverse. An
arbitrary function would not suffice here — identifying two states with
different transitions leaves no well-defined table (epoch-1 audit, finding 5). -/
def MultiTapeTM.relabelState {State' : Type*} (tm : MultiTapeTM k Symbol State)
    (e : State ≃ State') : MultiTapeTM k Symbol State' where
  q₀ := e tm.q₀
  tr := fun q inp ws => (tm.tr (e.symm q) inp ws).mapState e

/-- Relabeling commutes with each step, including the absorbing halted case. -/
lemma MultiTapeTM.relabelState_step {State' : Type*} {input : List Symbol}
    (tm : MultiTapeTM k Symbol State) (e : State ≃ State')
    (cfg : Cfg k Symbol State input) :
    (tm.relabelState e).step (cfg.mapState e) = (tm.step cfg).mapState e := by
  have hin : (cfg.mapState e).inputSymbol = cfg.inputSymbol := rfl
  have hwork : (cfg.mapState e).workTapeSymbols = cfg.workTapeSymbols := rfl
  unfold MultiTapeTM.step
  cases hs : cfg.state with
  | none => simp [Cfg.mapState, hs]
  | some q =>
    rw [show (cfg.mapState e).state = some (e q) by
      simp only [Cfg.mapState, hs, Option.map_some]]
    dsimp only
    rw [hin, hwork]
    simp only [MultiTapeTM.relabelState, Equiv.symm_apply_apply]
    exact Cfg.mapState_apply e _ cfg

/-- Initialized runs correspond at every time. This is deliberately an
initialized-run lemma (epoch-1 audit, finding 5); an arbitrary-start version
would be a separate statement. -/
lemma MultiTapeTM.relabelState_runFrom_init {State' : Type*}
    (tm : MultiTapeTM k Symbol State) (e : State ≃ State') (input : List Symbol)
    (t : ℕ) :
    (tm.relabelState e).runFrom ((tm.relabelState e).initCfg input) t =
      (tm.runFrom (tm.initCfg input) t).mapState e :=
  MultiTapeTM.runFrom_comm_of_step (Cfg.mapState e)
    (tm.relabelState_step e) (tm.initCfg input) t

end Turing
