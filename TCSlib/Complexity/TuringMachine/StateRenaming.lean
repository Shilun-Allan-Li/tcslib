/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.Simulation

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
* `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` — injective state transport
  followed by guarded agreement on the host carrier (moved from `Build/Embed` at
  MIG-0b's layering split, 2026-10-13, so that the contract core can rename states;
  hence the import of `Simulation`, for `AgreeOn`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2 — the machine model whose state
  spaces are transported here; the module itself is internal infrastructure
  with no direct textbook counterpart.)
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

namespace Turing

variable {Symbol : Type*}

/-! ## Guarded state transport (moved from `Build/Embed` at MIG-0b's layering split) -/

/-- An injectively renamed source run agrees with a host run through any
prefix whose live source controls satisfy `good`, provided both transition
tables agree on the renamed good states for every input and work-tape read.
**Proof sketch.** Extend the renamed source table to the entire host carrier.
Step commutation identifies its run, then same-carrier guarded agreement
transfers that run to the host on the image of the good source states. -/
theorem MultiTapeTM.runFrom_mapState_of_agreeOn {k : ℕ} {S H : Type} {x : List Symbol}
    (src : MultiTapeTM k Symbol S) (host : MultiTapeTM k Symbol H)
    (emb : S ↪ H) (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work,
      host.tr (emb q) inp work = (src.tr q inp work).mapState emb)
    (c : Cfg k Symbol S x) (t : ℕ)
    (hguard : ∀ u < t, ∀ q, (src.runFrom c u).state = some q → good q) :
    host.runFrom (c.mapState emb) t = (src.runFrom c t).mapState emb := by
  classical
  letI : Nonempty S := ⟨src.q₀⟩
  let reference : MultiTapeTM k Symbol H :=
    ⟨emb src.q₀, fun q inp work => (src.tr (Function.invFun emb q) inp work).mapState emb⟩
  have step (d : Cfg k Symbol S x) :
      reference.step (d.mapState emb) = (src.step d).mapState emb := by
    cases hs : d.state with
    | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
    | some q =>
      simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
      change (reference.tr (emb q) d.inputSymbol d.workTapeSymbols).apply (d.mapState emb) = _
      dsimp only [reference]
      rw [Function.leftInverse_invFun emb.injective q]
      exact Cfg.mapState_apply emb _ d
  have transport (u : ℕ) :
      reference.runFrom (c.mapState emb) u = (src.runFrom c u).mapState emb :=
    MultiTapeTM.runFrom_comm_of_step (fun d => d.mapState emb) step c u
  have agreement : reference.AgreeOn host {q | ∃ p, good p ∧ emb p = q} := by
    intro q hq inp work
    obtain ⟨p, hp, rfl⟩ := hq
    dsimp only [reference]
    rw [Function.leftInverse_invFun emb.injective p]
    exact (hagree p hp inp work).symm
  rw [MultiTapeTM.runFrom_eq_of_agreeOn agreement]
  · exact transport t
  · intro u hu q hq
    rw [transport u] at hq
    change ((src.runFrom c u).state.map emb) = some q at hq
    obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hq
    exact ⟨p, hguard u hu p hp, he⟩

end Turing
