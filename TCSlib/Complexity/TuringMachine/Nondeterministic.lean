/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic Multi-Tape Turing Machines

[AB09, §2.1.2]: a nondeterministic Turing machine (NDTM) is a standard TM with **two**
transition functions `δ₀` and `δ₁`; at every step the machine chooses which of the two to
apply. A finite run is therefore governed by a *choice word* — one bit per step — and the
run function is indexed by it. This module defines the raw machine, its choice-word
semantics in the style of the deterministic `Turing.MultiTapeTM.runFrom`, the all-branch
halting predicate that time bounds quantify over, the bundled finite layer `FinNDTM`, and
the embedding of deterministic machines. Acceptance and the class `NTIME` live one layer
up, in `TCSlib.Complexity.ClassNP.NTIME`, because they fix the binary alphabet. The last
section is the run-level layer of the nondeterministic contract variant (C1): runs along
state embeddings, the slice lemma, state relabelling and input locality.

## Design and deviations from [AB09]

* **Two total transition functions, `Bool`-indexed**: the single field
  `tr : Bool → …` carries [AB09]'s `δ₀` as `tr false` and `δ₁` as `tr true`. Both
  functions are total, so no configuration is ever *stuck* — every choice word of every
  length drives a complete run. (This is the load-bearing difference from a
  relational model such as cslib's `MultiTapeNTM`, surveyed and deliberately not
  ported — see the plan's decision log: with binary choice the accepting choice word
  *is* the polynomial-length certificate of [AB09, Theorem 2.6], while arbitrary
  branching relations have no canonical certificate encoding.)
* **Choice words are finite lists** (`List Bool`), consumed left to right, one bit per
  step: `runWith w cfg` is the configuration after `|w|` steps under the choices `w`.
  The alternative — infinite choice streams `ℕ → Bool` with a separate step count — is
  equivalent for every notion built here (only the first `t` bits of a stream are ever
  consulted); the list form makes the choice word a finite string that can be a
  certificate. **Design question (c) for the phase-2 audit.**
* **No `q_accept` state.** [AB09] equips NDTMs with a distinguished accepting state;
  our machines signal through their output tape, exactly as the deterministic
  development does (`Turing.FinTM.DecidesInTime` reads acceptance off the output
  `[true]`/`[false]`). Acceptance-by-output is defined in
  `TCSlib.Complexity.ClassNP.NTIME` and is **design question (a) for the phase-2
  audit**.
* **Halting is absorbing under every choice**: stepping a halted configuration is the
  identity regardless of the choice bit, mirroring the deterministic `step`. Extending
  a choice word beyond the halting time therefore never changes the reached
  configuration — the lemma `runWith_of_halt` below. This is what the exact-length
  quantifiers lean on, *directionally*: accepting witnesses pad to any larger exact
  length, and all-branch halting at a larger budget follows by splitting at the old
  one (`HaltsWithin.mono`). It does **not** make every bounded-length rewriting valid —
  "every word of length at most `t` is halted" already fails at the empty word — and
  the correct bounded readings are recorded in `TCSlib.Complexity.ClassNP.NTIME`
  (round-1 audit, finding 2).
* The model reuses the vendored configuration layer (`Turing.Cfg`, `Turing.Action`)
  unchanged: an NDTM step applies an `Action` exactly as a deterministic step does; only
  the *selection* of the action is new.

## Main definitions

* `Turing.NDTM` — the binary-choice nondeterministic machine. [AB09, §2.1.2]
* `Turing.NDTM.stepWith`, `Turing.NDTM.runWith` — one step under a choice bit; the run
  under a choice word. [AB09, §2.1.2]
* `Turing.NDTM.HaltsWithin` — every choice word of length `t` halts the machine on the
  given input; the totality condition of [AB09]'s "runs in `T(n)` time".
* `Turing.NDTM.fixChoice` — the deterministic slice at a fixed choice bit, with
  `Turing.NDTM.stepWith_eq_fixChoice_step` (added 2026-10-10).
* `Turing.FinNDTM` — the bundled finite layer, mirroring `Turing.FinTM`.
* `Turing.MultiTapeTM.toNDTM`, `Turing.FinTM.toFinNDTM` — a deterministic machine as an
  NDTM whose two transition functions coincide.
* `Turing.NDTM.relabelState` — state relabelling of an NDTM along an equivalence, mirroring
  `Turing.MultiTapeTM.relabelState` (C1).

## Main results

* `Turing.NDTM.runWith_eq_fixChoice_runFrom` — a branch that meets no real choice is the run of
  the deterministic slice (stage 2's slice lemma; statement gated 2026-10-14; proved, by the
  agreement transfer at the identity embedding, C1).
* `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt` — the choice-word run
  algebra (proved; pure unfoldings, the nondeterministic counterparts of the vendored
  `runFrom` lemmas).
* `Turing.NDTM.HaltsWithin.mono` — all-branch halting is monotone in the time bound.
* `Turing.MultiTapeTM.toNDTM_runWith` — the embedded deterministic machine ignores its
  choices: every choice word of length `t` reproduces `runFrom` at time `t`.
* `Turing.NDTM.runWith_mapState_of_agreeOn`, `Turing.NDTM.runWith_mapState_of_agreeOn_det` —
  the agreement transfer: a host whose transition functions agree with a nondeterministic or a
  deterministic source along a state embedding, at the states visited, runs as the source
  renamed (with the one-step form `Turing.NDTM.stepWith_mapState_of_agreeOn`; proved, C1).
* `Turing.NDTM.relabelState_runWith` — relabelled branches are the renamed branches (proved).
* `Turing.NDTM.runWith_initCfg_take` — input locality: a branch of at most `m` steps reads only
  the first `m` input symbols (proved, C1).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.4; §2.1.2, pp. 41-42.)
* cslib (https://github.com/leanprover/cslib), `MultiTape/Nondeterministic.lean` at
  commit a3747758: a relational nondeterministic model (related work, not ported — see
  `AroraBarakChapter2Plan.md`, decision log).
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A binary-choice nondeterministic multi-tape Turing machine [AB09, §2.1.2]: a
machine with **two** total transition functions, carried as the `Bool`-indexed field
`tr` — `tr false` is [AB09]'s `δ₀` and `tr true` is `δ₁`. Tapes, actions, and
configurations are exactly those of the deterministic `Turing.MultiTapeTM`; as there,
`Symbol` and `State` need not be finite at this layer (the bundled finite layer is
`Turing.FinNDTM` below). -/
structure NDTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- the two transition functions, indexed by the nondeterministic choice: `tr false`
  is `δ₀`, `tr true` is `δ₁`; each maps the state, input symbol, and work-head symbols
  to an action, exactly as the deterministic transition function does -/
  tr (choice : Bool) (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace NDTM

variable {input : List Symbol} {tm : NDTM k Symbol State}

/-- One step under the choice bit `b`: apply the action selected by transition function
`tr b`, or stay put when already halted. Halting is absorbing under **every** choice —
the halted branch does not consult `b` — mirroring `Turing.MultiTapeTM.step`. -/
def stepWith (b : Bool) (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tm.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration corresponding to an input string — identical to the
deterministic initialization (blank work tapes, input head on the first symbol). -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

/-- The configuration reached from `cfg` by running under the choice word `w`, one
choice bit per step, consumed left to right: `|w|` steps in total. This is the
nondeterministic counterpart of `Turing.MultiTapeTM.runFrom`; a "branch" of the
computation tree of [AB09, §2.1.2] is the run under one choice word. -/
def runWith : List Bool → Cfg k Symbol State input → Cfg k Symbol State input
  | [], cfg => cfg
  | b :: w, cfg => runWith w (tm.stepWith b cfg)

/-- The empty choice word runs zero steps. -/
@[simp]
lemma runWith_nil {cfg : Cfg k Symbol State input} : tm.runWith [] cfg = cfg := rfl

/-- Consuming one choice bit is one step: the run under `b :: w` is the run under `w`
from the configuration one `stepWith b` ahead. -/
lemma runWith_cons {b : Bool} {w : List Bool} {cfg : Cfg k Symbol State input} :
    tm.runWith (b :: w) cfg = tm.runWith w (tm.stepWith b cfg) := rfl

/-- Running under `w ++ w'` is running under `w`, then under `w'` from the reached
configuration — the counterpart of `Turing.MultiTapeTM.runFrom_add`. -/
lemma runWith_append (w w' : List Bool) (cfg : Cfg k Symbol State input) :
    tm.runWith (w ++ w') cfg = tm.runWith w' (tm.runWith w cfg) := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih => rw [List.cons_append, runWith_cons, runWith_cons, ih]

/-- The deterministic slice of a nondeterministic machine at a fixed choice bit: the
multi-tape machine that always uses the transition function `tm.tr b`. [AB09, §2.1.2: an
NDTM has two transition functions, and a choice bit selects one] (Shared by the
configuration-graph layer; added 2026-10-10.) -/
def fixChoice (tm : NDTM k Symbol State) (b : Bool) : MultiTapeTM k Symbol State :=
  ⟨tm.q₀, tm.tr b⟩

/-- One nondeterministic step under the choice bit `b` is one step of the slice at `b`.

**Proof sketch.** Both steps fix a halted configuration, and otherwise apply the action
that `tm.tr b` reads from the same configuration (`cases` on the state). -/
theorem stepWith_eq_fixChoice_step (tm : NDTM k Symbol State) (b : Bool)
    (cfg : Cfg k Symbol State input) : tm.stepWith b cfg = (tm.fixChoice b).step cfg := by
  cases h : cfg.state <;> simp only [NDTM.stepWith, MultiTapeTM.step, fixChoice, h]

/-- Stepping a halted configuration is the identity, under either choice. -/
@[simp]
lemma stepWith_of_halt {b : Bool} {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.stepWith b cfg = cfg := by
  unfold stepWith
  rw [h]

/-- Running from a halted configuration stays there, under **every** choice word — the
counterpart of `Turing.MultiTapeTM.runFrom_of_halt`. Extending a choice word beyond the
halting time therefore never changes the reached configuration. -/
@[simp]
lemma runWith_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none)
    {w : List Bool} : tm.runWith w cfg = cfg := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, stepWith_of_halt h]; exact ih

/-- The machine halts on `input` within `t` steps **along every branch**: after any `t`
nondeterministic choices the configuration is halted. This is the totality condition in
[AB09]'s "runs in `T(n)` time" (§2.1.2: *every* sequence of choices reaches the halting
state within the bound), rendered over choice words of length exactly `t`; by
`Turing.NDTM.runWith_of_halt` the exact-length quantifier already covers all longer
words, and `Turing.NDTM.HaltsWithin.mono` makes this precise. -/
def HaltsWithin (tm : NDTM k Symbol State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ w : List Bool, w.length = t → (tm.runWith w (tm.initCfg input)).state = none

/-- All-branch halting is monotone in the time bound.

**Proof sketch.** Given `w` with `|w| = t' ≥ t`, split `w = w.take t ++ w.drop t`
(`List.take_append_drop`) with `|w.take t| = t` (`List.length_take`, since `t ≤ t'`).
By the hypothesis the run under `w.take t` is halted; `Turing.NDTM.runWith_append`
factors the run under `w` through it, and `Turing.NDTM.runWith_of_halt` absorbs the
remaining choices, so the state at `w` equals the halted state at `w.take t`. -/
theorem HaltsWithin.mono {tm : NDTM k Symbol State} {input : List Symbol} {t t' : ℕ}
    (h : tm.HaltsWithin input t) (hle : t ≤ t') : tm.HaltsWithin input t' := by
  intro w hw
  have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
  have hhalt := h (w.take t) hlen
  have hrun := runWith_append (tm := tm) (w.take t) (w.drop t) (tm.initCfg input)
  rw [List.take_append_drop, runWith_of_halt _ hhalt] at hrun
  rw [hrun]
  exact hhalt

end NDTM

/-- A nondeterministic machine bundled with a finite state type, mirroring
`Turing.FinTM`: the instances are data (`Fintype`/`DecidableEq`, not `Finite`) for the
same reason as there — a machine that is to be encoded as a string must enumerate its
transition tables. All headline nondeterministic-complexity definitions
(`Turing.FinNDTM.DecidesInTime`, `Complexity.NTIME`) are stated over this layer. -/
structure FinNDTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying nondeterministic machine -/
  tm : NDTM k Symbol State

attribute [instance] FinNDTM.fintypeState FinNDTM.decEqState

/-- A deterministic machine as a nondeterministic one whose two transition functions
coincide: both choices apply the deterministic transition. This is the embedding behind
`DTIME ⊆ NTIME` ([AB09, §2.1.2]: a TM is an NDTM that ignores its choices). -/
def MultiTapeTM.toNDTM (tm : MultiTapeTM k Symbol State) : NDTM k Symbol State :=
  ⟨tm.q₀, fun _ => tm.tr⟩

/-- The embedded deterministic machine starts where the original does. -/
@[simp]
lemma MultiTapeTM.toNDTM_initCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.toNDTM.initCfg input = tm.initCfg input := rfl

/-- The embedded deterministic machine ignores its choices: running `toNDTM` under any
choice word `w` is running the original machine for `|w|` steps.

**Proof sketch.** Induction on `w` generalizing the configuration. For one step,
`Turing.NDTM.stepWith` on `toNDTM` and `Turing.MultiTapeTM.step` are the same match on
the state — halted branches are both the identity, and on a live state both apply the
action `tm.tr q …` since `toNDTM.tr b = tm.tr` for either `b`. The cons case is then
`Turing.NDTM.runWith_cons` against `Turing.MultiTapeTM.runFrom_succ_eq_step` (the step
count on the right is `|w| + 1`, `List.length_cons`). -/
theorem MultiTapeTM.toNDTM_runWith (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (w : List Bool) (cfg : Cfg k Symbol State input) :
    tm.toNDTM.runWith w cfg = tm.runFrom cfg w.length := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih =>
    rw [NDTM.runWith_cons, List.length_cons, runFrom_succ_eq_step]
    exact ih (tm.step cfg)

/-- A bundled deterministic machine as a bundled nondeterministic one — the `FinTM`
layer of `Turing.MultiTapeTM.toNDTM`, with the same tapes and state type. -/
def FinTM.toFinNDTM {Symbol : Type} (M : FinTM Symbol) : FinNDTM Symbol :=
  ⟨M.k, M.State, M.tm.toNDTM⟩

end Turing

/-! ## Branches along state embeddings, deterministic slices, relabelling, input locality

The run-level layer of the nondeterministic contract variant (design §15d and §16; the C1 design
note §3.1). A deterministic host whose correctness is a per-step lockstep lifts to NDTMs slice by
slice: `Turing.NDTM.runWith_mapState_of_agreeOn` transfers a run along a state embedding when the
host's two transition functions agree with the source's on the states visited, and its
deterministic-source form `Turing.NDTM.runWith_mapState_of_agreeOn_det` carries every
deterministic phase contract to every branch. `Turing.NDTM.runWith_eq_fixChoice_runFrom` is the
slice lemma that stage 2's nondeterministic form needs (statement gated by the stage-2 pack,
`audits/stage2-statements-pack.md`; proof here). `Turing.NDTM.relabelState` mirrors
`Turing.MultiTapeTM.relabelState`. `Turing.NDTM.runWith_initCfg_take` is input locality: a
branch of at most `m` steps reads only the first `m` input symbols. -/

namespace Turing.NDTM

section Transfer

variable {k : ℕ} {Γ S H : Type*}

/-- **One step transfers along a state embedding.** Suppose that at every good state both
transition functions of `host` are the transition functions of `src` with successors renamed
along `emb`. Then from a configuration that is halted or at a good state, one step of `host`
under either choice bit is the renamed step of `src` under that bit. (Technical glue, no
textbook counterpart: the one-step identity behind `Turing.NDTM.runWith_mapState_of_agreeOn`.)

**Proof sketch.** A halted configuration is fixed by both steps. At a good state both steps read
the same symbols, the agreement selects the renamed action, and renaming commutes with applying
an action (`Turing.Cfg.mapState_apply`). -/
theorem stepWith_mapState_of_agreeOn {x : List Γ}
    (src : NDTM k Γ S) (host : NDTM k Γ H) (emb : S ↪ H) (good : S → Prop)
    (hagree : ∀ (b : Bool) (q : S), good q → ∀ inp work,
      host.tr b (emb q) inp work = (src.tr b q inp work).mapState emb)
    (c : Cfg k Γ S x) (hc : ∀ q, c.state = some q → good q) (b : Bool) :
    host.stepWith b (c.mapState emb) = (src.stepWith b c).mapState emb := by
  cases hs : c.state with
  | none =>
    have h1 : (c.mapState emb).state = none := by simp [Cfg.mapState, hs]
    rw [stepWith_of_halt h1, stepWith_of_halt hs]
  | some q =>
    have h1 : (c.mapState emb).state = some (emb q) := by simp [Cfg.mapState, hs]
    unfold stepWith
    rw [h1, hs]
    simp only
    rw [hagree b q (hc q hs)]
    exact Cfg.mapState_apply emb _ c

/-- **The nondeterministic agreement transfer** (the run-level nondeterministic contract
variant of design §15d and §16). Suppose that both transition functions of `host` agree, along
the state embedding `emb`, with the corresponding transition functions of `src` at every good
state, and that the run of `src` under the choice word `w` is at a good state whenever it is
live before its end. Then `host` under `w` runs exactly as `src` under `w`, renamed. The
endpoint is unrestricted, and `w = []` is the trivial case. [AB09, §2.1.2: a branch is the run
along one choice word]

**Proof sketch.** Induct on `w`. The guard at time `0` licenses the one-step identity
(`Turing.NDTM.stepWith_mapState_of_agreeOn`), and the shifted guard feeds the induction
hypothesis. -/
theorem runWith_mapState_of_agreeOn {x : List Γ}
    (src : NDTM k Γ S) (host : NDTM k Γ H) (emb : S ↪ H) (good : S → Prop)
    (hagree : ∀ (b : Bool) (q : S), good q → ∀ inp work,
      host.tr b (emb q) inp work = (src.tr b q inp work).mapState emb)
    (c : Cfg k Γ S x) (w : List Bool)
    (hguard : ∀ u < w.length, ∀ q, (src.runWith (w.take u) c).state = some q → good q) :
    host.runWith w (c.mapState emb) = (src.runWith w c).mapState emb := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih =>
    have h0 : ∀ q, c.state = some q → good q := fun q hq =>
      hguard 0 (by simp) q (by simpa using hq)
    rw [runWith_cons, runWith_cons,
      stepWith_mapState_of_agreeOn src host emb good hagree c h0 b]
    apply ih
    intro u hu q hq
    exact hguard (u + 1) (by simp; omega) q
      (by simpa [List.take_succ_cons, runWith_cons] using hq)

/-- **The transfer from a deterministic source.** Suppose that both transition functions of
`host` reproduce, renamed along `emb`, the transition function of the deterministic machine
`src` at every good state, and that the run of `src` from `c` is at a good state whenever it
is live before time `|w|`. Then every branch of `host` of length `|w|` from the renamed `c` is
the renamed run of `src` for `|w|` steps. So a deterministic phase contract of `src` (a MIG-0a
`Turing.Contract`, say) holds for `host` under every choice word of its length. It is the
nondeterministic mirror of `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`. [AB09, §2.1.2]

**Proof sketch.** Apply `Turing.NDTM.runWith_mapState_of_agreeOn` to `src.toNDTM`, whose
branches are `src`'s run (`Turing.MultiTapeTM.toNDTM_runWith`), on both sides. -/
theorem runWith_mapState_of_agreeOn_det {x : List Γ}
    (src : MultiTapeTM k Γ S) (host : NDTM k Γ H) (emb : S ↪ H) (good : S → Prop)
    (hagree : ∀ (b : Bool) (q : S), good q → ∀ inp work,
      host.tr b (emb q) inp work = (src.tr q inp work).mapState emb)
    (c : Cfg k Γ S x) (w : List Bool)
    (hguard : ∀ u < w.length, ∀ q, (src.runFrom c u).state = some q → good q) :
    host.runWith w (c.mapState emb) = (src.runFrom c w.length).mapState emb := by
  have h := runWith_mapState_of_agreeOn src.toNDTM host emb good
    (fun b q hq inp work => hagree b q hq inp work) c w (by
      intro u hu q hq
      rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hq
      exact hguard u hu q hq)
  rw [h, MultiTapeTM.toNDTM_runWith]

end Transfer

section Slice

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- **A branch that meets no real choice is a deterministic run.** If, at each of the first
`|w|` configurations of the run of the slice `tm.fixChoice b` from `cfg`, the machine is halted
or in a state at which its two transition functions agree, then the run of `tm` under the choice
word `w` is that deterministic run: `tm.runWith w cfg = (tm.fixChoice b).runFrom cfg |w|`.
[AB09, §2.1.2]

**Statement gated by the stage-2 pack** (`audits/stage2-statements-pack.md`, `NDSlice` Part A,
verbatim); **proof here**, by C1's argument (design §15d: one copy lands, in this file).

**Proof sketch.** This is `Turing.NDTM.runWith_mapState_of_agreeOn_det` with the slice as the
deterministic source, `tm` as the host, the identity embedding, and "the two transition
functions coincide" as the good states: at such a state either transition function of `tm` is
the slice's. Renaming along the identity is the identity. -/
theorem runWith_eq_fixChoice_runFrom (tm : NDTM k Symbol State) (b : Bool) (w : List Bool)
    (cfg : Cfg k Symbol State input)
    (hagree : ∀ j < w.length, ∀ q : State, ((tm.fixChoice b).runFrom cfg j).state = some q →
      tm.tr false q = tm.tr true q) :
    tm.runWith w cfg = (tm.fixChoice b).runFrom cfg w.length := by
  have e₁ : ∀ a : Action k Symbol State, a.mapState (Function.Embedding.refl State) = a := by
    intro a
    cases a with
    | mk i wt o st => cases st <;> rfl
  have e₂ : ∀ d : Cfg k Symbol State input,
      d.mapState (Function.Embedding.refl State) = d := by
    intro d
    cases d with
    | mk st ip wt wp o => cases st <;> rfl
  have h := runWith_mapState_of_agreeOn_det (tm.fixChoice b) tm (Function.Embedding.refl State)
    (fun q => tm.tr false q = tm.tr true q)
    (fun b' q hq inp work => by
      rw [e₁]
      cases b' <;> cases b <;> simp [fixChoice, hq]) cfg w hagree
  simpa only [e₂] using h

end Slice

section Relabel

variable {k : ℕ} {Γ S S' : Type*}

/-- **State relabelling of an NDTM** along an equivalence `e`: the initial state is mapped
forward, and both transition functions read the table through `e.symm` and rename successors
by `e`. It mirrors `Turing.MultiTapeTM.relabelState` and packages the linear normal form into
the `Fin`-state `Turing.CodeNDTM`. (Technical glue; [AB09, §1.4]'s finite state sets.) -/
def relabelState (tm : NDTM k Γ S) (e : S ≃ S') : NDTM k Γ S' where
  q₀ := e tm.q₀
  tr := fun b q inp w => (tm.tr b (e.symm q) inp w).mapState e

/-- **Relabelled branches are the renamed branches**, under every choice word and from every
configuration: `(tm.relabelState e).runWith w (c.mapState e) = (tm.runWith w c).mapState e`.

**Proof sketch.** `Turing.NDTM.runWith_mapState_of_agreeOn` with every state good: the relabelled
table at `e q` is the original table at `q`, renamed. -/
theorem relabelState_runWith {x : List Γ} (tm : NDTM k Γ S) (e : S ≃ S')
    (c : Cfg k Γ S x) (w : List Bool) :
    (tm.relabelState e).runWith w (c.mapState e) = (tm.runWith w c).mapState e := by
  exact runWith_mapState_of_agreeOn tm (tm.relabelState e) e.toEmbedding (fun _ => True)
    (fun b q _ inp work => by simp [relabelState]) c w (fun _ _ _ _ => trivial)

end Relabel

section Locality

variable {k : ℕ} {Γ S : Type*}

/-- At an input position at most `m`, the input reads of `x` and of `x.take m` coincide.

**Proof sketch.** Three cases of the position `v`: at `0` both read the left blank; at
`|x| + 1` the input is shorter than `m`, so `x.take m` has the same length and both read the
right blank; otherwise both read the symbol at index `v - 1 < min m |x|`. -/
private lemma inputSymbol_take_eq {x : List Γ} {m : ℕ} (c : Cfg k Γ S x)
    (c' : Cfg k Γ S (x.take m)) (hp : c'.inputPos.val = c.inputPos.val)
    (hm : c.inputPos.val ≤ m) : c'.inputSymbol = c.inputSymbol := by
  have hlen : (x.take m).length = min m x.length := List.length_take
  have hlt := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have hz : c.inputPos = 0 := Fin.ext (by simp [h0])
    have hz' : c'.inputPos = 0 := Fin.ext (by simp [hp, h0])
    simp [Cfg.inputSymbol, hz, hz']
  · by_cases hr : c.inputPos.val = x.length + 1
    · have hz : c.inputPos ≠ 0 := fun h => h0 (by simp [h])
      have hz' : c'.inputPos ≠ 0 := fun h => h0 (by rw [← hp, h]; simp)
      have hr' : c'.inputPos.val = (x.take m).length + 1 := by omega
      simp only [Cfg.inputSymbol, dif_neg hz, dif_neg hz', dif_pos hr, dif_pos hr']
    · have hin := inputSymbolInner (cfg := c) (c.inputPos.val - 1) (by omega) (by omega)
      have hin' := inputSymbolInner (cfg := c') (c.inputPos.val - 1) (by omega)
        (by omega)
      rw [hin, hin', List.getElem_take]

/-- An input move lands at the proposed position, clamped to the right end. -/
private lemma moveInputPos_val {N : ℕ} (q : Fin (N + 2)) (s : SignType) :
    (moveInputPos q s).val = min (((q.val : ℤ) + (s.cast : ℤ)).toNat) (N + 1) := by
  unfold moveInputPos
  dsimp only
  split_ifs with h
  · exact (Nat.min_eq_left (by omega)).symm
  · exact (Nat.min_eq_right (by omega)).symm

/-- An input move from the same position, below the shorter input's right end or on inputs of
the same length, lands at the same position, at most one cell further right.

**Proof sketch.** Both moves clamp the same proposed position to their right ends, which agree
or are not reached; the proposed position is at most one cell right of the start. -/
private lemma moveInputPos_val_take {n n' : ℕ} (pos : Fin (n + 2)) (pos' : Fin (n' + 2))
    (hp : pos'.val = pos.val) (hn : n' ≤ n) (hle : pos.val ≤ n' ∨ n' = n) (s : SignType) :
    (moveInputPos pos' s).val = (moveInputPos pos s).val ∧
      (moveInputPos pos s).val ≤ pos.val + 1 := by
  have hs1 : (s.cast : ℤ) ≤ 1 := by cases s <;> simp
  have hs2 : -1 ≤ (s.cast : ℤ) := by cases s <;> simp
  rw [moveInputPos_val, moveInputPos_val, hp]
  have hpv : ((pos.val : ℤ) + (s.cast : ℤ)).toNat ≤ pos.val + 1 := by omega
  have hlt := pos.isLt
  generalize ((pos.val : ℤ) + (s.cast : ℤ)).toNat = p at hpv ⊢
  omega

/-- One step from agreeing configurations on `x` and on `x.take m`, with the input head at most
at `m`, gives agreeing configurations, and moves the input head at most one cell right.

**Proof sketch.** Halted configurations are fixed. At a live state both configurations read
the same input symbol (by the read lemma) and the same work symbols, so the same action applies;
its fields agree, the input move by the move lemma. -/
private lemma stepWith_take_agree (tm : NDTM k Γ S) {x : List Γ} {m : ℕ} (b : Bool)
    (c : Cfg k Γ S x) (c' : Cfg k Γ S (x.take m))
    (hs : c'.state = c.state) (hp : c'.inputPos.val = c.inputPos.val)
    (hw : c'.workTapes = c.workTapes) (hq : c'.workTapePos = c.workTapePos)
    (ho : c'.output = c.output) (hm : c.inputPos.val ≤ m) :
    (tm.stepWith b c').state = (tm.stepWith b c).state ∧
      (tm.stepWith b c').inputPos.val = (tm.stepWith b c).inputPos.val ∧
      (tm.stepWith b c').workTapes = (tm.stepWith b c).workTapes ∧
      (tm.stepWith b c').workTapePos = (tm.stepWith b c).workTapePos ∧
      (tm.stepWith b c').output = (tm.stepWith b c).output ∧
      (tm.stepWith b c).inputPos.val ≤ c.inputPos.val + 1 := by
  have hsym := inputSymbol_take_eq c c' hp hm
  have hws : c'.workTapeSymbols = c.workTapeSymbols := by
    funext i
    simp only [Cfg.workTapeSymbols, hw, hq]
  have hmv := moveInputPos_val_take c.inputPos c'.inputPos hp (by simp)
    (by rw [List.length_take]; omega)
  cases hst : c.state with
  | none =>
    have hst' : c'.state = none := by rw [hs, hst]
    rw [stepWith_of_halt hst, stepWith_of_halt hst']
    exact ⟨hs, hp, hw, hq, ho, by omega⟩
  | some q =>
    have hst' : c'.state = some q := by rw [hs, hst]
    have e₁ : tm.stepWith b c = (tm.tr b q c.inputSymbol c.workTapeSymbols).apply c := by
      unfold stepWith
      rw [hst]
    have e₂ : tm.stepWith b c' = (tm.tr b q c.inputSymbol c.workTapeSymbols).apply c' := by
      unfold stepWith
      rw [hst', hsym, hws]
    rw [e₁, e₂]
    refine ⟨rfl, (hmv _).1, ?_, ?_, ?_, (hmv _).2⟩
    · funext i
      simp only [Action.apply, hw, hq]
    · funext i
      simp only [Action.apply, hq]
    · simp only [Action.apply, ho]

/-- Agreement of branches on `x` and on `x.take m` propagates along a choice word while the
input head cannot pass position `m`.

**Proof sketch.** Induct on the word with the one-step lemma; the head budget
`position + remaining length ≤ m + 1` is preserved because each step moves the head at most one
cell. -/
private lemma runWith_take_agree (tm : NDTM k Γ S) {x : List Γ} {m : ℕ} :
    ∀ (w : List Bool) (c : Cfg k Γ S x) (c' : Cfg k Γ S (x.take m)),
      c'.state = c.state → c'.inputPos.val = c.inputPos.val → c'.workTapes = c.workTapes →
      c'.workTapePos = c.workTapePos → c'.output = c.output →
      c.inputPos.val + w.length ≤ m + 1 →
      (tm.runWith w c').state = (tm.runWith w c).state ∧
        (tm.runWith w c').inputPos.val = (tm.runWith w c).inputPos.val ∧
        (tm.runWith w c').workTapes = (tm.runWith w c).workTapes ∧
        (tm.runWith w c').workTapePos = (tm.runWith w c).workTapePos ∧
        (tm.runWith w c').output = (tm.runWith w c).output
  | [], _, _, hs, hp, hw, hq, ho, _ => ⟨hs, hp, hw, hq, ho⟩
  | b :: w, c, c', hs, hp, hw, hq, ho, hlen => by
    simp only [List.length_cons] at hlen
    obtain ⟨hs₁, hp₁, hw₁, hq₁, ho₁, hb⟩ :=
      stepWith_take_agree tm b c c' hs hp hw hq ho (by omega)
    simp only [runWith_cons]
    exact runWith_take_agree tm w _ _ hs₁ hp₁ hw₁ hq₁ ho₁ (by omega)

/-- **Input locality.** A branch of at most `m` steps from the initial configuration reads only
the first `m` input symbols: run on the truncated input `x.take m` under the same choice word,
it has the same state, work tapes, work-head positions and output, and its input head is at the
same position. The universal NDTM therefore needs only the window `x.take t` of its input to
simulate `t` steps, which keeps `|x|` out of its time bound (user decision 5 of 2026-10-13).
[AB09, §1.2: the input head moves at most one cell per step]

**Proof sketch.** The input head starts at position `1` and moves at most one cell per step, so
before each of the first `m` steps it is at a position at most `m`. There both inputs read the
same symbol: a blank at `0`, and otherwise the symbol at that index, or the right blank when `x`
is shorter than `m`. Equal reads select the same action, and the input move lands at the same
position, because the shorter input's right end is not reached. Induct on the word. -/
theorem runWith_initCfg_take (tm : NDTM k Γ S) (x : List Γ) (m : ℕ) (w : List Bool)
    (hw : w.length ≤ m) :
    let c := tm.runWith w (tm.initCfg x)
    let c' := tm.runWith w (tm.initCfg (x.take m))
    c'.state = c.state ∧ c'.inputPos.val = c.inputPos.val ∧ c'.workTapes = c.workTapes ∧
      c'.workTapePos = c.workTapePos ∧ c'.output = c.output := by
  have h := runWith_take_agree tm (x := x) (m := m) w (tm.initCfg x) (tm.initCfg (x.take m))
    rfl (by simp) rfl rfl rfl (by simp; omega)
  exact h

end Locality

end Turing.NDTM
