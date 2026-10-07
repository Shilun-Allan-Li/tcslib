/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Clean

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A bank of clean deciders

The compiled machine of a register-tape program calls its deciders through one machine
with several start states (`Complexity.LogProg.compileTM` takes a single decider block).
This file builds that machine from finitely many space-bounded deciders: each decider is
padded to the largest number of work tapes, the padded machines are run side by side in one
state space (the start state selects the decider), and the whole is cleaned
(`Complexity.LogProg.cleanTM`).

## Main definitions

* `Complexity.LogProg.padTM` — a machine with extra, unused work tapes.
* `Complexity.LogProg.bankTM`, `Complexity.LogProg.bankStart` — the bank and its start states.

## Main results

* `Complexity.LogProg.bank_cleanRun` — started in `bankStart j` on `V`, the bank answers
  whether `V` belongs to decider `j`'s language, cleanly, with heads in
  `[-max (s j |V|) 1, max (s j |V|) 1]`, where decider `j` runs in space `s j`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## Padding with unused tapes -/

section Pad

variable {k K : ℕ} {S : Type}

/-- The machine `M` with `K ≥ k` work tapes, the extra ones unused. -/
def padTM (M : MultiTapeTM k Bool S) (K : ℕ) : MultiTapeTM K Bool S where
  q₀ := M.q₀
  tr q a w :=
    let act := M.tr q a (fun i => if h : i.val < K then w ⟨i.val, h⟩ else none)
    ⟨act.inputTape, fun i => if h : i.val < k then act.workTapes ⟨i.val, h⟩ else (none, 0),
      act.output, act.state⟩

/-- The padded configuration. -/
def padCfg {x : List Bool} (K : ℕ) (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos, fun i z => if h : i.val < k then c.workTapes ⟨i.val, h⟩ z else none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- One step of the padded machine on a padded configuration is the padding of one step of the
original machine.

**Proof sketch.** Unfold one step on both sides: the padded transition reads the original tapes'
symbols (the padding tapes are never read), applies the original action to them, and leaves the
padding tapes and heads unchanged. Compare componentwise, splitting tape indices into original
and padding ones. -/
lemma padTM_step {x : List Bool} (M : MultiTapeTM k Bool S) (hk : k ≤ K) (c : Cfg k Bool S x) :
    (padTM M K).step (padCfg K c) = padCfg K (M.step c) := by
  unfold MultiTapeTM.step
  simp only [padCfg]
  cases hs : c.state with
  | none => simp [hs]
  | some q =>
    simp only
    have hw : (fun i : Fin k => if h : i.val < K then
        (padCfg K c : Cfg K Bool S x).workTapeSymbols ⟨i.val, h⟩ else none) =
          c.workTapeSymbols := by
      funext i
      simp [padCfg, Cfg.workTapeSymbols, show i.val < K by omega]
    have hin : (padCfg K c : Cfg K Bool S x).inputSymbol = c.inputSymbol := rfl
    change ((padTM M K).tr q (padCfg K c).inputSymbol (padCfg K c).workTapeSymbols).apply
      (padCfg K c) = padCfg K ((M.tr q c.inputSymbol c.workTapeSymbols).apply c)
    simp only [padTM, hin, hw]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z
      simp only [Action.apply, padCfg]
      by_cases h : i.val < k
      · simp only [h, ↓reduceDIte]
      · simp [h]
    · funext i
      simp only [Action.apply, padCfg]
      by_cases h : i.val < k <;> simp [h]

/-- Runs of the padded machine on padded configurations are the paddings of the original runs. -/
lemma padTM_runFrom {x : List Bool} (M : MultiTapeTM k Bool S) (hk : k ≤ K) (c : Cfg k Bool S x)
    (n : ℕ) : (padTM M K).runFrom (padCfg K c) n = padCfg K (M.runFrom c n) :=
  MultiTapeTM.runFrom_comm_of_step (padCfg K) (padTM_step M hk) c n

end Pad

/-! ## Machines side by side -/

section Sigma

variable {d K : ℕ} {S : Fin d → Type}

/-- The machines `Ms j` in one state space; the dummy state `none` halts. -/
def sigmaTM (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) :
    MultiTapeTM K Bool (Option (Σ j, S j)) where
  q₀ := none
  tr
    | none, _, _ => ⟨0, fun _ => (none, 0), none, none⟩
    | some ⟨j, q⟩, a, w =>
      let act := (Ms j).tr q a w
      ⟨act.inputTape, act.workTapes, act.output, act.state.map fun q' => some ⟨j, q'⟩⟩

/-- The configuration of machine `j` inside the side-by-side machine. -/
def sigCfg {x : List Bool} (j : Fin d) (c : Cfg K Bool (S j) x) :
    Cfg K Bool (Option (Σ j, S j)) x :=
  ⟨c.state.map fun q => some ⟨j, q⟩, c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- One step of the disjoint union of machines on a configuration of component `j` is that
component's step. -/
lemma sigmaTM_step {x : List Bool} (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) (j : Fin d)
    (c : Cfg K Bool (S j) x) : (sigmaTM Ms).step (sigCfg j c) = sigCfg j ((Ms j).step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [sigCfg, hs]
  | some q =>
    simp only [sigCfg, hs, Option.map_some]
    rfl

/-- Runs of the disjoint union of machines on configurations of component `j` are that
component's runs. -/
lemma sigmaTM_runFrom {x : List Bool} (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) (j : Fin d)
    (c : Cfg K Bool (S j) x) (n : ℕ) :
    (sigmaTM Ms).runFrom (sigCfg j c) n = sigCfg j ((Ms j).runFrom c n) :=
  MultiTapeTM.runFrom_comm_of_step (sigCfg j) (sigmaTM_step Ms j) c n

end Sigma

/-! ## The bank -/

section Bank

variable {d : ℕ} (Ms : Fin d → FinTM Bool)

/-- The common number of work tapes. -/
def bankK : ℕ := Finset.univ.sup fun j => (Ms j).k

/-- Every machine of the bank has at most `bankK Ms` work tapes. -/
lemma le_bankK (j : Fin d) : (Ms j).k ≤ bankK Ms :=
  Finset.le_sup (f := fun j => (Ms j).k) (Finset.mem_univ j)

/-- The raw state type of the bank. -/
abbrev BankS : Type := Option (Σ j, (Ms j).State)

/-- **The bank of deciders**: the deciders padded to `bankK` tapes, side by side, cleaned. -/
def bankTM : MultiTapeTM (bankK Ms + bankK Ms) Bool (CleanSt (BankS Ms) (bankK Ms)) :=
  cleanTM (sigmaTM fun j => padTM (Ms j).tm (bankK Ms)) none

/-- The start state of decider `j` in the bank. -/
def bankStart (j : Fin d) : CleanSt (BankS Ms) (bankK Ms) := .init (some ⟨j, (Ms j).tm.q₀⟩)

/-- **The bank answers cleanly.** If decider `j` decides `A j` in space `s j`, then the bank
started in `bankStart j` on any `V` halts with output `[V ∈ A j]`, blank work tapes and heads
at the origin, all heads within `[-B, B]` for `B = max (s j |V|) 1`.

**Proof sketch.** Padding (`padTM_runFrom`) and the side-by-side union (`sigmaTM_runFrom`)
run decider `j` unchanged; its tapes visit at most `s j |V|` cells each and the padding
tapes only the origin; `cleanTM_run` does the rest. -/
theorem bank_cleanRun (A : Fin d → Language Bool) (s : Fin d → ℕ → ℕ)
    (hMs : ∀ j, (Ms j).DecidesInSpace (A j) (s j)) (j : Fin d) (V : List Bool) :
    CleanRun (bankTM Ms) (bankStart Ms j) V
      (MultiTapeTM.indicator (A j : Set (List Bool)) V) (max (s j V.length) 1) := by
  obtain ⟨T, hT, hsp⟩ := hMs j V
  rw [FinTM.computesInTime_iff] at hT
  obtain ⟨hhalt, hout⟩ := hT
  set K := bankK Ms
  have hk : (Ms j).k ≤ K := le_bankK Ms j
  -- the side-by-side padded run
  have hrun : ∀ t, (sigmaTM fun j => padTM (Ms j).tm K).runFrom
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) t =
      sigCfg (S := fun j => (Ms j).State) j (padCfg K ((Ms j).tm.runFrom ((Ms j).tm.initCfg V) t)) := by
    intro t
    have e : (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V : Cfg K Bool (BankS Ms) V) =
        sigCfg (S := fun j => (Ms j).State) j (padCfg K ((Ms j).tm.initCfg V)) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i z; simp [sigCfg, padCfg, Cfg.init]
      · funext i; simp [sigCfg, padCfg, Cfg.init]
    rw [e, sigmaTM_runFrom, padTM_runFrom _ hk]
  have hhalt' : ((sigmaTM fun j => padTM (Ms j).tm K).runFrom
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T).state = none := by
    rw [hrun]; simp only [sigCfg, padCfg]; rw [hhalt]; rfl
  -- visited cells per tape
  have hvis : ∀ i : Fin K, ((sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i).card ≤ max (s j V.length) 1 := by
    intro i
    by_cases hi : i.val < (Ms j).k
    · have hsub : (sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
          (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i =
          (Ms j).tm.visitedByTapeHead ((Ms j).tm.initCfg V) T ⟨i.val, hi⟩ := by
        simp only [MultiTapeTM.visitedByTapeHead, hrun, sigCfg, padCfg, hi, ↓reduceDIte]
      rw [hsub]
      exact ((Ms j).tm.spaceUsedByTape_le_spaceUsed _ T _).trans (hsp.trans (le_max_left _ _))
    · have hsub : (sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
          (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i ⊆ {0} := by
        intro z hz
        simp only [MultiTapeTM.visitedByTapeHead, hrun, sigCfg, padCfg, hi, ↓reduceDIte,
          Finset.mem_image, Finset.mem_range] at hz
        obtain ⟨_, _, rfl⟩ := hz
        simp
      exact (Finset.card_le_card hsub).trans (by simp)
  obtain ⟨T', h1, h2, h3, h4, h5⟩ := cleanTM_run (sigmaTM fun j => padTM (Ms j).tm K) none
    (some ⟨j, (Ms j).tm.q₀⟩) V T hhalt' _ hvis
  unfold CleanRun bankStart bankTM
  refine ⟨T', h1, ?_, h3, h4, fun t ht i => by exact_mod_cast h5 t ht i⟩
  rw [h2, hrun]
  simp only [sigCfg, padCfg]
  exact hout

end Bank

end Complexity.LogProg
