/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.InputRewind

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic phase host, the choice writer, and the guess-then-run assembly

The nondeterministic part of the construction layer that the guess-first route needs (user
decision 1 of 2026-10-13; the C1 design note §3.1, §3.4). The universal NDTM and the
diagonalizer of `TCSlib.Complexity.Diagonalization.NTimeHierarchy` guess their whole choice word
up front, with one small nondeterministic leaf, and then run deterministically.

## Design

* **The ND phase host** `Turing.NDTM.phaseHostND` is `Turing.phaseHostTM` over nondeterministic
  phases, deterministic phases entering as `Turing.MultiTapeTM.toNDTM`. Each of its two slices
  is the deterministic phase host of the phases' slices (`Turing.NDTM.phaseHostND_fixChoice`,
  through the phase host's field equations), and a phase runs inside it along every word
  (`Turing.NDTM.phaseHostND_run`, from the transfer `Turing.NDTM.runWith_mapState_of_agreeOn`).
* **Never put a choice inside a round body.** A host whose correctness is a per-step lockstep
  (the phase host, Z1, the R1 embedding, renaming) lifts to NDTMs slice by slice. A host that
  composes multi-step rounds (`Turing.counterLoopTMVia`, the step clock) does not: a branch
  mixes slices across rounds. So no nondeterministic counter loop is built (statement note
  SC-3 of design §12.7 is closed by this route); choices are guessed by the writer below, before
  any round host runs.
* **The choice writer** `Turing.ndWriterTM` is the guessed flavor of a choice source (H5's
  device family): on one tape, while its controller does not stop it (and, in the bounded
  flavor, while the cell under the head is nonblank), it writes its choice bit and moves right.
  Under a general controller, control is choice-dependent: the successor `δ q b`, and with it
  every later stop, depends on the bit. In the trivial-controller, never-stop instance of the
  bounded flavor (`Turing.ndWriterTM_run_block`), the two choices differ only in the written
  symbol, so its timing is branch-independent. The bounded flavor serves the universal NDTM and
  the diagonalizer; the controller flavor, the linear normal form's display guess.
* **The guess-then-run assembly** `Turing.guessCtlRunTM` composes the phase host over a
  deterministic setup, a choice writer (its controller and flavor as parameters), a rewind by the
  catalog's `Turing.skipTM` and `Turing.skipBackTM`, a deterministic run ending in a live verdict,
  and a verdict leaf (ruling 2 of the C1 host-contracts gate). `Turing.guessRunTM` is its instance
  with the bounded writer and the trivial controller. Its contract identifies the writer's word,
  transfers the deterministic phases, and gives all-branch halting and exact-budget acceptance; with
  the interpreter core run silently (`Turing.embedSilentTM`), the core's precondition and live
  verdicts (`Turing.guessRunTM_silent_spec`).
* **The controller-stopped instance** of `Turing.guessCtlRunTM`, the unbounded writer over a tape
  blank from its head on: the guess ends when the
  controller stops, after a number of bits that depends on the bits. Its contract gives the
  handoff, the whole branch through the run's verdict, and acceptance in both directions; a
  halted branch has passed a stop of the controller (`Turing.guessCtlRunTM_stop_of_halted`).
  There is no all-branch halting: a stream that never stops the controller never ends the guess.

## Main definitions

* `Turing.NDTM.phaseHostND` — the nondeterministic phase host.
* `Turing.NDWriterState`, `Turing.ndWriterTM` — the choice writer. [AB09, §2.1.2]
* `Turing.GuessRunPhase`, `Turing.GuessRunPhase.CtlState`, `Turing.guessCtlRunPhases`,
  `Turing.guessCtlRunRed`, `Turing.guessCtlRunTM` — the guess-then-run host over a writer.
  [AB09, §2.1.2, proof of Theorem 2.6]
* `Turing.GuessRunPhase.State`, `Turing.guessRunPhases`, `Turing.guessRunRed`,
  `Turing.guessRunTM` — its bounded, trivial-controller instance.
* `Turing.guessRunCfg`, `Turing.streamStartCfg` — the run's entry configuration after a guess,
  and the interpreter core's start configuration.

## Main results

* `Turing.NDTM.phaseHostND_fixChoice`, `Turing.NDTM.phaseHostND_run` (proved).
* `Turing.ndWriterTM_run_block` — the bounded flavor's contract (proved).
* `Turing.ndWriterTM_run_controller` — the controller-stopped flavor's contract (proved).
* `Turing.guessRunTM_runWith_handoff`, `Turing.guessRunTM_runWith_handoff_state`,
  `Turing.guessRunTM_runWith_live`, `Turing.guessRunTM_runWith`,
  `Turing.guessRunTM_haltsWithin`, `Turing.guessRunTM_accepts_iff` — the guess-then-run assembly
  (proved); `Turing.guessRunTM_runWith_setup_halt` — a halting setup (proved).
* `Turing.guessRunCfg_clean`, `Turing.guessRunTM_silent_spec` (proved) — the interpreter
  core's interface: precondition, emission capture, live verdicts.
* `Turing.guessCtlRunTM_runWith_handoff`, `Turing.guessCtlRunTM_runWith`,
  `Turing.guessCtlRunTM_stop_of_halted`, `Turing.guessCtlRunTM_accepts_of`,
  `Turing.guessCtlRunTM_stream_of_accepts` — the controller-stopped instance (proved).
* The fields of the two configurations `Turing.guessRunCfg_state`, `_inputPos`, `_workTapes`,
  `_workTapePos`, `_output` and `Turing.streamStartCfg_state`, `_inputPos`, `_workTapes`,
  `_workTapePos`, `_output` (the ND inventory API, C1's pre-ship inventory, 2026-10-17).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2: an NDTM chooses one of its two transition
  functions at every step; the proof of Theorem 2.6: guess a string, then verify it
  deterministically; Exercise 2.6.)
-/

namespace Turing.NDTM

variable {k : ℕ} {Γ : Type}

/-- **The nondeterministic phase host**: `Turing.phaseHostTM` over nondeterministic phases.
Its states are the tagged phase states. A state that `red` maps to `some q` takes one
stationary, silent dispatch step to `q` under either choice; every other state of phase `i`
follows phase `i`'s two transition functions, with successors tagged by `i`. Deterministic
phases enter as `Turing.MultiTapeTM.toNDTM`. (A host of the construction layer; [AB09,
§2.1.2].) -/
def phaseHostND {I : Type} {Ph : I → Type} (M : (i : I) → NDTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) :
    NDTM k Γ (Σ i, Ph i) where
  q₀ := q0
  tr := fun b q inp w =>
    match red q.1 q.2 with
    | some q' => ⟨0, fun _ => (none, 0), none, some q'⟩
    | none => ((M q.1).tr b q.2 inp w).mapState (Sigma.mk q.1)

/-- **Each slice of the ND phase host is a deterministic phase host**: fixing the choice `b`
in `Turing.NDTM.phaseHostND` gives `Turing.phaseHostTM` over the phases' slices at `b`.

**Proof sketch.** Compare the two fields. The start states agree (`Turing.NDTM.fixChoice_q₀`,
`Turing.phaseHostTM_q₀`). For the tables, split on the redirect: at a redirected state both
dispatch to its target (`Turing.phaseHostTM_tr_of_red_some`); elsewhere both take the phase's
slice action with the successor tagged (`Turing.phaseHostTM_tr_of_red_none`,
`Turing.NDTM.fixChoice_tr`). A machine is determined by its two fields. -/
theorem phaseHostND_fixChoice {I : Type} {Ph : I → Type} (M : (i : I) → NDTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (b : Bool) :
    (phaseHostND M q0 red).fixChoice b = phaseHostTM (fun i => (M i).fixChoice b) q0 red := by
  have hq : ((phaseHostND M q0 red).fixChoice b).q₀ =
      (phaseHostTM (fun i => (M i).fixChoice b) q0 red).q₀ := by
    rw [NDTM.fixChoice_q₀, phaseHostTM_q₀]
    rfl
  have ht : ((phaseHostND M q0 red).fixChoice b).tr =
      (phaseHostTM (fun i => (M i).fixChoice b) q0 red).tr := by
    funext q inp w
    obtain ⟨i, s⟩ := q
    rw [NDTM.fixChoice_tr]
    cases h : red i s with
    | none =>
      rw [phaseHostTM_tr_of_red_none _ _ _ i s h, NDTM.fixChoice_tr]
      simp only [phaseHostND, h]
    | some q' =>
      rw [phaseHostTM_tr_of_red_some _ _ _ i s h]
      simp only [phaseHostND, h]
  calc (phaseHostND M q0 red).fixChoice b
      = ⟨((phaseHostND M q0 red).fixChoice b).q₀, ((phaseHostND M q0 red).fixChoice b).tr⟩ := rfl
    _ = ⟨(phaseHostTM (fun i => (M i).fixChoice b) q0 red).q₀,
          (phaseHostTM (fun i => (M i).fixChoice b) q0 red).tr⟩ := by rw [hq, ht]
    _ = phaseHostTM (fun i => (M i).fixChoice b) q0 red := rfl

/-- **The ND phase lemma** (the nondeterministic counterpart of `Turing.phaseHostTM_run`). Let
phase `i` run under the word `w` from `c` to `c'`, ending at a state `s'` that `red` redirects
to `q'`, and reaching no redirected state before. Then inside the host, every prefix of `w`
drives the tagged phase run from the tagged `c`, and one further choice, either bit, performs
the dispatch to `q'` with every other field of `c'` unchanged.

**Proof sketch.** `Turing.NDTM.runWith_mapState_of_agreeOn` along `Sigma.mk i`, with the good
states those that `red` does not redirect; the final dispatch is one explicit step. -/
theorem phaseHostND_run {I : Type} {Ph : I → Type} (M : (i : I) → NDTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) {x : List Γ}
    (c c' : Cfg k Γ (Ph i) x) (w : List Bool) (h : (M i).runWith w c = c') (s' : Ph i)
    (hs' : c'.state = some s') (q' : Σ i, Ph i) (hred : red i s' = some q')
    (hguard : ∀ u < w.length, ∀ s, ((M i).runWith (w.take u) c).state = some s →
      red i s = none) (b : Bool) :
    (∀ u ≤ w.length, (phaseHostND M q0 red).runWith (w.take u) (c.mapState (Sigma.mk i)) =
        ((M i).runWith (w.take u) c).mapState (Sigma.mk i)) ∧
      (phaseHostND M q0 red).runWith (w ++ [b]) (c.mapState (Sigma.mk i)) =
        c'.mapState (fun _ => q') := by
  let emb : Ph i ↪ (Σ i, Ph i) := ⟨Sigma.mk i, sigma_mk_injective⟩
  have hagree : ∀ (b : Bool) (s : Ph i), red i s = none → ∀ inp work,
      (phaseHostND M q0 red).tr b (emb s) inp work =
        ((M i).tr b s inp work).mapState emb := by
    intro b s hs inp work
    simp only [phaseHostND, emb, Function.Embedding.coeFn_mk, hs]
  have hpre : ∀ u ≤ w.length,
      (phaseHostND M q0 red).runWith (w.take u) (c.mapState (Sigma.mk i)) =
        ((M i).runWith (w.take u) c).mapState (Sigma.mk i) := by
    intro u hu
    exact runWith_mapState_of_agreeOn (M i) (phaseHostND M q0 red) emb
      (fun s => red i s = none) hagree c (w.take u) (by
        intro v hv s hs
        rw [List.length_take] at hv
        rw [List.take_take, Nat.min_eq_left (by omega)] at hs
        exact hguard v (by omega) s hs)
  refine ⟨hpre, ?_⟩
  rw [runWith_append]
  have hw := hpre w.length le_rfl
  rw [List.take_length, h] at hw
  rw [hw, runWith_cons, runWith_nil]
  have hst : (c'.mapState (Sigma.mk i)).state = some ⟨i, s'⟩ := by
    simp [Cfg.mapState, hs']
  unfold stepWith
  rw [hst]
  simp only [phaseHostND, hred]
  apply Cfg.ext <;> simp [Cfg.mapState, hs']

end Turing.NDTM

namespace Turing

/-- Control of the choice writer: running with a controller state `q`, or `done` (the live exit
anchor). -/
inductive NDWriterState (Q : Type) where
  /-- writing, with controller state `q` -/
  | run (q : Q)
  /-- the live exit anchor -/
  | done
  deriving DecidableEq

/-- **The choice writer** (H5's choice device, guessed flavor). An NDTM with `k` work tapes and
writer tape `j`. In state `run q`: if the controller asks to stop (`stop q`), or, in the
`bounded` flavor, the cell under the head of tape `j` is blank, it moves to `done` without
moving or writing; otherwise it writes its choice bit `b` on tape `j`, moves that head right,
and updates the controller to `δ q b`. `done` is a silent, stationary, live self-loop. Under a
general controller the choice also selects the successor `δ q b`, so control is
choice-dependent; with the trivial controller that never stops, the two choices differ only in
the written symbol. The controller type `Q` need not be finite. No input move, no output.
[AB09, §2.1.2: the choice at each step] -/
def ndWriterTM (k : ℕ) (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) : NDTM k Bool (NDWriterState Q) where
  q₀ := .run q₀
  tr := fun b q _ w =>
    match q with
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .run q =>
      if stop q || (bounded && (w j).isNone) then ⟨0, fun _ => (none, 0), none, some .done⟩
      else ⟨0, fun i => if i = j then (some (some b), 1) else (none, 0), none,
        some (.run (δ q b))⟩

/-- The configuration after writing the word `s`, in the writer state `q`, before testing the
next cell. -/
private def wr_cfg {k : ℕ} (j : Fin k) {Q : Type} {x : List Bool}
    (c : Cfg k Bool (NDWriterState Q) x) (q : NDWriterState Q) (s : List Bool) :
    Cfg k Bool (NDWriterState Q) x :=
  { c with
    state := some q
    workTapes := Function.update c.workTapes j (fun p =>
      if c.workTapePos j ≤ p ∧ p < c.workTapePos j + s.length then
        FinTM.bufferTape s (p - c.workTapePos j)
      else c.workTapes j p)
    workTapePos := Function.update c.workTapePos j (c.workTapePos j + s.length) }

/-- Extending a written interval by one bit is a single update at its right boundary.

**Proof sketch.** At the boundary use the buffer's append equation. Off the boundary the
update is inert, and the two integer interval tests agree. -/
private theorem wr_tape_append (t : ℤ → Option Bool) (a : ℤ) (s : List Bool) (b : Bool) :
    Function.update (fun p => if a ≤ p ∧ p < a + s.length then
      FinTM.bufferTape s (p - a) else t p) (a + s.length) (some b) =
    fun p => if a ≤ p ∧ p < a + (s ++ [b]).length then
      FinTM.bufferTape (s ++ [b]) (p - a) else t p := by
  funext p
  rw [FinTM.bufferTape_append]
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  by_cases hp : p = a + s.length
  · subst p
    rw [Function.update_self, if_pos (by omega)]
    rw [show a + (s.length : ℤ) - a = s.length by omega, Function.update_self]
  · rw [Function.update_of_ne hp]
    have hoff : p - a ≠ (s.length : ℤ) := by omega
    rw [Function.update_of_ne hoff]
    by_cases h : a ≤ p ∧ p < a + s.length
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-- The empty written prefix in the start state gives the original configuration. -/
private theorem wr_cfg_nil {k : ℕ} (j : Fin k) {Q : Type} {x : List Bool}
    (c : Cfg k Bool (NDWriterState Q) x) (q : NDWriterState Q) (hc : c.state = some q) :
    wr_cfg j c q [] = c := by
  apply Cfg.ext
  · exact hc.symm
  · rfl
  · funext i p
    have hempty : ¬ (c.workTapePos j ≤ p ∧ p < c.workTapePos j) := by omega
    by_cases hi : i = j <;> simp [wr_cfg, hi, hempty]
  · funext i
    by_cases hi : i = j <;> simp [wr_cfg, hi]
  · rfl

/-- The next cell of the block still has its original symbol. -/
private theorem wr_cfg_scan {k : ℕ} (j : Fin k) {Q : Type} {x : List Bool}
    (c : Cfg k Bool (NDWriterState Q) x) (q : NDWriterState Q) (s : List Bool) :
    (wr_cfg j c q s).workTapeSymbols j = c.workTapes j (c.workTapePos j + s.length) := by
  rw [Cfg.workTapeSymbols_eq]
  simp only [wr_cfg, Function.update_self, lt_self_iff_false, and_false, if_false]

/-- One writer step from the written-prefix configuration in the controller state `q`: if the
controller stops, or (bounded flavor) the next cell is blank, the stationary exit `done`;
otherwise the written prefix extended by the choice bit, the controller updated by it, and the
writer's head one cell further right.

**Proof sketch.** Read the live step through `Turing.NDTM.stepWith_of_some` and the writer's
test at the next cell (`wr_cfg_scan`), then the applied action through its field equations. On
both branches the input head and the output are unchanged. On the exit the action is stationary
and writes nothing; otherwise the buffer append equation (`wr_tape_append`) gives the written
tape and the head moves by one. -/
private theorem wr_cfg_stepWith {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) {x : List Bool}
    (c : Cfg k Bool (NDWriterState Q) x) (q : Q) (s : List Bool) (b : Bool) :
    (ndWriterTM k j q₀ δ stop bounded).stepWith b (wr_cfg j c (.run q) s) =
      if (stop q || (bounded && (c.workTapes j (c.workTapePos j + s.length)).isNone)) = true then
        wr_cfg j c .done s
      else wr_cfg j c (.run (δ q b)) (s ++ [b]) := by
  rw [NDTM.stepWith_of_some (q := .run q) (by rfl)]
  simp only [ndWriterTM, wr_cfg_scan]
  split_ifs with hcell <;> apply Cfg.ext <;>
    first
    | (rw [Action.apply_state]; try rfl)
    | (rw [Action.apply_inputPos]; exact moveInputPos_zero _)
    | (rw [Action.apply_output]; simp only [Option.toList_none, List.append_nil, wr_cfg])
    | skip
  · funext i
    rw [Action.apply_workTapes]
    simp only [Option.getD_none, Cfg.workTapeSymbols_eq, Function.update_eq_self]
    rfl
  · funext i
    rw [Action.apply_workTapePos]
    simp only [SignType.coe_zero, add_zero]
    rfl
  · funext i
    rw [Action.apply_workTapes]
    by_cases hi : i = j
    · subst i
      simp only [wr_cfg, Function.update_self, ↓reduceIte, Option.getD_some]
      exact wr_tape_append (c.workTapes j) (c.workTapePos j) s b
    · simp only [wr_cfg, if_neg hi, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self, Function.update_of_ne hi]
  · funext i
    rw [Action.apply_workTapePos]
    by_cases hi : i = j
    · subst i
      simp only [wr_cfg, Function.update_self, ↓reduceIte, SignType.coe_one,
        List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    · simp only [wr_cfg, Function.update_of_ne hi, if_neg hi, SignType.coe_zero, add_zero]

/-- While the writer does not stop (its controller does not stop it, and, bounded, the next cell
is nonblank), every prefix of the word drives it to the written-prefix configuration, in the
controller state that the prefix reaches.

**Proof sketch.** Induct on the prefix length. The writer does not stop at the state the prefix
so far reaches, so the one-step lemma appends the next choice bit and updates the controller by
it; `List.foldl` over the extended prefix is that update. -/
private theorem wr_prefix_gen {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) {x : List Bool} (c : Cfg k Bool (NDWriterState Q) x)
    (q : Q) (hc : c.state = some (.run q)) (w : List Bool) (u : ℕ) (hw : u ≤ w.length)
    (hlive : ∀ i < u, (stop ((w.take i).foldl δ q) ||
      (bounded && (c.workTapes j (c.workTapePos j + i)).isNone)) = false) :
    (ndWriterTM k j q₀ δ stop bounded).runWith (w.take u) c =
      wr_cfg j c (.run ((w.take u).foldl δ q)) (w.take u) := by
  revert hw hlive
  induction u with
  | zero =>
    intro _ _
    rw [List.take_zero, NDTM.runWith_nil, List.foldl_nil, wr_cfg_nil j c _ hc]
  | succ u ih =>
    intro hw hlive
    have hlt : u < w.length := by omega
    have hlen : (w.take u).length = u := List.length_take_of_le (by omega)
    rw [List.take_succ_eq_append_getElem hlt, NDTM.runWith_append,
      ih (by omega) (fun i hi => hlive i (by omega)), NDTM.runWith_cons, NDTM.runWith_nil,
      wr_cfg_stepWith, hlen, if_neg (by simp [hlive u (by omega)]), List.foldl_append,
      List.foldl_cons, List.foldl_nil]

/-- Every prefix that fits in the nonblank block drives the bounded writer with the trivial
controller to the written-prefix configuration (`wr_prefix_gen`). -/
private theorem wr_prefix {k : ℕ} (j : Fin k) {x : List Bool}
    (c : Cfg k Bool (NDWriterState Unit) x) (hc : c.state = some (.run ()))
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → c.workTapes j (c.workTapePos j + p) ≠ none)
    (w : List Bool) (u : ℕ) (hu : u ≤ m) (hw : u ≤ w.length) :
    (ndWriterTM k j () (fun _ _ => ()) (fun _ => false) true).runWith (w.take u) c =
      wr_cfg j c (.run ()) (w.take u) :=
  wr_prefix_gen j () (fun _ _ => ()) (fun _ => false) true c () hc w u hw (fun i hi => by
    cases h : c.workTapes j (c.workTapePos j + i) with
    | none => exact absurd h (hblock i (by omega))
    | some _ => rfl)

/-- **The writer's first stop.** If along the word `w` the writer first stops after `m` written
bits (its controller, or, bounded, the next cell, stops it at `m` and at no `i < m`), with
`m < |w|`, then the prefix `w.take (m + 1)` writes `w.take m` from the head and reaches `done`,
every other field unchanged, and no prefix of length at most `m` reaches `done`.

**Proof sketch.** `wr_prefix_gen` up to `m`, then one step of `wr_cfg_stepWith`, whose test holds
at `m`; the prefixes up to `m` are at `run`. -/
private theorem wr_run_first_stop {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) {x : List Bool} (c : Cfg k Bool (NDWriterState Q) x)
    (q : Q) (hc : c.state = some (.run q)) (w : List Bool) (m : ℕ) (hm : m < w.length)
    (hlive : ∀ i < m, (stop ((w.take i).foldl δ q) ||
      (bounded && (c.workTapes j (c.workTapePos j + i)).isNone)) = false)
    (hstop : (stop ((w.take m).foldl δ q) ||
      (bounded && (c.workTapes j (c.workTapePos j + m)).isNone)) = true) :
    (ndWriterTM k j q₀ δ stop bounded).runWith (w.take (m + 1)) c =
      { c with
        state := some .done
        workTapes := Function.update c.workTapes j (fun p =>
          if c.workTapePos j ≤ p ∧ p < c.workTapePos j + m then
            FinTM.bufferTape (w.take m) (p - c.workTapePos j)
          else c.workTapes j p)
        workTapePos := Function.update c.workTapePos j (c.workTapePos j + m) } ∧
    ∀ i ≤ m, ((ndWriterTM k j q₀ δ stop bounded).runWith (w.take i) c).state ≠ some .done := by
  have hlen : (w.take m).length = m := List.length_take_of_le hm.le
  constructor
  · rw [List.take_succ_eq_append_getElem hm, NDTM.runWith_append,
      wr_prefix_gen j q₀ δ stop bounded c q hc w m hm.le hlive, NDTM.runWith_cons,
      NDTM.runWith_nil, wr_cfg_stepWith, hlen, if_pos hstop]
    simp only [wr_cfg, hlen]
  · intro i hi
    rw [wr_prefix_gen j q₀ δ stop bounded c q hc w i (by omega)
      (fun i' hi' => hlive i' (by omega))]
    simp only [wr_cfg, ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- **The bounded choice writer's contract.** Start the bounded writer with the trivial
controller at `run ()` over a nonblank block of `m` cells of tape `j` from its head, followed by
a blank. Then every choice word `w` of length `m + 1` overwrites the block with its first `m`
bits, leaves the head of tape `j` just after the block, and reaches `done`; every other field is
unchanged. No shorter word reaches `done`. So the guessed stream is exactly `w.take m`, on every
branch at the same time `m + 1`, and every stream of length `m` is guessed (by `s ++ [b]`).
[AB09, §2.1.2]

**Proof sketch.** Induct on the first `m` steps: at step `u < m` the head of tape `j` is at cell
`u` of the block, which still holds its original nonblank symbol, so the writer writes `w[u]`
and moves right, keeping state `run ()`. At step `m` the head reads the blank after the block,
and the writer moves to `done` without moving. Before step `m + 1` the state is `run ()`. -/
theorem ndWriterTM_run_block {k : ℕ} (j : Fin k) {x : List Bool}
    (c : Cfg k Bool (NDWriterState Unit) x) (hc : c.state = some (.run ()))
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → c.workTapes j (c.workTapePos j + p) ≠ none)
    (hend : c.workTapes j (c.workTapePos j + m) = none)
    (w : List Bool) (hw : w.length = m + 1) :
    (ndWriterTM k j () (fun _ _ => ()) (fun _ => false) true).runWith w c =
      { c with
        state := some .done
        workTapes := Function.update c.workTapes j (fun p =>
          if c.workTapePos j ≤ p ∧ p < c.workTapePos j + m then
            FinTM.bufferTape (w.take m) (p - c.workTapePos j)
          else c.workTapes j p)
        workTapePos := Function.update c.workTapePos j (c.workTapePos j + m) } ∧
    ∀ w' : List Bool, w'.length < m + 1 →
      ((ndWriterTM k j () (fun _ _ => ()) (fun _ => false) true).runWith w' c).state ≠
        some .done := by
  have hfirst := wr_run_first_stop j () (fun _ _ => ()) (fun _ => false) true c () hc w m (by omega)
    (fun i hi => by
      cases h : c.workTapes j (c.workTapePos j + i) with
      | none => exact absurd h (hblock i hi)
      | some _ => rfl)
    (by simp [hend])
  rw [List.take_of_length_le (show w.length ≤ m + 1 by omega)] at hfirst
  refine ⟨hfirst.1, ?_⟩
  intro w' hw'
  have hrun := wr_prefix j c hc m hblock w' w'.length (by omega) le_rfl
  rw [List.take_length] at hrun
  rw [hrun]
  simp only [wr_cfg, ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- While the controller has not stopped, every prefix of the word drives the controller-stopped
writer to the written-prefix configuration, in the controller state that the prefix reaches
(`wr_prefix_gen`). -/
private theorem wr_prefix_controller {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q)
    (δ : Q → Bool → Q) (stop : Q → Bool) {x : List Bool} (c : Cfg k Bool (NDWriterState Q) x)
    (q : Q) (hc : c.state = some (.run q)) (w : List Bool) (u : ℕ) (hw : u ≤ w.length)
    (hlive : ∀ i < u, stop ((w.take i).foldl δ q) = false) :
    (ndWriterTM k j q₀ δ stop false).runWith (w.take u) c =
      wr_cfg j c (.run ((w.take u).foldl δ q)) (w.take u) :=
  wr_prefix_gen j q₀ δ stop false c q hc w u hw (fun i hi => by simp [hlive i hi])

/-- **The controller-stopped choice writer's contract.** Start the writer, unbounded, at `run q`
on any tape `j`. Let a choice word `w` first stop the controller after `m` written bits: the
controller state after writing `w.take i` is `(w.take i).foldl δ q`, which does not stop for
`i < m` and stops at `m`, with `m < |w|`. Then the prefix `w.take (m + 1)` overwrites the `m`
cells of tape `j` from its head with `w.take m`, leaves the head just after them and reaches
`done`, every other field unchanged; and no prefix of length at most `m` reaches `done`. The
writer ignores the cells it overwrites, so the tape may hold anything there. [AB09, §2.1.2]

**Proof sketch.** Induct on `i ≤ m` (`wr_prefix_controller`): after `w.take i` the configuration
is the block update with `w.take i`, the head at `c.workTapePos j + i`, state
`run ((w.take i).foldl δ q)`. At `i < m` the controller does not stop, so the writer writes
`w[i]` and moves right; at `m` it stops and moves to `done` without moving. -/
theorem ndWriterTM_run_controller {k : ℕ} (j : Fin k) {Q : Type} (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) {x : List Bool} (c : Cfg k Bool (NDWriterState Q) x) (q : Q)
    (hc : c.state = some (.run q)) (w : List Bool) (m : ℕ) (hm : m < w.length)
    (hlive : ∀ i < m, stop ((w.take i).foldl δ q) = false)
    (hstop : stop ((w.take m).foldl δ q) = true) :
    (ndWriterTM k j q₀ δ stop false).runWith (w.take (m + 1)) c =
      { c with
        state := some .done
        workTapes := Function.update c.workTapes j (fun p =>
          if c.workTapePos j ≤ p ∧ p < c.workTapePos j + m then
            FinTM.bufferTape (w.take m) (p - c.workTapePos j)
          else c.workTapes j p)
        workTapePos := Function.update c.workTapePos j (c.workTapePos j + m) } ∧
    ∀ i ≤ m, ((ndWriterTM k j q₀ δ stop false).runWith (w.take i) c).state ≠ some .done :=
  wr_run_first_stop j q₀ δ stop false c q hc w m hm (fun i hi => by simp [hlive i hi])
    (by simp [hstop])

end Turing

/-! ## The guess-then-run assembly

The universal NDTM and the diagonalizer of `TCSlib.Complexity.Diagonalization.NTimeHierarchy`
share one shape (user decision 1 of 2026-10-13; ruling 2 of the C1 host-contracts gate). A
deterministic setup leaves a nonblank block of `m` cells on a stream tape; the bounded choice
writer overwrites it with `m` choice bits; the stream head is rewound; a deterministic run ends in
one of two live verdict states; and a verdict leaf emits the verdict bit and halts. This is a
composition of the present host `Turing.NDTM.phaseHostND` over six phases, with the catalog's
`Turing.skipTM` and `Turing.skipBackTM` as the rewind: no new host. Deterministic phases enter as
`Turing.MultiTapeTM.toNDTM`, so the writer is the only choice-dependent phase, and a branch is
determined by the `m` bits it writes. The host is defined once over the writer
(`Turing.guessCtlRunTM`, the writer's controller and flavor as parameters), and its handoff and
the rest of a branch are proved once for any writer whose run on the stream is known;
`Turing.guessRunTM` is the instance with the bounded writer and the trivial controller, and the
controller-stopped instance is the next section's.

* `Turing.guessRunTM_runWith_handoff`: every word of length `TP + 2m + 9` drives the host to the
  run's entry, with the block overwritten by the word's `m` bits after its first `TP + 1` (the
  writer's word, identified) and every head where the setup left it.
* `Turing.guessRunTM_runWith_live`: no shorter word halts the host;
  `Turing.guessRunTM_runWith_handoff_state`: at the handoff itself the host is live, at the run's
  entry.
* `Turing.guessRunTM_runWith_setup_halt`: a setup that halts before its exit halts the host,
  unguessed.
* `Turing.guessRunTM_runWith`: the whole branch, through the run's first verdict, halted by time
  `TP + 2m + TQ + 11` with the verdict bit appended to the output; later choices are absorbed.
* `Turing.guessRunTM_haltsWithin`, `Turing.guessRunTM_accepts_iff`: all-branch halting, and
  exact-budget acceptance in both directions.
* `Turing.guessRunCfg_clean`, `Turing.guessRunTM_silent_spec`: the interface of the interpreter
  core `Turing.exists_ndInterpreterCore`. From a clean setup the run's entry is the core's start
  configuration, silently embedded (`Turing.embedSilentTM` captures the core's emissions), and
  the core's live verdicts become the host's.

Every theorem here is proved. The writer's contract `Turing.ndWriterTM_run_block` is proved by
one induction over the written prefix (C1-W, 2026-10-17); the seven theorems that pass the
writer use it, and `Turing.guessRunTM_runWith_setup_halt` and `Turing.guessRunCfg_clean` do not.
-/

namespace Turing

/-- The choice writer's control states are finite when the controller's are: `NDWriterState Q`
is equivalent to `Option Q` (`run q ↦ some q`, `done ↦ none`). Needed to bundle the
guess-then-run host as a `Turing.FinNDTM`. -/
instance NDWriterState.instFintype {Q : Type} [Fintype Q] : Fintype (NDWriterState Q) :=
  Fintype.ofEquiv (Option Q)
    { toFun := fun o => match o with
        | some q => .run q
        | none => .done
      invFun := fun s => match s with
        | .run q => some q
        | .done => none
      left_inv := fun o => by cases o <;> rfl
      right_inv := fun s => by cases s <;> rfl }

/-- **The phases of the guess-then-run host**, in run order: the deterministic setup, the bounded
choice writer, one step right past the guessed block, the rewind of the writer's tape to the
block's start, the deterministic run up to a live verdict, and the verdict emission. (Technical
glue: the phase index of `Turing.guessRunTM`.) -/
inductive GuessRunPhase where
  /-- the deterministic setup -/
  | pre
  /-- the bounded choice writer -/
  | guess
  /-- one step right, past the blank after the guessed block -/
  | skip
  /-- the rewind of the writer's tape to the block's start -/
  | back
  /-- the deterministic run, up to a live verdict -/
  | run
  /-- the verdict emission -/
  | out
  deriving DecidableEq, Fintype

/-- **The control states of each phase of the guess-then-run host over a writer with controller
states `Q`**: the setup's `SP`; the writer's `Turing.NDWriterState Q`; the seek phases
`Turing.SeekPhase` for the step right and for the rewind; the run's `SQ`; and the verdict bit for
the emission. -/
def GuessRunPhase.CtlState (SP SQ Q : Type) : GuessRunPhase → Type
  | .pre => SP
  | .guess => NDWriterState Q
  | .skip => SeekPhase
  | .back => SeekPhase
  | .run => SQ
  | .out => Bool

/-- Each phase's state type is finite when the setup's, the run's and the controller's are. -/
instance GuessRunPhase.instFintypeCtlState {SP SQ Q : Type} [Fintype SP] [Fintype SQ]
    [Fintype Q] : (i : GuessRunPhase) → Fintype (GuessRunPhase.CtlState SP SQ Q i)
  | .pre => inferInstanceAs (Fintype SP)
  | .guess => inferInstanceAs (Fintype (NDWriterState Q))
  | .skip => inferInstanceAs (Fintype SeekPhase)
  | .back => inferInstanceAs (Fintype SeekPhase)
  | .run => inferInstanceAs (Fintype SQ)
  | .out => inferInstanceAs (Fintype Bool)

/-- Each phase's state type has decidable equality when the setup's, the run's and the
controller's have. -/
instance GuessRunPhase.instDecidableEqCtlState {SP SQ Q : Type} [DecidableEq SP]
    [DecidableEq SQ] [DecidableEq Q] :
    (i : GuessRunPhase) → DecidableEq (GuessRunPhase.CtlState SP SQ Q i)
  | .pre => inferInstanceAs (DecidableEq SP)
  | .guess => inferInstanceAs (DecidableEq (NDWriterState Q))
  | .skip => inferInstanceAs (DecidableEq SeekPhase)
  | .back => inferInstanceAs (DecidableEq SeekPhase)
  | .run => inferInstanceAs (DecidableEq SQ)
  | .out => inferInstanceAs (DecidableEq Bool)

/-- **The control states of each phase of the guess-then-run host**: those of
`Turing.GuessRunPhase.CtlState` with the trivial controller, the writer's
`Turing.NDWriterState Unit` in the guess phase. -/
def GuessRunPhase.State (SP SQ : Type) : GuessRunPhase → Type :=
  GuessRunPhase.CtlState SP SQ Unit

/-- Each phase's state type is finite when the setup's and the run's are. -/
instance GuessRunPhase.instFintypeState {SP SQ : Type} [Fintype SP] [Fintype SQ] :
    (i : GuessRunPhase) → Fintype (GuessRunPhase.State SP SQ i) :=
  GuessRunPhase.instFintypeCtlState (Q := Unit)

/-- Each phase's state type has decidable equality when the setup's and the run's have. -/
instance GuessRunPhase.instDecidableEqState {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ] :
    (i : GuessRunPhase) → DecidableEq (GuessRunPhase.State SP SQ i) :=
  GuessRunPhase.instDecidableEqCtlState (Q := Unit)

/-- **The phase machines of the guess-then-run host over a writer.** The setup `P` and the run
`V`, as `Turing.MultiTapeTM.toNDTM` (both choices apply their one transition function); the choice
writer `Turing.ndWriterTM` on tape `j` with the controller `q₀`, `δ`, `stop` and the flavor
`bounded`; `Turing.skipTM` and `Turing.skipBackTM` on tape `j`, as `toNDTM`; and the verdict leaf,
which in state `b` emits `b` and halts under either choice, moving no head and writing nothing.
The leaf is hand-built: the construction layer has no public emit-and-halt row for plain machines
(`Turing.OracleTM.answerAction` is the oracle machines' one), so its one transition is written
here, as in the hand-built deciders of the library. -/
def guessCtlRunPhases {k : ℕ} {SP SQ Q : Type} (P : MultiTapeTM k Bool SP) (j : Fin k)
    (q₀ : Q) (δ : Q → Bool → Q) (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ) :
    (i : GuessRunPhase) → NDTM k Bool (GuessRunPhase.CtlState SP SQ Q i)
  | .pre => P.toNDTM
  | .guess => ndWriterTM k j q₀ δ stop bounded
  | .skip => (skipTM k j).toNDTM
  | .back => (skipBackTM k j).toNDTM
  | .run => V.toNDTM
  | .out => ⟨false, fun _ b _ _ => ⟨0, fun _ => (none, 0), some b, none⟩⟩

/-- **The phase machines of the guess-then-run host.** The setup `P` and the run `Q`, as
`Turing.MultiTapeTM.toNDTM` (both choices apply their one transition function); the bounded choice
writer `Turing.ndWriterTM` on tape `j` with the trivial controller that never stops (the instance of
`Turing.ndWriterTM_run_block`): the instance of `Turing.guessCtlRunPhases`; `Turing.skipTM` and
`Turing.skipBackTM` on tape `j`, as `toNDTM`; and the verdict leaf, which in state `b` emits `b` and
halts under either choice, moving no head and writing nothing. The leaf is hand-built: the
construction layer has no public emit-and-halt row for plain machines
(`Turing.OracleTM.answerAction` is the oracle machines' one), so its one transition is written here,
as in the hand-built deciders of the library. -/
def guessRunPhases {k : ℕ} {SP SQ : Type} (P : MultiTapeTM k Bool SP) (j : Fin k)
    (Q : MultiTapeTM k Bool SQ) :
    (i : GuessRunPhase) → NDTM k Bool (GuessRunPhase.State SP SQ i) :=
  guessCtlRunPhases P j () (fun _ _ => ()) (fun _ => false) true Q

/-- **The redirects of the guess-then-run host over a writer.** The setup's exit `pexit`
dispatches to the writer's start `run q₀`; the writer's `done` to the start of the step right;
its `done` to the start of the rewind; the rewind's `done` to the run's entry `qentry`; the run's
verdict `acc` to the leaf's `true`, and `rej` to its `false` (`acc` is tested first). No other
state is redirected, so a halt of the run is the host's halt. Each redirect is one stationary,
silent step of the host under either choice (`Turing.NDTM.phaseHostND`). -/
def guessCtlRunRed {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ] (pexit : SP) (q₀ : Q)
    (qentry acc rej : SQ) :
    (i : GuessRunPhase) → GuessRunPhase.CtlState SP SQ Q i →
      Option (Σ i, GuessRunPhase.CtlState SP SQ Q i)
  | .pre, s => if s = pexit then some ⟨.guess, NDWriterState.run q₀⟩ else none
  | .guess, .done => some ⟨.skip, SeekPhase.run⟩
  | .guess, .run _ => none
  | .skip, .done => some ⟨.back, SeekPhase.run⟩
  | .skip, .run => none
  | .skip, .gap => none
  | .skip, .back => none
  | .back, .done => some ⟨.run, qentry⟩
  | .back, .run => none
  | .back, .gap => none
  | .back, .back => none
  | .run, s => if s = acc then some ⟨.out, true⟩ else if s = rej then some ⟨.out, false⟩
      else none
  | .out, _ => none

/-- **The redirects of the guess-then-run host.** The setup's exit `pexit` dispatches to the
writer's start `run ()`; the writer's `done` to the start of the step right; its `done` to the start
of the rewind; the rewind's `done` to the run's entry `qentry`; the run's verdict `acc` to the
leaf's `true`, and `rej` to its `false` (`acc` is tested first). No other state is redirected, so a
halt of the run is the host's halt. Each redirect is one stationary, silent step of the host under
either choice (`Turing.NDTM.phaseHostND`). The instance of `Turing.guessCtlRunRed` at `q₀ := ()`. -/
def guessRunRed {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ] (pexit : SP)
    (qentry acc rej : SQ) :
    (i : GuessRunPhase) → GuessRunPhase.State SP SQ i →
      Option (Σ i, GuessRunPhase.State SP SQ i) :=
  guessCtlRunRed pexit () qentry acc rej

/-- **The guess-then-run host over a writer.** The nondeterministic phase host
`Turing.NDTM.phaseHostND` over `Turing.guessCtlRunPhases P j q₀ δ stop bounded V` with the
redirects `Turing.guessCtlRunRed pexit q₀ qentry acc rej`, started at the setup's initial state.
The setup `P` runs to its exit `pexit`; the writer guesses bits on tape `j` from that tape's head
until it stops (its controller stops it, or, bounded, it meets a blank); one step right and the
rewind `Turing.skipBackTM` return the head of tape `j` to the stream's start; the run `V` starts at
`qentry` and runs to a live verdict, `acc` or `rej`; the verdict leaf emits `true` or `false` and
halts. Every phase but the writer is deterministic, so a branch is determined by the writer's
bits. The bounded, trivial-controller instance is `Turing.guessRunTM`. [AB09, §2.1.2: an NDTM
writes down a guessed string, then runs a deterministic verifier] -/
def guessCtlRunTM {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) :
    NDTM k Bool (Σ i, GuessRunPhase.CtlState SP SQ Q i) :=
  NDTM.phaseHostND (guessCtlRunPhases P j q₀ δ stop bounded V) ⟨.pre, P.q₀⟩
    (guessCtlRunRed pexit q₀ qentry acc rej)

/-- **The guess-then-run host.** The nondeterministic phase host `Turing.NDTM.phaseHostND` over
`Turing.guessRunPhases P j Q` with the redirects `Turing.guessRunRed pexit qentry acc rej`,
started at the setup's initial state. The setup `P` runs to its exit `pexit`; the bounded choice
writer guesses the block on tape `j` from that tape's head; one step right and the rewind
`Turing.skipBackTM` return the head of tape `j` to the block's start; the run `Q` starts at
`qentry` and runs to a live verdict, `acc` or `rej`; the verdict leaf emits `true` or `false`
and halts. If `Q` halts on its own, so does the host. Every phase but the writer is
deterministic, so a branch is determined by the writer's bits. A composition of the present host
with catalog rows (ruling 2 of the C1 host-contracts gate), not a new host. [AB09, §2.1.2, proof
of Theorem 2.6: an NDTM writes down a guessed string, then runs a deterministic verifier]

It is `Turing.guessCtlRunTM` with the bounded writer and the trivial controller. -/
def guessRunTM {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) : NDTM k Bool (Σ i, GuessRunPhase.State SP SQ i) :=
  guessCtlRunTM P pexit j () (fun _ _ => ()) (fun _ => false) true Q qentry acc rej

/-- **The run's entry configuration after a guess.** The configuration `c` in state `q`, with
the `|s|` cells of tape `j` from its head overwritten by `s`; the input head, every other tape,
every head (that of tape `j` included) and the output are `c`'s. -/
def guessRunCfg {k : ℕ} {S S' : Type} {z : List Bool} (c : Cfg k Bool S z) (j : Fin k)
    (s : List Bool) (q : S') : Cfg k Bool S' z :=
  ⟨some q, c.inputPos,
    Function.update c.workTapes j (fun p =>
      if c.workTapePos j ≤ p ∧ p < c.workTapePos j + s.length then
        FinTM.bufferTape s (p - c.workTapePos j)
      else c.workTapes j p),
    c.workTapePos, c.output⟩

/-! The handoff configuration's fields as equations (the ND inventory API, 2026-10-17), by `simps`
without the `simp` attribute: the state is `some q`, tape `j` holds `s` from its head with every
other cell `c`'s, and the input head, every other tape, every head and the output are `c`'s. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  guessRunCfg

/-- **The interpreter core's start configuration**: state `q`, input head on the first symbol
of `z`, the stream `s` on tape `j` from cell `0`, every other tape blank, every head at `0`,
empty output. It is the configuration `start` of `Turing.exists_ndInterpreterCore`, verbatim. -/
def streamStartCfg {K : ℕ} {S : Type} (z : List Bool) (j : Fin K) (q : S) (s : List Bool) :
    Cfg K Bool S z :=
  ⟨some q, 1, fun i => if i = j then FinTM.bufferTape s else fun _ => none, fun _ => 0, []⟩

/-! The start configuration's fields as equations (the ND inventory API, 2026-10-17), by `simps`
without the `simp` attribute: state `some q`, input head `1`, tape `j` the buffer of `s` and every
other tape blank, every head `0`, output `[]`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  streamStartCfg

/-- A word longer than `L` splits as its first `L` bits, one bit, and the rest. -/
private theorem guessRun_split (L : ℕ) (w : List Bool) (h : L < w.length) :
    ∃ (a : List Bool) (b : Bool) (r : List Bool), w = a ++ [b] ++ r ∧ a.length = L := by
  refine ⟨w.take L, w[L], w.drop (L + 1), ?_, by simp; omega⟩
  rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons h,
    List.take_append_drop]

/-- A writer's endpoint over a renamed configuration, through the renaming's field equations:
`done`, the `m` cells from the head overwritten by `s`, the head after them, every other field
the original's.

**Proof sketch.** Field by field: the state is the update's; the input head and the output are
the original's (`Turing.Cfg.mapState_inputPos`, `_output`); the tapes and heads are the
original's as functions (`Turing.Cfg.mapState_workTapes`, `_workTapePos`), inside the update. -/
private theorem gr_writer_end {k : ℕ} {S Q : Type} {z : List Bool} (cP : Cfg k Bool S z)
    (f : S → NDWriterState Q) (j : Fin k) (s : List Bool) (m : ℕ) :
    ({ cP.mapState f with
        state := some .done
        workTapes := Function.update (cP.mapState f).workTapes j (fun p =>
          if (cP.mapState f).workTapePos j ≤ p ∧ p < (cP.mapState f).workTapePos j + m then
            FinTM.bufferTape s (p - (cP.mapState f).workTapePos j)
          else (cP.mapState f).workTapes j p)
        workTapePos := Function.update (cP.mapState f).workTapePos j
          ((cP.mapState f).workTapePos j + m) } : Cfg k Bool (NDWriterState Q) z) =
      ⟨some .done, cP.inputPos, Function.update cP.workTapes j (fun p =>
          if cP.workTapePos j ≤ p ∧ p < cP.workTapePos j + m then
            FinTM.bufferTape s (p - cP.workTapePos j)
          else cP.workTapes j p),
        Function.update cP.workTapePos j (cP.workTapePos j + m), cP.output⟩ := by
  have hwt : (cP.mapState f).workTapes = cP.workTapes :=
    funext fun i => funext (Cfg.mapState_workTapes f cP i)
  have hwp : (cP.mapState f).workTapePos = cP.workTapePos :=
    funext (Cfg.mapState_workTapePos f cP)
  apply Cfg.ext
  · rfl
  · exact Cfg.mapState_inputPos f cP
  · show Function.update (cP.mapState f).workTapes j _ = _
    rw [hwt, hwp]
  · show Function.update (cP.mapState f).workTapePos j _ = _
    rw [hwp]
  · exact Cfg.mapState_output f cP

/-- The handoff of the guess-then-run host over any writer, given the writer's run on the
word's stream segment: from the setup's dispatch, `m + 1` bits reach `done` with the `m` bits
written from the head and the head after them, and no shorter prefix reaches `done`. Both
writers' contracts give this hypothesis.

**Proof sketch.** Split the word into the setup's `TP` bits and a dispatch bit, the writer's
`m + 1` bits and a dispatch bit, the step right's bit and a dispatch bit, and the rewind's `m + 3`
bits and a dispatch bit. Each phase is one application of `Turing.NDTM.phaseHostND_run`: the
setup's branch is its run (`Turing.MultiTapeTM.toNDTM_runWith`), with no redirect before `TP`;
the writer's branch is the hypothesis, whose second clause is the guard; the step right is
`Turing.skipTM_run_ofCfg` over the empty word (the cell after the stream is blank); the rewind is
`Turing.skipBackTM_run_ofCfg` over the stream (the cells before and after it are blank). Each
phase's endpoint, renamed (`Turing.Cfg.mapState_mapState`), is the next phase's start; the last is
the entry configuration, by the renaming's field equations. -/
private theorem gr_handoff {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ)
    {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (w : List Bool) (hw : w.length = TP + 2 * m + 9)
    (hW : (ndWriterTM k j q₀ δ stop bounded).runWith ((w.drop (TP + 1)).take (m + 1))
        (cP.mapState (fun _ => NDWriterState.run q₀)) =
      ⟨some .done, cP.inputPos, Function.update cP.workTapes j (fun p =>
          if cP.workTapePos j ≤ p ∧ p < cP.workTapePos j + m then
            FinTM.bufferTape ((w.drop (TP + 1)).take m) (p - cP.workTapePos j)
          else cP.workTapes j p),
        Function.update cP.workTapePos j (cP.workTapePos j + m), cP.output⟩)
    (hWg : ∀ u < m + 1, ((ndWriterTM k j q₀ δ stop bounded).runWith
        (((w.drop (TP + 1)).take (m + 1)).take u)
        (cP.mapState (fun _ => NDWriterState.run q₀))).state ≠ some .done) :
    (guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).initCfg z) =
      (guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry).mapState
        (Sigma.mk GuessRunPhase.run) := by
  classical
  -- the five segments of the word
  obtain ⟨a₁, b₁, r₁, rfl, ha₁⟩ := guessRun_split TP w (by omega)
  have hr₁ : r₁.length = 2 * m + 8 := by simp [ha₁] at hw; omega
  obtain ⟨a₂, b₂, r₂, rfl, ha₂⟩ := guessRun_split (m + 1) r₁ (by omega)
  have hr₂ : r₂.length = m + 6 := by simp at hr₁; omega
  obtain ⟨a₃, b₃, r₃, rfl, ha₃⟩ := guessRun_split 1 r₂ (by omega)
  have hr₃ : r₃.length = m + 4 := by simp at hr₂; omega
  obtain ⟨a₄, b₄, r₄, rfl, ha₄⟩ := guessRun_split (m + 3) r₃ (by omega)
  have hr₄ : r₄ = [] := by simp at hr₃; exact List.eq_nil_of_length_eq_zero (by omega)
  subst hr₄
  have hpre : ∀ i ≤ m + 1, ((a₁ ++ [b₁] ++ (a₂ ++ [b₂] ++ (a₃ ++ [b₃] ++ (a₄ ++ [b₄] ++ []))))
      |>.drop (TP + 1) |>.take i) = a₂.take i := by
    intro i hi
    rw [List.drop_left' (by simp [ha₁])]
    rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length (by omega)]
  rw [hpre m (by omega)]
  have hW' := hW
  rw [hpre (m + 1) le_rfl, List.take_of_length_le (show a₂.length ≤ m + 1 by omega),
    hpre m (by omega)] at hW'
  have hWg' : ∀ u < m + 1, ((ndWriterTM k j q₀ δ stop bounded).runWith (a₂.take u)
      (cP.mapState (fun _ => NDWriterState.run q₀))).state ≠ some .done := fun u hu => by
    have := hWg u hu
    rwa [hpre (m + 1) le_rfl, List.take_of_length_le (show a₂.length ≤ m + 1 by omega)] at this
  set s := a₂.take m with hs_def
  have hslen : s.length = m := by simp [s, ha₂]
  set M := guessCtlRunPhases P j q₀ δ stop bounded V
  set red := guessCtlRunRed pexit q₀ qentry acc rej
  have hN : guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej =
      NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red := rfl
  rw [hN]
  set H := NDTM.phaseHostND M ⟨GuessRunPhase.pre, P.q₀⟩ red with hH
  have hinit : H.initCfg z = (P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre) := by
    rw [NDTM.initCfg_eq, MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.init_state, Cfg.init_state, Option.map_some]
      rfl
    · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
    · funext i p
      rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext i
      rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  -- phase 1: the setup, then one dispatch
  have h1 : H.runWith (a₁ ++ [b₁]) ((P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre)) =
      cP.mapState (fun _ =>
        (⟨.guess, NDWriterState.run q₀⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) := by
    refine (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.pre (P.initCfg z) cP a₁ ?_
      pexit hPexit _ ?_ ?_ b₁).2
    · show P.toNDTM.runWith a₁ (P.initCfg z) = cP
      rw [MultiTapeTM.toNDTM_runWith, ha₁, hP]
    · show (if pexit = pexit then _ else none) = _
      simp
    · intro u hu s' hs'
      change (P.toNDTM.runWith (a₁.take u) (P.initCfg z)).state = some s' at hs'
      rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hs'
      have hne := hPfirst u (by omega)
      show (if s' = pexit then _ else none) = none
      rw [if_neg]
      rintro rfl
      exact hne hs'
  -- phase 2: the controller-stopped writer, then one dispatch
  let cW : Cfg k Bool (NDWriterState Q) z := cP.mapState (fun _ => NDWriterState.run q₀)
  have hcW : cP.mapState (fun _ =>
      (⟨.guess, NDWriterState.run q₀⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) =
      cW.mapState (Sigma.mk GuessRunPhase.guess) := by
    rw [Cfg.mapState_mapState]; rfl
  -- the writer's endpoint, named, through the renaming's field equations
  let tW : ℤ → Option Bool := fun p =>
    if cP.workTapePos j ≤ p ∧ p < cP.workTapePos j + (m : ℤ) then
      FinTM.bufferTape s (p - cP.workTapePos j)
    else cP.workTapes j p
  let cW' : Cfg k Bool (NDWriterState Q) z :=
    ⟨some .done, cP.inputPos, Function.update cP.workTapes j tW,
      Function.update cP.workTapePos j (cP.workTapePos j + m), cP.output⟩
  have hX : (ndWriterTM k j q₀ δ stop bounded).runWith a₂ cW = cW' := hW'
  have h2 := (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.guess cW cW' a₂ hX
    NDWriterState.done rfl ⟨.skip, SeekPhase.run⟩ rfl (by
      intro u hu s' hs'
      cases s' with
      | done => exact absurd hs' (hWg' u (by omega))
      | run _ => rfl) b₂).2
  -- phase 3: one step right, onto the cell after the stream's right blank, then one dispatch
  let cS : Cfg k Bool SeekPhase z := cW'.mapState (fun _ => SeekPhase.run)
  have hcS : cW'.mapState (fun _ =>
      (⟨.skip, SeekPhase.run⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) =
      cS.mapState (Sigma.mk GuessRunPhase.skip) := by
    rw [Cfg.mapState_mapState]; rfl
  have hS := skipTM_run_ofCfg (x := z) j ([] : List Bool) cS
    (by simp only [cS, Cfg.mapState_state]; rfl) (by
    intro p h0 h1
    have hp : p = 0 := by simp at h1; omega
    subst hp
    simp [cS, cW', tW, Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hend])
  let cS' : Cfg k Bool SeekPhase z :=
    { cS with
      state := some .done
      workTapePos := Function.update cS.workTapePos j
        (cS.workTapePos j + ([] : List Bool).length + 1) }
  have h3 := (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.skip cS cS' a₃ (by
      show (skipTM k j).toNDTM.runWith a₃ cS = cS'
      rw [MultiTapeTM.toNDTM_runWith, ha₃]
      exact hS.1)
    SeekPhase.done rfl ⟨.back, SeekPhase.run⟩ rfl (by
      intro u hu s' hs'
      change ((skipTM k j).toNDTM.runWith (a₃.take u) cS).state = some s' at hs'
      rw [MultiTapeTM.toNDTM_runWith] at hs'
      have hne := hS.2.1 (a₃.take u).length (by simp; omega)
      cases s' with
      | done => exact absurd hs' hne
      | run => rfl
      | gap => rfl
      | back => rfl) b₃).2
  -- phase 4: the rewind over the guessed stream, then one dispatch into the deterministic run
  let cB : Cfg k Bool SeekPhase z := cS'.mapState (fun _ => SeekPhase.run)
  have hcB : cS'.mapState (fun _ =>
      (⟨.back, SeekPhase.run⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) =
      cB.mapState (Sigma.mk GuessRunPhase.back) := by
    rw [Cfg.mapState_mapState]; rfl
  have hBpos : cB.workTapePos j = cP.workTapePos j + m + 1 := by
    simp [cB, cS', cS, cW', Cfg.mapState_inputPos, Cfg.mapState_workTapePos,
      Cfg.mapState_output]
  have hB := skipBackTM_run_ofCfg (x := z) j s cB
    (by simp only [cB, Cfg.mapState_state]; rfl) (by
    intro p h0 h1
    rw [hBpos, hslen]
    have harg : cP.workTapePos j + m + 1 - m - 1 + p = cP.workTapePos j + p := by ring
    rw [harg]
    simp only [cB, cS', cS, cW', Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      Function.update_self]
    simp only [tW]
    by_cases hin : 0 ≤ p ∧ p < (m : ℤ)
    · rw [if_pos (by omega)]
      congr 1
      ring
    · rw [if_neg (by omega)]
      rw [hslen] at h1
      rcases (show p = -1 ∨ p = (m : ℤ) by omega) with rfl | rfl
      · rw [FinTM.bufferTape_left, ← hleft]
        congr 1
      · rw [hend, FinTM.bufferTape_nat, List.getElem?_eq_none (by omega)])
  let cB' : Cfg k Bool SeekPhase z :=
    { cB with
      state := some .done
      workTapePos := Function.update cB.workTapePos j (cB.workTapePos j - s.length - 1) }
  have h4 := (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.back cB cB' a₄ (by
      show (skipBackTM k j).toNDTM.runWith a₄ cB = cB'
      rw [MultiTapeTM.toNDTM_runWith, ha₄, ← hslen]
      exact hB.1)
    SeekPhase.done rfl ⟨.run, qentry⟩ rfl (by
      intro u hu s' hs'
      change ((skipBackTM k j).toNDTM.runWith (a₄.take u) cB).state = some s' at hs'
      rw [MultiTapeTM.toNDTM_runWith] at hs'
      have hne := hB.2.1 (a₄.take u).length (by simp; omega)
      cases s' with
      | done => exact absurd hs' hne
      | run => rfl
      | gap => rfl
      | back => rfl) b₄).2
  -- the chain
  rw [hinit, NDTM.runWith_append, h1, hcW, NDTM.runWith_append, h2]
  erw [hcS]
  rw [NDTM.runWith_append, h3]
  erw [hcB]
  rw [List.append_nil, h4]
  apply Cfg.ext
  · simp only [cB', Cfg.mapState_state, guessRunCfg_state, Option.map_some]
  · simp only [cB', cB, cS', cS, cW', Cfg.mapState_inputPos, guessRunCfg_inputPos]
  · funext i p
    simp only [cB', cB, cS', cS, cW', tW, Cfg.mapState_workTapes, guessRunCfg_workTapes, hslen]
  · funext i
    simp only [cB', cB, cS', cS, cW', Cfg.mapState_workTapePos, guessRunCfg_workTapePos,
      Function.update_apply, hslen, List.length_nil]
    split_ifs with h
    · subst h
      omega
    · rfl
  · simp only [cB', cB, cS', cS, cW', Cfg.mapState_output, guessRunCfg_output]


/-- The rest of a branch of the guess-then-run host over any writer, from its handoff: the run
`V` up to its first verdict, one dispatch, and the verdict leaf; later choices are absorbed.

**Proof sketch.** `Turing.NDTM.phaseHostND_run` for the run phase: its branch is the
deterministic run (`Turing.MultiTapeTM.toNDTM_runWith`), its first verdict the redirected exit,
and the earlier states, none a verdict, the guard. One step of the verdict leaf
(`Turing.NDTM.stepWith_of_some` and the action's field equations) emits the bit and halts, and
absorption (`Turing.NDTM.runWith_of_halt`) takes the remaining choices. -/
private theorem gr_runWith_of_handoff {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (bounded : Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ)
    {z : List Bool} (cP : Cfg k Bool SP z) (s : List Bool) (TQ : ℕ)
    (hverd : (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
      (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej)
    (hfirst : ∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
      (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (L : ℕ) (w : List Bool)
    (hH : (guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).runWith (w.take L)
        ((guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).initCfg z) =
      (guessRunCfg cP j s qentry).mapState (Sigma.mk GuessRunPhase.run))
    (hw : L + TQ + 2 ≤ w.length) :
    let d := V.runFrom (guessRunCfg cP j s qentry) TQ
    (guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej).initCfg z) =
      ⟨none, d.inputPos, d.workTapes, d.workTapePos,
        d.output ++ [decide (d.state = some acc)]⟩ := by
  intro d
  set M := guessCtlRunPhases P j q₀ δ stop bounded V
  set red := guessCtlRunRed pexit q₀ qentry acc rej
  have hN : guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej =
      NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red := rfl
  rw [← List.take_append_drop L w, NDTM.runWith_append, hH, hN]
  -- the deterministic run up to its verdict, then one dispatch into the verdict leaf
  obtain ⟨a, b, r, hv, ha⟩ := guessRun_split TQ (w.drop L) (by simp; omega)
  have hr : 1 ≤ r.length := by
    have := congrArg List.length hv
    simp [ha] at this
    omega
  obtain ⟨b', r', rfl⟩ : ∃ b' r', r = b' :: r' := by
    cases r with
    | nil => simp at hr
    | cons b' r' => exact ⟨b', r', rfl⟩
  obtain ⟨sv, hsv, hred⟩ : ∃ sv, d.state = some sv ∧
      red GuessRunPhase.run sv = some ⟨.out, decide (d.state = some acc)⟩ := by
    rcases hverd with h | h
    · have h' : d.state = some acc := h
      exact ⟨acc, h', by simp [red, guessCtlRunRed, h']⟩
    · have h' : d.state = some rej := h
      by_cases hra : rej = acc
      · subst hra
        exact ⟨rej, h', by simp [red, guessCtlRunRed, h']⟩
      · exact ⟨rej, h', by simp [red, guessCtlRunRed, h', hra]⟩
  have hQ := (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.run
    (guessRunCfg cP j s qentry) d a (by
      show V.toNDTM.runWith a (guessRunCfg cP j s qentry) = d
      rw [MultiTapeTM.toNDTM_runWith, ha]) sv hsv _ hred (by
      intro u hu s' hs'
      change (V.toNDTM.runWith (a.take u) (guessRunCfg cP j s qentry)).state = some s' at hs'
      rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hs'
      have hne := hfirst u (by omega)
      show (if s' = acc then _ else if s' = rej then _ else none) = none
      rw [if_neg (fun h => hne.1 (by rw [← h]; exact hs')),
        if_neg (fun h => hne.2 (by rw [← h]; exact hs'))]) b).2
  rw [hv, NDTM.runWith_append, hQ, NDTM.runWith_cons]
  -- the verdict leaf emits the verdict bit and halts; the rest of the word is absorbed
  have hout : (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).stepWith b'
      (d.mapState (fun _ => (⟨.out, decide (d.state = some acc)⟩ :
        Σ i, GuessRunPhase.CtlState SP SQ Q i))) =
      ⟨none, d.inputPos, d.workTapes, d.workTapePos,
        d.output ++ [decide (d.state = some acc)]⟩ := by
    have hst : (d.mapState (fun _ => (⟨.out, decide (d.state = some acc)⟩ :
        Σ i, GuessRunPhase.CtlState SP SQ Q i))).state =
        some ⟨.out, decide (d.state = some acc)⟩ := by
      rw [Cfg.mapState_state, hsv]
      rfl
    rw [NDTM.stepWith_of_some hst]
    have hwt : ∀ i, (d.mapState (fun _ => (⟨.out, decide (d.state = some acc)⟩ :
        Σ i, GuessRunPhase.CtlState SP SQ Q i))).workTapes i = d.workTapes i := fun i =>
      funext (Cfg.mapState_workTapes _ d i)
    apply Cfg.ext <;> (try funext i) <;> (try funext p) <;>
      simp only [NDTM.phaseHostND, red, guessCtlRunRed, M, guessCtlRunPhases, hwt,
        Action.apply_state, Action.apply_inputPos, Action.apply_workTapes, Action.apply_workTapePos,
        Action.apply_output, Action.mapState_state, Action.mapState_inputTape,
        Action.mapState_workTapes, Action.mapState_output, Cfg.mapState_inputPos,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
        Cfg.workTapeSymbols_eq, Function.update_eq_self, moveInputPos_zero, Option.map_none,
        Option.toList_some, Option.getD_none, SignType.coe_zero, add_zero]
  erw [hout]
  rw [NDTM.runWith_of_halt _ rfl]


/-- **Through the guess and the rewind.** Let the setup `P` run from its initial configuration on
`z` to `cP` at time `TP`, at its exit `pexit` and not at `pexit` before, with a nonblank block of
`m` cells of tape `j` from its head, a blank just after the block and a blank just before it.
Then every choice word `w` of length `TP + 2m + 9` drives the host to the run's entry
configuration `Turing.guessRunCfg cP j s qentry`, tagged by the run phase, where `s` is the `m`
bits of `w` after its first `TP + 1`: the block holds `s`, the head of tape `j` is back at the
block's start, and every other field is `cP`'s. The time is `TP` for the setup, `1` per dispatch
(four), `m + 1` for the writer, `1` for the step right and `m + 3` for the rewind. The first
`TP + 1` bits and the writer's last bit are ignored, and every stream of length `m` is the
stream of some word. [AB09, §2.1.2, proof of Theorem 2.6]

**Proof sketch.** Split `w` into the setup's `TP` bits and a dispatch bit, the writer's `m + 1`
bits and a dispatch bit, the step right's bit and a dispatch bit, and the rewind's `m + 3` bits
and a dispatch bit. Each phase is one application of `Turing.NDTM.phaseHostND_run`. The setup's
branch is its run (`Turing.MultiTapeTM.toNDTM_runWith`), with no redirect before `TP`. The
writer's branch is `Turing.ndWriterTM_run_block`, whose second clause is the guard. The step right
is `Turing.skipTM_run_ofCfg` over the empty word (the cell after the block is blank). The rewind
is `Turing.skipBackTM_run_ofCfg` over `s` (the cells before and after the block are blank). Each
phase's endpoint, renamed, is the next phase's start; the last is the entry configuration, the
head of tape `j` restored. -/
theorem guessRunTM_runWith_handoff {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (w : List Bool) (hw : w.length = TP + 2 * m + 9) :
    (guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z) =
      (guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry).mapState
        (Sigma.mk GuessRunPhase.run) := by
  have hst : (cP.mapState (fun _ => NDWriterState.run ())).state = some (NDWriterState.run ()) := by
    rw [Cfg.mapState_state, hPexit]; rfl
  obtain ⟨hW1, hW2⟩ := ndWriterTM_run_block j (cP.mapState (fun _ => NDWriterState.run ())) hst m
    (fun p hp => by rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]; exact hblock p hp)
    (by rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]; exact hend)
    ((w.drop (TP + 1)).take (m + 1)) (by simp; omega)
  rw [List.take_take, Nat.min_eq_left (by omega)] at hW1
  refine gr_handoff P pexit j () (fun _ _ => ()) (fun _ => false) true Q qentry acc rej TP cP hP
    hPexit hPfirst m hend hleft w hw ?_ ?_
  · rw [hW1, gr_writer_end]
  · intro u hu
    exact hW2 _ (by simp; omega)

/-- **No branch halts before the handoff.** Under the setup hypotheses of
`Turing.guessRunTM_runWith_handoff`, every choice word shorter than `TP + 2m + 9` leaves the host
live. So a budget below the handoff time accepts nothing, whatever the run does.

**Proof sketch.** Pad the word to length `TP + 2m + 9`. If its branch had halted, absorption
(`Turing.NDTM.runWith_of_halt`) would keep it halted, but the padded word reaches the live entry
configuration (`Turing.guessRunTM_runWith_handoff`). -/
theorem guessRunTM_runWith_live {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (w : List Bool) (hw : w.length < TP + 2 * m + 9) :
    ((guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z)).state ≠ none := by
  intro h
  have hh := guessRunTM_runWith_handoff P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m
    hblock hend hleft (w ++ List.replicate (TP + 2 * m + 9 - w.length) false)
    (by simp; omega)
  rw [NDTM.runWith_append, NDTM.runWith_of_halt _ h] at hh
  rw [hh] at h
  simp [guessRunCfg, Cfg.mapState] at h

/-- **At the handoff the host is live, at the run's entry.** Under the setup hypotheses of
`Turing.guessRunTM_runWith_handoff`, every choice word of length exactly `TP + 2m + 9` leaves the
host in the state `⟨run, qentry⟩`: live, and at the run's entry. With
`Turing.guessRunTM_runWith_live` (every shorter word), the host is live at every length up to
the handoff.

**Proof sketch.** The state field of the configuration that
`Turing.guessRunTM_runWith_handoff` gives. -/
theorem guessRunTM_runWith_handoff_state {k : ℕ} {SP SQ : Type} [DecidableEq SP]
    [DecidableEq SQ] (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k)
    (Q : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool} (TP : ℕ)
    (cP : Cfg k Bool SP z) (hP : P.runFrom (P.initCfg z) TP = cP)
    (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (w : List Bool) (hw : w.length = TP + 2 * m + 9) :
    ((guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z)).state =
      some ⟨GuessRunPhase.run, qentry⟩ := by
  rw [guessRunTM_runWith_handoff P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m hblock
    hend hleft w hw]
  rfl

/-- **The whole branch.** Under the setup hypotheses of `Turing.guessRunTM_runWith_handoff`,
let `s` be a stream of length `m`, and let the run `Q` from the entry configuration
`Turing.guessRunCfg cP j s qentry` reach a verdict state, `acc` or `rej`, first at time `TQ`, in
the configuration `d`. Then every choice word whose `m` bits after its first `TP + 1` are `s`,
of length at least `TP + 2m + TQ + 11`, halts the host with `d`'s input head, tapes and heads, and
with output `d`'s output followed by the verdict bit (`true` iff `d` is at `acc`). The branch
is halted by time `TP + 2m + TQ + 11`: the handoff, the run, one dispatch and the leaf's
emitting step.
Choices after the stream are ignored. The run's own emissions stay in the output; capturing them
is the caller's choice (`Turing.guessRunTM_silent_spec`). [AB09, §2.1.2]

**Proof sketch.** `Turing.guessRunTM_runWith_handoff` on the first `TP + 2m + 9` bits. Then
`Turing.NDTM.phaseHostND_run` for the run phase: its branch is the deterministic run
(`Turing.MultiTapeTM.toNDTM_runWith`), its first verdict the redirected exit, and the earlier
states, none a verdict, the guard. One step of the verdict leaf emits the bit and halts, and
absorption (`Turing.NDTM.runWith_of_halt`) takes the remaining choices. -/
theorem guessRunTM_runWith {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (s : List Bool) (hs : s.length = m) (TQ : ℕ)
    (hverd : (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
      (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej)
    (hfirst : ∀ u < TQ, (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
      (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (w : List Bool) (hws : (w.drop (TP + 1)).take m = s)
    (hw : TP + 2 * m + TQ + 11 ≤ w.length) :
    let d := Q.runFrom (guessRunCfg cP j s qentry) TQ
    (guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z) =
      ⟨none, d.inputPos, d.workTapes, d.workTapePos,
        d.output ++ [decide (d.state = some acc)]⟩ := by
  -- through the guess and the rewind
  have hH := guessRunTM_runWith_handoff P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m
    hblock hend hleft (w.take (TP + 2 * m + 9)) (by simp; omega)
  have hs' : ((w.take (TP + 2 * m + 9)).drop (TP + 1)).take m = s := by
    rw [← hws, List.drop_take, List.take_take]
    congr 1
    omega
  rw [hs'] at hH
  exact gr_runWith_of_handoff P pexit j () (fun _ _ => ()) (fun _ => false) true Q qentry acc rej
    cP s TQ hverd hfirst (TP + 2 * m + 9) w hH (by omega)

/-- **A setup that halts before its exit.** If the setup `P` halts on `z` at time `TP` without
being at its exit `pexit` before, then every choice word of length at least `TP` leaves the host
in `P`'s halted configuration, tagged by the setup phase: the host halts without guessing, with
`P`'s output. (For inputs that a consumer rejects outright, such as the diagonalizer's non-unary
inputs.) [AB09, §2.1.2]

**Proof sketch.** `Turing.NDTM.runWith_mapState_of_agreeOn_det` with `P` as the deterministic
source along the setup phase's tag, the good states being those other than `pexit`, where the
host redirects nothing and so follows `P`'s transitions, renamed; then absorption
(`Turing.NDTM.runWith_of_halt`) takes the remaining choices. -/
theorem guessRunTM_runWith_setup_halt {k : ℕ} {SP SQ : Type} [DecidableEq SP]
    [DecidableEq SQ] (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k)
    (Q : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool} (TP : ℕ)
    (hhalt : (P.runFrom (P.initCfg z) TP).state = none)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (w : List Bool) (hw : TP ≤ w.length) :
    (guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z) =
      (P.runFrom (P.initCfg z) TP).mapState (Sigma.mk GuessRunPhase.pre) := by
  set M := guessRunPhases P j Q
  set red := guessRunRed pexit qentry acc rej
  have hN : guessRunTM P pexit j Q qentry acc rej = NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red := rfl
  rw [hN]
  let emb : SP ↪ (Σ i, GuessRunPhase.State SP SQ i) :=
    ⟨fun s => ⟨GuessRunPhase.pre, s⟩, fun a b h => sigma_mk_injective h⟩
  have hpre := NDTM.runWith_mapState_of_agreeOn_det P (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red) emb
    (fun s => s ≠ pexit) (by
      intro b s hs inp work
      have hr : red GuessRunPhase.pre s = none := by
        show (if s = pexit then _ else none) = none
        rw [if_neg hs]
      change (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).tr b ⟨GuessRunPhase.pre, s⟩ inp work = _
      simp only [NDTM.phaseHostND, hr]
      rfl)
    (P.initCfg z) (w.take TP) (by
      intro u hu s hs
      rw [List.length_take, Nat.min_eq_left hw] at hu
      rintro rfl
      exact hPfirst u hu hs)
  rw [List.length_take, Nat.min_eq_left hw] at hpre
  rw [← List.take_append_drop TP w, NDTM.runWith_append]
  erw [hpre]
  rw [NDTM.runWith_of_halt _ (by
    show Option.map _ (P.runFrom (P.initCfg z) TP).state = none
    rw [hhalt]
    rfl)]
  rfl

/-- **All-branch halting.** Under the setup hypotheses of
`Turing.guessRunTM_runWith_handoff`, if for every stream `s` of length `m` the run from the entry
configuration `Turing.guessRunCfg cP j s qentry` reaches a verdict first at some time at most
`T`, then every branch of the host on `z` halts within `TP + 2m + T + 11`
(`Turing.NDTM.HaltsWithin`). [AB09, §2.1.2: every branch halts within the bound]

**Proof sketch.** A word of that length has some stream as its `m` bits after its first
`TP + 1`; `Turing.guessRunTM_runWith` at that stream's verdict time gives a halted branch. -/
theorem guessRunTM_haltsWithin {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none) (T : ℕ)
    (hQ : ∀ s : List Bool, s.length = m → ∃ TQ ≤ T,
      ((Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
        (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej) ∧
      ∀ u < TQ, (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
        (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej) :
    (guessRunTM P pexit j Q qentry acc rej).HaltsWithin z (TP + 2 * m + T + 11) := by
  intro w hw
  obtain ⟨TQ, hTQ, hv, hf⟩ := hQ ((w.drop (TP + 1)).take m) (by simp; omega)
  rw [guessRunTM_runWith P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m hblock hend
    hleft _ (by simp; omega) TQ hv hf w rfl (by omega)]

/-- **Exact-budget acceptance, both directions.** Under the hypotheses of
`Turing.guessRunTM_haltsWithin`, at every budget `B` at least `TP + 2m + T + 11`: some choice word
of length exactly `B` halts the host with output exactly `[true]` (the shape of
`Turing.FinNDTM.AcceptsWithin`) iff some stream `s` of length `m` makes the run's first verdict
`acc`, with an empty output at that time. A stream whose first verdict state is `rej` and
different from `acc`, or whose run's output (the setup's emissions included) is nonempty at the
verdict, gives no accepting branch; when `acc = rej` that verdict accepts, since the leaf tests
`acc` first.
[AB09, §2.1.2, proof of Theorem 2.6]

**Proof sketch.** Forward: take the accepting word's stream; by `Turing.guessRunTM_runWith` at
that stream's verdict time, the output is the run's output followed by the verdict bit, which is
`[true]` only if the run's output is empty and the verdict is `acc`. Backward: the word made of
`TP + 1` bits `false`, then `s`, then `false` up to length `B`, has stream `s`; the first verdict
time is unique, hence at most `T`, and `Turing.guessRunTM_runWith` gives the output
`[] ++ [true]`. -/
theorem guessRunTM_accepts_iff {k : ℕ} {SP SQ : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (Q : MultiTapeTM k Bool SQ)
    (qentry acc rej : SQ) {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (m : ℕ) (hblock : ∀ p : ℕ, p < m → cP.workTapes j (cP.workTapePos j + p) ≠ none)
    (hend : cP.workTapes j (cP.workTapePos j + m) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none) (T : ℕ)
    (hQ : ∀ s : List Bool, s.length = m → ∃ TQ ≤ T,
      ((Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
        (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej) ∧
      ∀ u < TQ, (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
        (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (B : ℕ) (hB : TP + 2 * m + T + 11 ≤ B) :
    (∃ w : List Bool, w.length = B ∧
      ((guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z)).state = none ∧
      ((guessRunTM P pexit j Q qentry acc rej).runWith w
        ((guessRunTM P pexit j Q qentry acc rej).initCfg z)).output = [true]) ↔
    ∃ s : List Bool, s.length = m ∧ ∃ TQ : ℕ,
      (Q.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∧
      (∀ u < TQ, (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
        (Q.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej) ∧
      (Q.runFrom (guessRunCfg cP j s qentry) TQ).output = [] := by
  constructor
  · rintro ⟨w, hw, -, hout⟩
    have hslen : ((w.drop (TP + 1)).take m).length = m := by simp; omega
    obtain ⟨TQ, hTQ, hv, hf⟩ := hQ _ hslen
    rw [guessRunTM_runWith P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m hblock hend
      hleft _ hslen TQ hv hf w rfl (by omega)] at hout
    have hlen := congrArg List.length hout
    simp only [List.length_append, List.length_singleton] at hlen
    have hnil : (Q.runFrom (guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry) TQ).output =
        [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil, List.nil_append, List.singleton_inj, decide_eq_true_iff] at hout
    exact ⟨_, hslen, TQ, hout, hf, hnil⟩
  · rintro ⟨s, hslen, TQ', hacc, hf', hnil⟩
    obtain ⟨TQ, hTQ, hv, hf⟩ := hQ s hslen
    have heq : TQ' = TQ := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact (hf TQ' h).1 hacc
      · rcases hv with hv | hv
        · exact (hf' TQ h).1 hv
        · exact (hf' TQ h).2 hv
    subst heq
    let w := List.replicate (TP + 1) false ++ s ++ List.replicate (B - (TP + 1 + m)) false
    have hwlen : w.length = B := by simp [w, hslen]; omega
    have hws : (w.drop (TP + 1)).take m = s := by
      simp only [w, List.append_assoc]
      rw [List.drop_left' (by simp), List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    refine ⟨w, hwlen, ?_⟩
    rw [guessRunTM_runWith P pexit j Q qentry acc rej TP cP hP hPexit hPfirst m hblock hend
      hleft s hslen TQ' (Or.inl hacc) hf' w hws (by omega)]
    simp [hacc, hnil]

/-- **The core's precondition at the handoff.** Let the setup end clean: in a state `q`, with
the input head on the first symbol, every tape blank except tape `ι jR`, which holds a block `blk`
blank outside the cells `0, …, m - 1`, every head at `0`, and an empty output. Then, for every
stream `s` of length `m`, the run's entry configuration in state `entry` is the core's start
configuration `Turing.streamStartCfg z jR entry s`, silently embedded along `ι` with the capture
tape `cap` outside the selection (`Turing.embedSilentCfg` with a blank frame, heads at `0`, an
empty capture word and an empty host output). This is the clean-bank, head and output
precondition of `Turing.exists_ndInterpreterCore`, delivered by the guess and the rewind.

**Proof sketch.** Field by field. The state and the input head are `entry` and `1` on both
sides. A selected tape `ι a` is the core's tape `a` (`Turing.embedSilentCfg_selected_tape`): at
`a = jR` the overwritten block is `bufferTape s`, since `blk` is blank outside the block and so is
`bufferTape s`; elsewhere both are blank. The capture tape holds the empty capture word with its
head at `0` (`Turing.embedSilentCfg_cap`); every other unselected tape is the blank frame
(`Turing.embedSilentTM_frame` at time `0`). Heads are `0`; outputs are
empty. -/
theorem guessRunCfg_clean {K k : ℕ} {SP SR : Type} {z : List Bool} (ι : Fin K ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (jR : Fin K) (blk : ℤ → Option Bool) (m : ℕ)
    (hblk : ∀ p : ℤ, (p < 0 ∨ (m : ℤ) ≤ p) → blk p = none) (q : SP) (entry : SR)
    (s : List Bool) (hs : s.length = m) :
    guessRunCfg (⟨some q, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ :
        Cfg k Bool SP z) (ι jR) s entry =
      embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (streamStartCfg z jR entry s) := by
  classical
  -- a one-state machine whose frame lemma at time `0` reads the unselected tapes
  let M0 : MultiTapeTM K Bool SR :=
    ⟨entry, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  have hframe := (embedSilentTM_frame ι cap hcap M0 (fun _ _ => none) (fun _ => 0) [] []
    (streamStartCfg z jR entry s) 0).1
  simp only [MultiTapeTM.runFrom_zero] at hframe
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hi
      rw [embedSilentCfg_selected_tape]
      simp only [guessRunCfg, streamStartCfg]
      by_cases ha : a = jR
      · subst ha
        rw [Function.update_self, if_pos rfl]
        funext p
        simp only [Function.update_self, zero_add, sub_zero, hs]
        by_cases hp : 0 ≤ p ∧ p < (m : ℤ)
        · rw [if_pos hp]
        · rw [if_neg hp, hblk p (by omega)]
          simp only [FinTM.bufferTape]
          split_ifs with h0
          · symm
            exact List.getElem?_eq_none (by rw [hs]; omega)
          · rfl
      · have hne : ι a ≠ ι jR := fun h => ha (ι.injective h)
        rw [Function.update_of_ne hne, Function.update_of_ne hne, if_neg ha]
    · by_cases hc : i = cap
      · subst hc
        have hne : i ≠ ι jR := fun h => hi ⟨jR, h.symm⟩
        simp only [guessRunCfg, Function.update_of_ne hne]
        -- the capture tape holds the empty capture word
        rw [(embedSilentCfg_cap ι i hcap (fun _ _ => none) (fun _ => 0) [] []
          (streamStartCfg z jR entry s)).1]
        simp [streamStartCfg]
      · have hne : i ≠ ι jR := fun h => hi ⟨jR, h.symm⟩
        simp only [guessRunCfg, Function.update_of_ne hne]
        exact ((hframe i hi hc).1).symm
  · funext i
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hi
      rw [embedSilentCfg_selected_pos]
      rfl
    · by_cases hc : i = cap
      · subst hc
        -- the capture head sits after the empty capture word
        rw [(embedSilentCfg_cap ι i hcap (fun _ _ => none) (fun _ => 0) [] []
          (streamStartCfg z jR entry s)).2]
        simp [guessRunCfg, streamStartCfg]
      · exact ((hframe i hi hc).2).symm
  · rfl

/-- **Guess, then run the interpreter core** (the assembly `Turing.exists_timed_universal_NDTM`'s
sketch names). Let `R` be a `K`-tape machine with an entry state `entry` and live verdicts `acc`
and `rej`, run silently on the host tapes selected by `ι`, its emissions captured on a tape
`cap` outside the selection (`Turing.embedSilentTM`). Let the setup `P` reach its exit `pexit`
first at time `TP`, clean: input head on the first symbol, every tape blank except tape `ι jR`,
which is nonblank exactly at the cells `0, …, m - 1`, every head at `0`, empty output. Suppose
that for every stream `s` of length `m`, `R` from its start configuration
`Turing.streamStartCfg z jR entry s` reaches a verdict first within `T`. Then the host `N` halts
on every branch within `TP + 2m + T + 11`, and at every budget `B` at least that, `N` has a branch
of length exactly `B` halting with output exactly `[true]` iff some stream `s` of length `m`
makes `R`'s first verdict `acc`. `R`'s own output is never examined: the capture makes the host's
output exactly the verdict bit. [AB09, §2.1.2, proof of Theorem 2.6; Exercise 2.6]

**Proof sketch.** The setup's endpoint satisfies the block hypotheses of
`Turing.guessRunTM_runWith_handoff` (nonblank inside the block, blank at `m` and at `-1`). By
`Turing.guessRunCfg_clean` the entry configuration is `R`'s start, silently embedded, so the
run's states are `R`'s and its output stays empty (`Turing.embedSilentTM_runFrom`). Conclude by
`Turing.guessRunTM_haltsWithin` and `Turing.guessRunTM_accepts_iff`, whose output condition then
holds. -/
theorem guessRunTM_silent_spec {K k : ℕ} {SP SR : Type} [DecidableEq SP] [DecidableEq SR]
    (ι : Fin K ↪ Fin k) (cap : Fin k) (hcap : cap ∉ Set.range ι) (jR : Fin K)
    (R : MultiTapeTM K Bool SR) (entry acc rej : SR)
    (P : MultiTapeTM k Bool SP) (pexit : SP) {z : List Bool} (TP m : ℕ)
    (blk : ℤ → Option Bool) (hblk : ∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < m)
    (hP : P.runFrom (P.initCfg z) TP =
      ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit) (T : ℕ)
    (hR : ∀ s : List Bool, s.length = m → ∃ TR ≤ T,
      ((R.runFrom (streamStartCfg z jR entry s) TR).state = some acc ∨
        (R.runFrom (streamStartCfg z jR entry s) TR).state = some rej) ∧
      ∀ u < TR, (R.runFrom (streamStartCfg z jR entry s) u).state ≠ some acc ∧
        (R.runFrom (streamStartCfg z jR entry s) u).state ≠ some rej) :
    let N := guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej
    N.HaltsWithin z (TP + 2 * m + T + 11) ∧
      ∀ B : ℕ, TP + 2 * m + T + 11 ≤ B →
        ((∃ w : List Bool, w.length = B ∧ (N.runWith w (N.initCfg z)).state = none ∧
            (N.runWith w (N.initCfg z)).output = [true]) ↔
          ∃ s : List Bool, s.length = m ∧ ∃ TR : ℕ,
            (R.runFrom (streamStartCfg z jR entry s) TR).state = some acc ∧
            ∀ u < TR, (R.runFrom (streamStartCfg z jR entry s) u).state ≠ some acc ∧
              (R.runFrom (streamStartCfg z jR entry s) u).state ≠ some rej) := by
  intro N
  set cP : Cfg k Bool SP z :=
    ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ with hcP
  have hout : ∀ p : ℤ, (p < 0 ∨ (m : ℤ) ≤ p) → blk p = none := by
    intro p hp
    by_contra h
    have := (hblk p).mp h
    omega
  have hblock : ∀ p : ℕ, p < m → cP.workTapes (ι jR) (cP.workTapePos (ι jR) + p) ≠ none := by
    intro p hp
    simp only [cP, Function.update_self, zero_add]
    exact (hblk p).mpr ⟨by omega, by omega⟩
  have hend : cP.workTapes (ι jR) (cP.workTapePos (ι jR) + m) = none := by
    simp only [cP, Function.update_self, zero_add]
    exact hout m (Or.inr le_rfl)
  have hleft : cP.workTapes (ι jR) (cP.workTapePos (ι jR) - 1) = none := by
    simp only [cP, Function.update_self, zero_sub]
    exact hout (-1) (Or.inl (by omega))
  -- the handoff is the silently embedded start of `R`, and the embedded run is `R`'s
  have hrun : ∀ (s : List Bool), s.length = m → ∀ u : ℕ,
      (embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) u =
        embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
          (R.runFrom (streamStartCfg z jR entry s) u) := by
    intro s hs u
    rw [hcP, guessRunCfg_clean ι cap hcap jR blk m hout pexit entry s hs]
    exact embedSilentTM_runFrom ι cap hcap R _ _ [] [] _ u
  have hQ : ∀ s : List Bool, s.length = m → ∃ TQ ≤ T,
      (((embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) TQ).state =
          some acc ∨
        ((embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) TQ).state =
          some rej) ∧
      ∀ u < TQ,
        ((embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) u).state ≠ some acc ∧
        ((embedSilentTM ι cap R).runFrom (guessRunCfg cP (ι jR) s entry) u).state ≠
          some rej := by
    intro s hs
    obtain ⟨TR, hTR, hv, hf⟩ := hR s hs
    refine ⟨TR, hTR, ?_, ?_⟩
    · rw [hrun s hs]
      exact hv
    · intro u hu
      rw [hrun s hs]
      exact hf u hu
  refine ⟨guessRunTM_haltsWithin P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej TP cP
    hP rfl hPfirst m hblock hend hleft T hQ, fun B hB => ?_⟩
  rw [guessRunTM_accepts_iff P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej TP cP
    hP rfl hPfirst m hblock hend hleft T hQ B hB]
  constructor
  · rintro ⟨s, hs, TQ, hacc, hf, -⟩
    refine ⟨s, hs, TQ, ?_, ?_⟩
    · rw [hrun s hs] at hacc
      exact hacc
    · intro u hu
      have h := hf u hu
      rw [hrun s hs] at h
      exact h
  · rintro ⟨s, hs, TR, hacc, hf⟩
    refine ⟨s, hs, TR, ?_, ?_, ?_⟩
    · rw [hrun s hs]
      exact hacc
    · intro u hu
      rw [hrun s hs]
      exact hf u hu
    · rw [hrun s hs]
      rfl

end Turing

/-! ## The controller-stopped guess-then-run assembly

The instance of `Turing.guessCtlRunTM` with the unbounded writer under a controller. The
setup leaves the stream tape blank from its head on; the writer guesses bits until its controller
stops, after a number of bits that depends on the bits; the stream head is rewound; a
deterministic run ends in one of two live verdict states; and the verdict leaf emits the verdict
bit and halts. A guessed display of unknown length has this shape (the linear normal form,
`TCSlib.Complexity.ClassNP.NDNormalForm`).

* `Turing.guessCtlRunTM_runWith_handoff`: a word whose stream first stops the controller after
  `m` bits drives the host to the run's entry at time `TP + 2m + 9`, the stream on the tape.
* `Turing.guessCtlRunTM_runWith`: the whole branch, through the run's first verdict.
* `Turing.guessCtlRunTM_stop_of_halted`: a halted branch has passed a stop of the controller.
* `Turing.guessCtlRunTM_accepts_of`, `Turing.guessCtlRunTM_stream_of_accepts`: acceptance,
  forward at every budget beyond the branch's time, and backward.

There is no all-branch halting lemma: a stream that never stops the controller never ends the
guess.
-/

namespace Turing

/-- **Through the guess and the rewind.** Let the setup `P` run from its initial configuration on
`z` to `cP` at time `TP`, at its exit `pexit` and not at `pexit` before, with tape `j` blank from
its head on and just before it. Let the `m` bits of the word `w` after its first `TP + 1` first
stop the controller: the controller state after `i` of them does not stop for `i < m` and stops
at `m`. Then a word of length `TP + 2m + 9` drives the host to the run's entry configuration
`Turing.guessRunCfg cP j s qentry`, tagged by the run phase, where `s` is those `m` bits. The
time is that of `Turing.guessRunTM_runWith_handoff`: `TP` for the setup, `1` per dispatch (four),
`m + 1` for the writer, `1` for the step right and `m + 3` for the rewind.
[AB09, §2.1.2]

**Proof sketch.** As for `Turing.guessRunTM_runWith_handoff`, one application of
`Turing.NDTM.phaseHostND_run` per phase, with `Turing.ndWriterTM_run_controller` for the writer:
its second clause is the guard. The blank tape gives the step right's blank after the stream and
the rewind's blank before it. -/
theorem guessCtlRunTM_runWith_handoff {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool}
    (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (hblank : ∀ p : ℕ, cP.workTapes j (cP.workTapePos j + p) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (m : ℕ) (w : List Bool) (hw : w.length = TP + 2 * m + 9)
    (hlive : ∀ i < m, stop (((w.drop (TP + 1)).take i).foldl δ q₀) = false)
    (hstop : stop (((w.drop (TP + 1)).take m).foldl δ q₀) = true) :
    (guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z) =
      (guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry).mapState
        (Sigma.mk GuessRunPhase.run) := by
  have hst : (cP.mapState (fun _ => NDWriterState.run q₀)).state = some (NDWriterState.run q₀) := by
    rw [Cfg.mapState_state, hPexit]; rfl
  obtain ⟨hW1, hW2⟩ := ndWriterTM_run_controller j q₀ δ stop
    (cP.mapState (fun _ => NDWriterState.run q₀)) q₀ hst (w.drop (TP + 1)) m (by simp; omega)
    hlive hstop
  refine gr_handoff P pexit j q₀ δ stop false V qentry acc rej TP cP hP hPexit hPfirst m
    (hblank m) hleft w hw ?_ ?_
  · rw [hW1, gr_writer_end]
  · intro u hu
    rw [List.take_take, Nat.min_eq_left (by omega)]
    exact hW2 u (by omega)

/-- **The whole branch.** Under the setup hypotheses of `Turing.guessCtlRunTM_runWith_handoff`,
let the stream `s` of length `m` first stop the controller at its end, and let the run `V` from
the entry configuration `Turing.guessRunCfg cP j s qentry` reach a verdict state, `acc` or `rej`,
first at time `TQ`, in the configuration `d`. Then every choice word whose `m` bits after its
first `TP + 1` are `s`, of length at least `TP + 2m + TQ + 11`, halts the host with `d`'s input
head, tapes and heads, and with output `d`'s output followed by the verdict bit (`true` iff `d` is
at `acc`). Choices after the stream are ignored. [AB09, §2.1.2]

**Proof sketch.** `Turing.guessCtlRunTM_runWith_handoff` on the first `TP + 2m + 9` bits, whose
stream is `s`. Then, as for `Turing.guessRunTM_runWith`, `Turing.NDTM.phaseHostND_run` for the
run phase up to its first verdict, one step of the verdict leaf, and absorption
(`Turing.NDTM.runWith_of_halt`) for the remaining choices. -/
theorem guessCtlRunTM_runWith {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool}
    (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (hblank : ∀ p : ℕ, cP.workTapes j (cP.workTapePos j + p) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (m : ℕ) (s : List Bool) (hs : s.length = m)
    (hslive : ∀ i < m, stop ((s.take i).foldl δ q₀) = false)
    (hsstop : stop (s.foldl δ q₀) = true) (TQ : ℕ)
    (hverd : (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
      (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej)
    (hfirst : ∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
      (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (w : List Bool) (hws : (w.drop (TP + 1)).take m = s)
    (hw : TP + 2 * m + TQ + 11 ≤ w.length) :
    let d := V.runFrom (guessRunCfg cP j s qentry) TQ
    (guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z) =
      ⟨none, d.inputPos, d.workTapes, d.workTapePos,
        d.output ++ [decide (d.state = some acc)]⟩ := by
  -- the stream of the handoff word
  have hseg : ∀ i ≤ m, ((w.take (TP + 2 * m + 9)).drop (TP + 1)).take i = s.take i := by
    intro i hi
    rw [← hws, List.drop_take, List.take_take, List.take_take]
    congr 1
    omega
  -- through the guess and the rewind
  have hH := guessCtlRunTM_runWith_handoff P pexit j q₀ δ stop V qentry acc rej TP cP hP hPexit
    hPfirst hblank hleft m (w.take (TP + 2 * m + 9)) (by simp; omega)
    (fun i hi => by rw [hseg i hi.le]; exact hslive i hi)
    (by rw [hseg m le_rfl, ← hs, List.take_length]; exact hsstop)
  rw [hseg m le_rfl, ← hs, List.take_length, hs] at hH
  exact gr_runWith_of_handoff P pexit j q₀ δ stop false V qentry acc rej cP s TQ hverd hfirst
    (TP + 2 * m + 9) w hH (by omega)

/-- **A halted branch has passed a stop of the controller.** Under the setup hypotheses of
`Turing.guessCtlRunTM_runWith_handoff` (only the setup's run to its exit), if the host halts on
the choice word `w`, then the bits of `w` after its first `TP + 1` first stop the controller after
some `m` of them, with at least one more bit of `w` after those `m`. A branch whose bits never stop
the controller is still guessing: it has not halted. [AB09, §2.1.2]

**Proof sketch.** Otherwise the controller does not stop after any `i < |w| − (TP + 1)` of those
bits (by strong induction, each such `i` would be a first stop). If `w` has at most `TP` bits, the
host is in the setup phase, live (`Turing.NDTM.phaseHostND_run`'s prefix clause; the setup is live
before its exit). Otherwise, after the setup and its dispatch the host follows the writer on the
remaining bits (`Turing.NDTM.runWith_mapState_of_agreeOn`, the writer's states being redirected
only at `done`), and the writer is still at `run` (`wr_prefix_controller`): live again. -/
theorem guessCtlRunTM_stop_of_halted {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool}
    (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (w : List Bool)
    (hhalt : ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).state = none) :
    ∃ m, TP + 1 + m < w.length ∧
      (∀ i < m, stop (((w.drop (TP + 1)).take i).foldl δ q₀) = false) ∧
      stop (((w.drop (TP + 1)).take m).foldl δ q₀) = true := by
  classical
  by_contra hno
  push_neg at hno
  set M := guessCtlRunPhases P j q₀ δ stop false V
  set red := guessCtlRunRed pexit q₀ qentry acc rej
  have hN : guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej =
      NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red := rfl
  rw [hN] at hhalt
  have hinit : (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).initCfg z =
      (P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre) := by
    rw [NDTM.initCfg_eq, MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.init_state, Cfg.init_state, Option.map_some]
      rfl
    · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
    · funext i p
      rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext i
      rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  rw [hinit] at hhalt
  -- the setup is live up to its exit
  have hPlive : ∀ u ≤ TP, (P.runFrom (P.initCfg z) u).state ≠ none := by
    intro u hu h
    have := hPexit
    rw [← hP, show TP = u + (TP - u) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ h] at this
    rw [h] at this
    exact Option.noConfusion this
  by_cases hshort : w.length ≤ TP
  · -- still in the setup: the host follows the setup, which is live
    let emb : GuessRunPhase.CtlState SP SQ Q GuessRunPhase.pre ↪
        (Σ i, GuessRunPhase.CtlState SP SQ Q i) :=
      ⟨Sigma.mk GuessRunPhase.pre, sigma_mk_injective⟩
    have hagree : ∀ (b : Bool) (q : SP), (fun s => red GuessRunPhase.pre s = none) q →
        ∀ inp work, (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).tr b (emb q) inp work =
          ((M GuessRunPhase.pre).tr b q inp work).mapState emb := by
      intro b q hq inp work
      simp only [NDTM.phaseHostND, emb, Function.Embedding.coeFn_mk, hq]
    have hrun := NDTM.runWith_mapState_of_agreeOn (M GuessRunPhase.pre)
      (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red) emb
      (fun s => red GuessRunPhase.pre s = none) hagree (P.initCfg z) w (by
        intro u hu s' hs'
        change (P.toNDTM.runWith (w.take u) (P.initCfg z)).state = some s' at hs'
        rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hs'
        have hne := hPfirst u (by omega)
        show (if s' = pexit then _ else none) = none
        rw [if_neg]
        rintro rfl
        exact hne hs')
    rw [show (P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre) = (P.initCfg z).mapState emb
      from rfl, hrun] at hhalt
    change ((P.toNDTM.runWith w (P.initCfg z)).mapState _).state = none at hhalt
    rw [MultiTapeTM.toNDTM_runWith] at hhalt
    simp only [Cfg.mapState_state] at hhalt
    exact hPlive w.length hshort (Option.map_eq_none_iff.mp hhalt)
  · -- after the setup: the host follows the writer, which has not stopped
    push_neg at hshort
    obtain ⟨a₁, b₁, r, hw, ha₁⟩ := guessRun_split TP w hshort
    have hdrop : w.drop (TP + 1) = r := by
      rw [hw, List.drop_left' (by simp [ha₁])]
    rw [hdrop] at hno
    -- no stop along the remaining bits
    have hnostop : ∀ i < r.length, stop ((r.take i).foldl δ q₀) = false := by
      intro i hi
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        exact Bool.eq_false_iff.mpr (hno i (by rw [hw]; simp [ha₁]; omega)
          (fun i' hi' => ih i' hi' (by omega)))
    -- the setup and its dispatch
    have h1 : (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).runWith (a₁ ++ [b₁])
        ((P.initCfg z).mapState (Sigma.mk GuessRunPhase.pre)) =
        cP.mapState (fun _ =>
          (⟨.guess, NDWriterState.run q₀⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) := by
      refine (NDTM.phaseHostND_run M ⟨.pre, P.q₀⟩ red GuessRunPhase.pre (P.initCfg z) cP a₁ ?_
        pexit hPexit _ ?_ ?_ b₁).2
      · show P.toNDTM.runWith a₁ (P.initCfg z) = cP
        rw [MultiTapeTM.toNDTM_runWith, ha₁, hP]
      · show (if pexit = pexit then _ else none) = _
        simp
      · intro u hu s' hs'
        change (P.toNDTM.runWith (a₁.take u) (P.initCfg z)).state = some s' at hs'
        rw [MultiTapeTM.toNDTM_runWith, List.length_take, Nat.min_eq_left hu.le] at hs'
        have hne := hPfirst u (by omega)
        show (if s' = pexit then _ else none) = none
        rw [if_neg]
        rintro rfl
        exact hne hs'
    let cW : Cfg k Bool (NDWriterState Q) z := cP.mapState (fun _ => NDWriterState.run q₀)
    have hcW : cP.mapState (fun _ =>
        (⟨.guess, NDWriterState.run q₀⟩ : Σ i, GuessRunPhase.CtlState SP SQ Q i)) =
        cW.mapState (Sigma.mk GuessRunPhase.guess) := by
      rw [Cfg.mapState_mapState]; rfl
    have hWst : cW.state = some (NDWriterState.run q₀) := by simp [cW, Cfg.mapState_state, hPexit]
    have hwr : ∀ u ≤ r.length, (ndWriterTM k j q₀ δ stop false).runWith (r.take u) cW =
        wr_cfg j cW (.run ((r.take u).foldl δ q₀)) (r.take u) := fun u hu =>
      wr_prefix_controller j q₀ δ stop cW q₀ hWst r u hu (fun i hi => hnostop i (by omega))
    let emb : GuessRunPhase.CtlState SP SQ Q GuessRunPhase.guess ↪
        (Σ i, GuessRunPhase.CtlState SP SQ Q i) :=
      ⟨Sigma.mk GuessRunPhase.guess, sigma_mk_injective⟩
    have hagree : ∀ (b : Bool) (q : NDWriterState Q),
        (fun s => red GuessRunPhase.guess s = none) q → ∀ inp work,
        (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red).tr b (emb q) inp work =
          ((M GuessRunPhase.guess).tr b q inp work).mapState emb := by
      intro b q hq inp work
      simp only [NDTM.phaseHostND, emb, Function.Embedding.coeFn_mk, hq]
    have hrun := NDTM.runWith_mapState_of_agreeOn (M GuessRunPhase.guess)
      (NDTM.phaseHostND M ⟨.pre, P.q₀⟩ red) emb
      (fun s => red GuessRunPhase.guess s = none) hagree cW r (by
        intro u hu s' hs'
        change ((ndWriterTM k j q₀ δ stop false).runWith (r.take u) cW).state = some s' at hs'
        rw [hwr u hu.le] at hs'
        simp only [wr_cfg, Option.some.injEq] at hs'
        subst hs'
        rfl)
    rw [hw, NDTM.runWith_append, h1, hcW,
      show cW.mapState (Sigma.mk GuessRunPhase.guess) = cW.mapState emb from rfl, hrun] at hhalt
    change (((ndWriterTM k j q₀ δ stop false).runWith r cW).mapState _).state = none at hhalt
    rw [show r = r.take r.length from (List.take_length).symm, hwr r.length le_rfl] at hhalt
    simp [wr_cfg, Cfg.mapState_state] at hhalt

/-- **Acceptance, forward.** Under the setup hypotheses of `Turing.guessCtlRunTM_runWith_handoff`,
let the stream `s` first stop the controller at its end, and let the run `V` from
`Turing.guessRunCfg cP j s qentry` reach `acc` first at time `TQ`, not at `rej` before, with an
empty output. Then at every budget `B` at least `TP + 2|s| + TQ + 11`, some choice word of length
exactly `B` halts the host with output exactly `[true]` (the shape of
`Turing.FinNDTM.AcceptsWithin`). [AB09, §2.1.2]

**Proof sketch.** The word of `TP + 1` bits `false`, then `s`, then `false` up to length `B`, has
stream `s`; `Turing.guessCtlRunTM_runWith` gives the output `[] ++ [true]`. -/
theorem guessCtlRunTM_accepts_of {k : ℕ} {SP SQ Q : Type} [DecidableEq SP] [DecidableEq SQ]
    (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q) (δ : Q → Bool → Q)
    (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ) {z : List Bool}
    (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (hblank : ∀ p : ℕ, cP.workTapes j (cP.workTapePos j + p) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (s : List Bool) (hslive : ∀ i < s.length, stop ((s.take i).foldl δ q₀) = false)
    (hsstop : stop (s.foldl δ q₀) = true) (TQ : ℕ)
    (hacc : (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc)
    (hfirst : ∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
      (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (hnil : (V.runFrom (guessRunCfg cP j s qentry) TQ).output = [])
    (B : ℕ) (hB : TP + 2 * s.length + TQ + 11 ≤ B) :
    ∃ w : List Bool, w.length = B ∧
      ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).state = none ∧
      ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).output =
          [true] := by
  let w := List.replicate (TP + 1) false ++ s ++ List.replicate (B - (TP + 1 + s.length)) false
  have hwlen : w.length = B := by simp [w]; omega
  have hws : (w.drop (TP + 1)).take s.length = s := by
    simp only [w, List.append_assoc]
    rw [List.drop_left' (by simp), List.take_left' rfl]
  have hrun := guessCtlRunTM_runWith P pexit j q₀ δ stop V qentry acc rej TP cP hP hPexit
    hPfirst hblank hleft s.length s rfl hslive hsstop TQ (Or.inl hacc) hfirst w hws
    (by omega)
  refine ⟨w, hwlen, ?_, ?_⟩
  · rw [hrun]
  · rw [hrun]
    show (V.runFrom (guessRunCfg cP j s qentry) TQ).output ++
      [decide ((V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc)] = [true]
    rw [hnil, hacc]
    simp

/-- **Acceptance, backward.** Under the setup hypotheses of `Turing.guessCtlRunTM_runWith_handoff`,
let the run `V` reach a verdict, `acc` or `rej`, from the entry configuration of every stream that
first stops the controller at its end. If some choice word halts the host with output exactly
`[true]`, then some such stream makes `V`'s first verdict `acc`, with an empty output at that time.
[AB09, §2.1.2]

**Proof sketch.** The halted branch has passed a stop of the controller
(`Turing.guessCtlRunTM_stop_of_halted`); its stream `s` is the bits before it. Pad the word past
`TP + 2|s| + TQ + 11`: by absorption (`Turing.NDTM.runWith_of_halt`) the padded branch is the same
halted configuration, and `Turing.guessCtlRunTM_runWith` gives its output, `V`'s output followed
by the verdict bit. That is `[true]` only if `V`'s output is empty and the verdict is `acc`. -/
theorem guessCtlRunTM_stream_of_accepts {k : ℕ} {SP SQ Q : Type} [DecidableEq SP]
    [DecidableEq SQ] (P : MultiTapeTM k Bool SP) (pexit : SP) (j : Fin k) (q₀ : Q)
    (δ : Q → Bool → Q) (stop : Q → Bool) (V : MultiTapeTM k Bool SQ) (qentry acc rej : SQ)
    {z : List Bool} (TP : ℕ) (cP : Cfg k Bool SP z)
    (hP : P.runFrom (P.initCfg z) TP = cP) (hPexit : cP.state = some pexit)
    (hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some pexit)
    (hblank : ∀ p : ℕ, cP.workTapes j (cP.workTapePos j + p) = none)
    (hleft : cP.workTapes j (cP.workTapePos j - 1) = none)
    (hV : ∀ s : List Bool, (∀ i < s.length, stop ((s.take i).foldl δ q₀) = false) →
      stop (s.foldl δ q₀) = true → ∃ TQ : ℕ,
        ((V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∨
          (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some rej) ∧
        ∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
          (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej)
    (w : List Bool)
    (hhalt : ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).state = none)
    (hout : ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
        ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z)).output = [true]) :
    ∃ s : List Bool, (∀ i < s.length, stop ((s.take i).foldl δ q₀) = false) ∧
      stop (s.foldl δ q₀) = true ∧ ∃ TQ : ℕ,
        (V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc ∧
        (∀ u < TQ, (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some acc ∧
          (V.runFrom (guessRunCfg cP j s qentry) u).state ≠ some rej) ∧
        (V.runFrom (guessRunCfg cP j s qentry) TQ).output = [] := by
  obtain ⟨m, hm, hl, hst⟩ := guessCtlRunTM_stop_of_halted P pexit j q₀ δ stop V qentry acc rej
    TP cP hP hPexit hPfirst w hhalt
  set s := (w.drop (TP + 1)).take m with hs_def
  have hslen : s.length = m := by simp [s]; omega
  have hslive : ∀ i < s.length, stop ((s.take i).foldl δ q₀) = false := by
    intro i hi
    rw [hslen] at hi
    rw [hs_def, List.take_take, Nat.min_eq_left hi.le]
    exact hl i hi
  obtain ⟨TQ, hverd, hfirst⟩ := hV s hslive hst
  let w' := w ++ List.replicate (TP + 2 * m + TQ + 11) false
  have hws : (w'.drop (TP + 1)).take m = s := by
    simp only [w']
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  have hrun := guessCtlRunTM_runWith P pexit j q₀ δ stop V qentry acc rej TP cP hP hPexit
    hPfirst hblank hleft m s hslen (fun i hi => hslive i (by omega)) hst TQ hverd hfirst w' hws
    (by simp [w'])
  have habs : (guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w'
      ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z) =
      (guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).runWith w
      ((guessCtlRunTM P pexit j q₀ δ stop false V qentry acc rej).initCfg z) := by
    simp only [w']
    rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
  rw [← habs, hrun] at hout
  have hlen := congrArg List.length hout
  simp only [List.length_append, List.length_singleton] at hlen
  have hnil : (V.runFrom (guessRunCfg cP j s qentry) TQ).output = [] :=
    List.eq_nil_of_length_eq_zero (by omega)
  change (V.runFrom (guessRunCfg cP j s qentry) TQ).output ++
    [decide ((V.runFrom (guessRunCfg cP j s qentry) TQ).state = some acc)] = [true] at hout
  rw [hnil, List.nil_append, List.singleton_inj, decide_eq_true_iff] at hout
  exact ⟨s, hslive, hst, TQ, hout, hfirst, hnil⟩

end Turing
