/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic phase host and the choice writer

The nondeterministic part of the construction layer that the guess-first route needs (user
decision 1 of 2026-10-13; the C1 design note §3.1, §3.4). The universal NDTM and the
diagonalizer of `TCSlib.Complexity.Diagonalization.NTimeHierarchy` guess their whole choice word
up front, with one small nondeterministic leaf, and then run deterministically.

## Design

* **The ND phase host** `Turing.NDTM.phaseHostND` is `Turing.phaseHostTM` over nondeterministic
  phases, deterministic phases entering as `Turing.MultiTapeTM.toNDTM`. Each of its two slices
  is the deterministic phase host of the phases' slices (`Turing.NDTM.phaseHostND_fixChoice`,
  by `rfl`), and a phase runs inside it along every word
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

## Main definitions

* `Turing.NDTM.phaseHostND` — the nondeterministic phase host.
* `Turing.NDWriterState`, `Turing.ndWriterTM` — the choice writer. [AB09, §2.1.2]

## Main results

* `Turing.NDTM.phaseHostND_fixChoice`, `Turing.NDTM.phaseHostND_run` (proved).
* `Turing.ndWriterTM_run_block` — the bounded flavor's contract (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2: an NDTM chooses one of its two transition
  functions at every step.)
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
in `Turing.NDTM.phaseHostND` gives `Turing.phaseHostTM` over the phases' slices at `b`. -/
theorem phaseHostND_fixChoice {I : Type} {Ph : I → Type} (M : (i : I) → NDTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (b : Bool) :
    (phaseHostND M q0 red).fixChoice b = phaseHostTM (fun i => (M i).fixChoice b) q0 red :=
  rfl

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
  sorry

end Turing
