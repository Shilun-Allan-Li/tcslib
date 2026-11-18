/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunEncoding
import TCSlib.Complexity.TuringMachine.NondeterministicSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Choice slices of the RAM simulation phases

An instruction's only genuine choice is at its entry. After that first transition the entry
is never reached again, so any remaining choice word follows the corresponding fixed slice.
The forwarding tape embedding lifts the two deterministic slices to the host's tape bank.

## Main definitions

* `WordRAM.Sim.runEmbedND`: the forwarding embedding of a binary-choice phase.

## Main results

* `WordRAM.Sim.runEmbedND_fixChoice`: each slice is the forwarding embedding of its source.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2: branches of a nondeterministic machine.)
-/

namespace WordRAM.Sim

open Turing

/-- The nondeterministic forwarding embedding uses the existing deterministic tape embedding
for each choice. It adds no control states or transitions beyond that transformation. -/
@[simps (config := { isSimp := false }) q₀ tr]
def runEmbedND {K : ℕ} {S : Type} (σ : Fin 8 ↪ Fin K) (N : NDTM 8 Bool S) :
    NDTM K Bool S where
  q₀ := N.q₀
  tr b := (embedEmitTM σ (N.fixChoice b)).tr

/-- Fixing a choice in the nondeterministic tape embedding gives exactly the corresponding
deterministic forwarding embedding. -/
theorem runEmbedND_fixChoice {K : ℕ} {S : Type} (σ : Fin 8 ↪ Fin K)
    (N : NDTM 8 Bool S) (b : Bool) :
    (runEmbedND σ N).fixChoice b = embedEmitTM σ (N.fixChoice b) := by
  have hq : ((runEmbedND σ N).fixChoice b).q₀ =
      (embedEmitTM σ (N.fixChoice b)).q₀ := by
    rw [NDTM.fixChoice_q₀, runEmbedND_q₀, embedEmitTM_q₀, NDTM.fixChoice_q₀]
  have ht : ((runEmbedND σ N).fixChoice b).tr =
      (embedEmitTM σ (N.fixChoice b)).tr := by
    funext q inp work
    rw [NDTM.fixChoice_tr, runEmbedND_tr]
  calc (runEmbedND σ N).fixChoice b
      = ⟨((runEmbedND σ N).fixChoice b).q₀, ((runEmbedND σ N).fixChoice b).tr⟩ := rfl
    _ = ⟨(embedEmitTM σ (N.fixChoice b)).q₀, (embedEmitTM σ (N.fixChoice b)).tr⟩ := by
      rw [hq, ht]
    _ = embedEmitTM σ (N.fixChoice b) := rfl

/-- If no transition of a phase enters `entry`, every positive-time configuration of either
deterministic slice avoids that state, from any starting configuration. -/
theorem runSlice_avoids_entry {K : ℕ} {S : Type} {x : List Bool}
    (N : NDTM K Bool S) (entry : S)
    (hentry : ∀ (b : Bool) (q : S) inp work, (N.tr b q inp work).state ≠ some entry)
    (b : Bool) (d : Turing.Cfg K Bool S x) (t : ℕ) (ht : 0 < t) :
    ((N.fixChoice b).runFrom d t).state ≠ some entry := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [MultiTapeTM.runFrom_succ_eq_step']
  cases hs : ((N.fixChoice b).runFrom d u).state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs, hs]
    intro h
    cases h
  | some q =>
    rw [MultiTapeTM.step_of_some hs, Action.apply_state, NDTM.fixChoice_tr]
    exact hentry b q _ _

/-- A phase whose only possible choice is its unrepeated entry follows the slice selected by
the first bit of the branch. All later bits are immaterial.

**Proof sketch.** Take the first step in the chosen slice. Every later live state differs
from the entry by `runSlice_avoids_entry`, so the published deterministic-slice transfer
`Turing.NDTM.runWith_eq_fixChoice_runFrom` applies to the entire tail. -/
theorem runWith_entry_slice {K : ℕ} {S : Type} {x : List Bool}
    (N : NDTM K Bool S) (entry : S)
    (hentry : ∀ (b : Bool) (q : S) inp work, (N.tr b q inp work).state ≠ some entry)
    (hagree : ∀ q : S, q ≠ entry → N.tr false q = N.tr true q)
    (b : Bool) (w : List Bool) (d : Turing.Cfg K Bool S x) :
    N.runWith (b :: w) d = (N.fixChoice b).runFrom d (w.length + 1) := by
  rw [NDTM.runWith_cons, NDTM.stepWith_eq_fixChoice_step,
    MultiTapeTM.runFrom_succ_eq_step]
  apply NDTM.runWith_eq_fixChoice_runFrom
  intro j _ q hq
  apply hagree
  intro he
  subst q
  apply runSlice_avoids_entry N entry hentry b d (j + 1) (Nat.succ_pos _)
  rw [MultiTapeTM.runFrom_succ_eq_step]
  exact hq

/-- Either slice of the deterministic-to-nondeterministic embedding is the original machine. -/
theorem runDet_fixChoice {K : ℕ} {S : Type} (M : MultiTapeTM K Bool S) (b : Bool) :
    M.toNDTM.fixChoice b = M := by
  have hq : (M.toNDTM.fixChoice b).q₀ = M.q₀ := by
    rw [NDTM.fixChoice_q₀, MultiTapeTM.toNDTM_q₀]
  have ht : (M.toNDTM.fixChoice b).tr = M.tr := by
    funext q inp work
    rw [NDTM.fixChoice_tr, MultiTapeTM.toNDTM_tr]
  calc M.toNDTM.fixChoice b
      = ⟨(M.toNDTM.fixChoice b).q₀, (M.toNDTM.fixChoice b).tr⟩ := rfl
    _ = ⟨M.q₀, M.tr⟩ := by rw [hq, ht]
    _ = M := rfl

/-- The forwarding nondeterministic embedding commutes with every branch, preserving the
ambient frame and forwarding the source output.

**Proof sketch.** Induct on the choice word. One step under its head bit is a step of the
corresponding deterministic embedding, by `runEmbedND_fixChoice`, and the existing one-step
case of `Turing.embedEmitTM_runFrom` transports that step. -/
theorem runEmbedND_runWith {K : ℕ} {S : Type} {x : List Bool}
    (σ : Fin 8 ↪ Fin K) (N : NDTM 8 Bool S)
    (tapes : Fin K → ℤ → Option Bool) (heads : Fin K → ℤ) (pre : List Bool)
    (w : List Bool) (d : Turing.Cfg 8 Bool S x) :
    (runEmbedND σ N).runWith w (embedEmitCfg σ tapes heads pre d) =
      embedEmitCfg σ tapes heads pre (N.runWith w d) := by
  induction w generalizing d with
  | nil => rw [NDTM.runWith_nil, NDTM.runWith_nil]
  | cons b w ih =>
    rw [NDTM.runWith_cons, NDTM.stepWith_eq_fixChoice_step, runEmbedND_fixChoice,
      ← MultiTapeTM.runFrom_one, embedEmitTM_runFrom, MultiTapeTM.runFrom_one,
      ← NDTM.stepWith_eq_fixChoice_step, ih, NDTM.runWith_cons]

/-- A constant choice word follows the corresponding fixed slice, even when the machine's
two transitions differ. This also covers the empty word. -/
theorem runWith_replicate {K : ℕ} {S : Type} {x : List Bool}
    (N : NDTM K Bool S) (b : Bool) (t : ℕ) (d : Turing.Cfg K Bool S x) :
    N.runWith (List.replicate t b) d = (N.fixChoice b).runFrom d t := by
  induction t generalizing d with
  | zero => rw [List.replicate_zero, NDTM.runWith_nil, MultiTapeTM.runFrom_zero]
  | succ t ih =>
    rw [List.replicate_succ, NDTM.runWith_cons, NDTM.stepWith_eq_fixChoice_step, ih,
      MultiTapeTM.runFrom_succ_eq_step]

end WordRAM.Sim
