/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: transport along the R1 embedding

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`).
MIG-0a's `Turing.Contract.embed`, moved here from `Build/Contract.lean` as landed on 2026-10-13
with no statement changed, with MIG-0b's joint trajectory and positivity of the transport.

## Main definitions

* `Turing.Contract.embed`: transport along the R1 embedding `Turing.embedEmitTM`, for
  output-normalized preconditions.

## Main results

* `Turing.Contract.Traj.embed`, `Turing.Contract.embed_positive`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the specification-only calls adapted as `Turing.Contract` (design adaptation; full
  entry in `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

namespace Contract

/-- **Transport along the R1 embedding** (`Turing.embedEmitTM_runFrom`): the source contract
holds on the selected tapes; unselected tapes and heads are framed, and output is appended.
The precondition and the time are the source contract's at the selection `d.select σ`, and so
is the envelope of a selected head; an unselected head has the one-point envelope at its start.
The endpoint embeds the source endpoint into `d`'s tapes, heads and output.

The selection empties the source output, so `embed` transports **output-normalized**
preconditions only: a source precondition that inspects the output is tested on `[]` and is not
preserved (one asking for output `[true]` becomes false for every host). The intended
clean-call and tape-word instances fit; output-sensitive contracts would need a transport with
an explicit decomposition of the host output.

**Proof sketch.** By `Turing.embedEmitCfg_select`, `d` is the embedding of its own selection, so
`Turing.embedEmitTM_runFrom` makes the host run, at every time, the embedding of the source run
from the selection. The run is the embedded source run, and the exit and the cut are the
source's, since the selection and the embedding keep the state. For the envelope, a selected
head is the source head (`Turing.embedEmitCfg_selected_pos`), with the source bounds; an
unselected head stays at its start by the frame lemma `Turing.embedEmitTM_frame`, inside its
one-point interval. -/
noncomputable def embed {m : ℕ} (σ : Fin m ↪ Fin k) {S : Type} {M : MultiTapeTM m Γ S}
    {entry : S} {X : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry X ι x) :
    Contract (embedEmitTM σ M) entry X ι x where
  pre i d := C.pre i (d.select σ)
  time i d := C.time i (d.select σ)
  post i d := embedEmitCfg σ d.workTapes d.workTapePos d.output (C.post i (d.select σ))
  lo i d := Function.extend σ (C.lo i (d.select σ)) d.workTapePos
  hi i d := Function.extend σ (C.hi i (d.select σ)) d.workTapePos
  run i d hd hp := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ)
      (C.time i (d.select σ))
    rw [embedEmitCfg_select σ d] at hr
    rw [hr, C.run i _ hd hp]
  exit_mem i d hd hp := C.exit_mem i _ hd hp
  cut i d hd hp u hu := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) u
    rw [embedEmitCfg_select σ d] at hr
    rw [hr]
    exact C.cut i _ hd hp u hu
  env i d hd hp u hu j := by
    have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) u
    rw [embedEmitCfg_select σ d] at hr
    show ((embedEmitTM σ M).runFrom d u).workTapePos j ∈
      Finset.Icc (Function.extend σ (C.lo i (d.select σ)) d.workTapePos j)
        (Function.extend σ (C.hi i (d.select σ)) d.workTapePos j)
    rw [hr]
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨a, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, σ.injective.extend_apply, σ.injective.extend_apply]
      exact C.env i _ hd hp u hu a
    · have hf := (embedEmitTM_frame σ M d.workTapes d.workTapePos d.output (d.select σ) u).1 j hj
      rw [embedEmitTM_runFrom] at hf
      have hne : ¬∃ a, σ a = j := fun ⟨a, ha⟩ => hj ⟨a, ha⟩
      rw [hf.2, Function.extend_apply' _ _ _ hne, Function.extend_apply' _ _ _ hne]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-- **`embed` preserves joint trajectories**: the source relation holds of the selected heads,
at the selection, and every unselected head stays at its start.

**Proof sketch.** As in `Turing.Contract.embed`'s envelope: the host run is the embedded source
run (`Turing.embedEmitTM_runFrom` with `Turing.embedEmitCfg_select`), whose selected heads are
the source's (`Turing.embedEmitCfg_selected_pos`) and whose unselected heads are the frame
(`Turing.embedEmitCfg_unselected`). -/
theorem Traj.embed {m : ℕ} (σ : Fin m ↪ Fin k) {S : Type} {M : MultiTapeTM m Γ S} {entry : S}
    {X : Set (Option S)} {ι : Type} {x : List Γ} {C : Contract M entry X ι x}
    {R : ι → Cfg m Γ S x → (Fin m → ℤ) → Prop} (h : C.Traj R) :
    (Contract.embed σ C).Traj fun i d p => R i (d.select σ) (fun a => p (σ a)) ∧
      ∀ j, j ∉ Set.range σ → p j = d.workTapePos j := by
  intro i d hd hp u hu
  have hr := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) u
  rw [embedEmitCfg_select σ d] at hr
  rw [hr]
  refine ⟨?_, fun j hj => (embedEmitCfg_unselected σ _ _ _ _ j hj).2⟩
  have hs : (fun a => (embedEmitCfg σ d.workTapes d.workTapePos d.output
      (M.runFrom (d.select σ) u)).workTapePos (σ a)) = (M.runFrom (d.select σ) u).workTapePos :=
    funext fun a => embedEmitCfg_selected_pos σ _ _ _ _ a
  rw [hs]
  exact h i _ hd hp u hu

/-- `embed` keeps positivity: the time is the source's. -/
theorem embed_positive {m : ℕ} (σ : Fin m ↪ Fin k) {S : Type} {M : MultiTapeTM m Γ S}
    {entry : S} {X : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry X ι x)
    (h : C.Positive) : (Contract.embed σ C).Positive :=
  fun i _ hd hp => h i _ hd hp

end Contract

end Turing
