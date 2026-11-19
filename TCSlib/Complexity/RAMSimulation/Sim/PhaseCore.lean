/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseLayout
import TCSlib.Complexity.TuringMachine.Build.Contract.Seam
import TCSlib.Complexity.TuringMachine.Build.Contract.Reach
import TCSlib.Complexity.TuringMachine.CfgFacts

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State-independent frames for composing instruction rows

The instruction rows share eight tapes while their finite control types differ. A `PhaseFrame`
records the input head, work tapes, work heads and output, leaving control to the row that runs
on it. `PhaseRow` packages a finite row's bounded contract on these frames.

## Main definitions

* `WordRAM.Sim.PhaseFrame`: the state-independent part of an eight-tape configuration.
* `WordRAM.Sim.PhaseFrame.cfg`, `WordRAM.Sim.PhaseFrame.ofCfg`: install and remove control.
* `WordRAM.Sim.PhaseRow`: a finite row with a precondition and prescribed frame transformation.

## Main results

* `WordRAM.Sim.PhaseFrame.cfg_ofCfg`: reconstruction at a live state.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The input head, eight work tapes and heads, and output, independently of finite control. -/
structure PhaseFrame (x : List Bool) where
  inputPos : Fin (x.length + 2)
  workTapes : Fin 8 → ℤ → Option Bool
  workTapePos : Fin 8 → ℤ
  output : List Bool

/-- Removing control from a configuration retains its four tape and head fields. -/
def PhaseFrame.ofCfg {S : Type} {x : List Bool} (d : Turing.Cfg 8 Bool S x) : PhaseFrame x :=
  ⟨d.inputPos, d.workTapes, d.workTapePos, d.output⟩

attribute [simps (config := { isSimp := false }) inputPos workTapes workTapePos output] PhaseFrame.ofCfg

/-- Removing control retains the input head, work tapes and heads, and output, as an equation. -/
theorem PhaseFrame.ofCfg_eq {S : Type} {x : List Bool} (d : Turing.Cfg 8 Bool S x) :
    PhaseFrame.ofCfg d = ⟨d.inputPos, d.workTapes, d.workTapePos, d.output⟩ := rfl

/-- Installing control at `q` gives a live configuration with exactly the frame's tapes and heads. -/
def PhaseFrame.cfg {S : Type} {x : List Bool} (q : S) (F : PhaseFrame x) : Turing.Cfg 8 Bool S x :=
  ⟨some q, F.inputPos, F.workTapes, F.workTapePos, F.output⟩

attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output] PhaseFrame.cfg

/-- Installing control preserves all four frame fields and sets the live state to `q`. -/
theorem PhaseFrame.cfg_eq {S : Type} {x : List Bool} (q : S) (F : PhaseFrame x) :
    F.cfg q = ⟨some q, F.inputPos, F.workTapes, F.workTapePos, F.output⟩ := rfl

/-- Removing and reinstalling a configuration's live state reconstructs the configuration. -/
theorem PhaseFrame.cfg_ofCfg {S : Type} {x : List Bool} (d : Turing.Cfg 8 Bool S x) (q : S)
    (hd : d.state = some q) : (PhaseFrame.ofCfg d).cfg q = d :=
  Cfg.ext hd.symm rfl rfl rfl rfl

/-- Removing control after installing it recovers the frame. -/
theorem PhaseFrame.ofCfg_cfg {S : Type} {x : List Bool} (q : S) (F : PhaseFrame x) :
    PhaseFrame.ofCfg (F.cfg q) = F := rfl

/-- Renaming the control of a frame configuration only renames its installed live state. -/
theorem PhaseFrame.cfg_mapState {S S' : Type} {x : List Bool} (q : S) (F : PhaseFrame x)
    (f : S → S') : (F.cfg q).mapState f = F.cfg (f q) :=
  Cfg.mapState_eq_of_fields (F.cfg q) f (F.cfg (f q)) rfl rfl rfl rfl rfl

/-- A finite eight-tape row transforms a frame as prescribed, within uniform time and radius
bounds, and restores every work head. The index supplies word sizes and the semantic data read
by the row; the finite machine is uniform in that index and in the input. -/
structure PhaseRow (I : List Bool → Type)
    (pre : ∀ {x : List Bool}, I x → PhaseFrame x → Prop)
    (post : ∀ {x : List Bool}, I x → PhaseFrame x → PhaseFrame x)
    (B E : ∀ {x : List Bool}, I x → ℕ) where
  State : Type
  finite : Fintype State
  decEq : DecidableEq State
  machine : MultiTapeTM 8 Bool State
  entry : State
  exit : State
  heads : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), pre i F →
    (post i F).workTapePos = F.workTapePos
  run : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), pre i F →
    ReachesWithin machine (F.cfg entry) {some exit} (B i) (E i) ((post i F).cfg exit)

/-- A single-exit frame run followed by a frame run with any live exit set composes through
the seam. One dispatch step is added, and restored intermediate heads keep a common center for
the two radius bounds.

**Proof sketch.** Turn the two runs into singleton-precondition contracts with
`Contract.ofReaches`. `Contract.seq` supplies their seam run, cut and envelope, and
`PhaseFrame.cfg_mapState` identifies the state transports. The selected times are bounded by
`Contract.ofReaches_time_le`. Since the intermediate heads are restored, the hull of the two
head intervals lies within the sum of the radii about the original heads. -/
theorem phase_reaches_seq {S₁ S₂ : Type} [DecidableEq S₁] {x : List Bool}
    (M₁ : MultiTapeTM 8 Bool S₁) (M₂ : MultiTapeTM 8 Bool S₂)
    (entry₁ exit₁ : S₁) (entry₂ q₂ : S₂) (X₂ : Set (Option S₂))
    (F F₁ F₂ : PhaseFrame x) (B₁ E₁ B₂ E₂ : ℕ)
    (hr₁ : ReachesWithin M₁ (F.cfg entry₁) {some exit₁} B₁ E₁ (F₁.cfg exit₁))
    (hr₂ : ReachesWithin M₂ (F₁.cfg entry₂) X₂ B₂ E₂ (F₂.cfg q₂))
    (hq₂ : some q₂ ∈ X₂) (hh : F₁.workTapePos = F.workTapePos) :
    ReachesWithin (seamCompTM M₁ exit₁ M₂ entry₂) (F.cfg (Sum.inl entry₁))
      (Option.map Sum.inr '' X₂) (B₁ + 1 + B₂) (E₁ + E₂) (F₂.cfg (Sum.inr q₂)) := by
  classical
  let C₁ := Contract.ofReaches (M := M₁) (entry := entry₁) (X := {some exit₁})
    (fun (_ : Unit) d => d = F.cfg entry₁) (fun _ _ => B₁) (fun _ _ => E₁)
    (fun _ _ => F₁.cfg exit₁)
    (by intro u d hd he; subst d; exact hr₁)
    (by intro u d hd he; exact Set.mem_singleton_iff.mpr rfl)
  let C₂ := Contract.ofReaches (M := M₂) (entry := entry₂) (X := X₂)
    (fun (_ : Unit) d => d = F₁.cfg entry₂) (fun _ _ => B₂) (fun _ _ => E₂)
    (fun _ _ => F₂.cfg q₂)
    (by intro u d hd he; subst d; exact hr₂)
    (by intro u d hd he; exact hq₂)
  have link : ∀ (u : Unit) d, d.state = some entry₁ → C₁.pre u d →
      C₂.pre () ((C₁.post u d).mapState fun _ => entry₂) := by
    intro u d hd he
    simp only [C₁, C₂, Contract.ofReaches_pre, Contract.ofReaches_post,
      PhaseFrame.cfg_mapState]
  let C := Contract.seq C₁ C₂ (fun _ => ()) link
  have hpre : C.pre () (F.cfg (Sum.inl entry₁)) := by
    simp only [C, Contract.seq_pre, C₁, Contract.ofReaches_pre, PhaseFrame.cfg_mapState]
  have hpost : C.post () (F.cfg (Sum.inl entry₁)) = F₂.cfg (Sum.inr q₂) := by
    simp only [C, Contract.seq_post, C₁, C₂, Contract.ofReaches_post,
      PhaseFrame.cfg_mapState]
  have ht₁ : C₁.time () (F.cfg entry₁) ≤ B₁ := by
    apply Contract.ofReaches_time_le
    · rfl
    · rfl
  have ht₂ : C₂.time () (F₁.cfg entry₂) ≤ B₂ := by
    apply Contract.ofReaches_time_le
    · rfl
    · rfl
  have htime : C.time () (F.cfg (Sum.inl entry₁)) ≤ B₁ + 1 + B₂ := by
    simpa only [C, Contract.seq_time, C₁, Contract.ofReaches_post,
      PhaseFrame.cfg_mapState] using Nat.add_le_add (Nat.add_le_add_right ht₁ 1) ht₂
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨C.time () (F.cfg (Sum.inl entry₁)), htime, ?_, ?_, ?_⟩
  · exact C.cut () (F.cfg (Sum.inl entry₁)) rfl hpre
  · intro u hu j
    have he := C.env () (F.cfg (Sum.inl entry₁)) rfl hpre u hu j
    rw [Finset.mem_Icc] at he
    simp only [C, Contract.seq_lo, Contract.seq_hi, C₁, C₂,
      Contract.ofReaches_lo, Contract.ofReaches_hi, Contract.ofReaches_post,
      Cfg.mapState_workTapePos, PhaseFrame.cfg_eq, hh] at he
    rw [PhaseFrame.cfg_eq, abs_le]
    dsimp only at he ⊢
    omega
  · rw [← hpost]
    exact C.run () (F.cfg (Sum.inl entry₁)) rfl hpre

/-- Finite rows compose sequentially with the second precondition tested on the first result,
adding one dispatch step and their radius allowances.

**Proof sketch.** Use `phase_reaches_seq` for the bounded seam run. Both rows restore the work
heads, so their frame transformations compose with the same property. -/
theorem PhaseRow.seq {I : List Bool → Type}
    {P Q : ∀ {x : List Bool}, I x → PhaseFrame x → Prop}
    {f g : ∀ {x : List Bool}, I x → PhaseFrame x → PhaseFrame x}
    {B₁ E₁ B₂ E₂ : ∀ {x : List Bool}, I x → ℕ}
    (R₁ : PhaseRow I P f B₁ E₁) (R₂ : PhaseRow I Q g B₂ E₂) :
    Nonempty (PhaseRow I (fun i F => P i F ∧ Q i (f i F)) (fun i F => g i (f i F))
      (fun i => B₁ i + 1 + B₂ i) (fun i => E₁ i + E₂ i)) := by
  classical
  letI := R₁.finite
  letI := R₁.decEq
  letI := R₂.finite
  letI := R₂.decEq
  refine ⟨⟨R₁.State ⊕ R₂.State, inferInstance, inferInstance,
    seamCompTM R₁.machine R₁.exit R₂.machine R₂.entry, Sum.inl R₁.entry, Sum.inr R₂.exit,
    ?_, ?_⟩⟩
  · intro x i F hp
    rw [R₂.heads i (f i F) hp.2, R₁.heads i F hp.1]
  · intro x i F hp
    simpa only [Set.image_singleton, Option.map_some] using
      phase_reaches_seq R₁.machine R₂.machine R₁.entry R₁.exit R₂.entry R₂.exit
        {some R₂.exit} F (f i F) (g i (f i F)) (B₁ i) (E₁ i) (B₂ i) (E₂ i)
        (R₁.run i F hp.1) (R₂.run i (f i F) hp.2) (Set.mem_singleton_iff.mpr rfl)
        (R₁.heads i F hp.1)

end WordRAM.Sim
