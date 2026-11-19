/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBranchMachines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Frame contracts inside the registered phase host

A native frame contract runs inside a tagged phase until its live exit, then dispatches to its
redirect target. Every host exit set confined to other phases is avoided before that endpoint.
The bounded-run composition lemma also concatenates two contracts of the same host.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_reaches_inPhase`: place a bounded frame contract in the phase host.
* `WordRAM.Sim.phase_reaches_trans`: concatenate bounded runs of the same machine.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- Binding a frame's live control to one live target installs that target without changing
any frame fields. -/
theorem phase_frame_bindState {S H : Type} {x : List Bool} (F : PhaseFrame x)
    (q : S) (r : H) (f : S → Option H) (hf : f q = some r) :
    (F.cfg q).bindState f = F.cfg r := by
  apply Cfg.ext
  · simpa only [Cfg.bindState_state, PhaseFrame.cfg_eq] using hf
  · simp only [Cfg.bindState_inputPos, PhaseFrame.cfg_eq]
  · funext j z
    simp only [Cfg.bindState_workTapes, PhaseFrame.cfg_eq]
  · funext j
    simp only [Cfg.bindState_workTapePos, PhaseFrame.cfg_eq]
  · simp only [Cfg.bindState_output, PhaseFrame.cfg_eq]

/-- A native bounded run dispatches once inside the phase host, retaining its radius and
avoiding any host exit set consisting entirely of live states in other phases.

**Proof sketch.** Turn the native row into `Contract.ofReaches` and place it with
`Contract.inPhase`. Its published time, post and envelope equations give the endpoint and
bounds. For the possibly larger host cut, `phaseHostTM_run_le` tags the native prefix by its
source phase; it cannot meet an exit tagged by another phase. -/
theorem phase_reaches_inPhase {I : Type} {Ph : I → Type} {x : List Bool}
    (Mf : (p : I) → MultiTapeTM 8 Bool (Ph p)) (q₀ : Σ p, Ph p)
    (red : (p : I) → Ph p → Option (Σ p, Ph p)) (p : I) (entry exit : Ph p)
    (X : Set (Option (Ph p))) (F G : PhaseFrame x) (B E : ℕ)
    (hr : ReachesWithin (Mf p) (F.cfg entry) X B E (G.cfg exit))
    (hx : some exit ∈ X) (hnone : none ∉ X)
    (hred : ∀ q, some q ∉ X → red p q = none)
    (hsome : ∀ q, some q ∈ X → ∃ r, red p q = some r ∧ r.1 ≠ p)
    (target : Σ p, Ph p) (htarget : red p exit = some target)
    (Y : Set (Option (Σ p, Ph p))) (hYnone : none ∉ Y)
    (hYtag : ∀ r, some r ∈ Y → r.1 ≠ p) :
    ReachesWithin (phaseHostTM Mf q₀ red) (F.cfg ⟨p, entry⟩) Y (B + 1) E
      (G.cfg target) := by
  classical
  let C := Contract.ofReaches (M := Mf p) (entry := entry) (X := X)
    (fun (_ : Unit) d => d = F.cfg entry) (fun _ _ => B) (fun _ _ => E)
    (fun _ _ => G.cfg exit)
    (by intro u d hd he; subst d; exact hr)
    (by intro u d hd he; simpa only [PhaseFrame.cfg_eq] using hx)
  let H := Contract.inPhase Mf q₀ red p C hnone hred hsome
  have hpre : H.pre () (F.cfg ⟨p, entry⟩) := by
    simp only [H, Contract.inPhase_pre, C, Contract.ofReaches_pre, PhaseFrame.cfg_mapState]
  have hpost : H.post () (F.cfg ⟨p, entry⟩) = G.cfg target := by
    simp only [H, Contract.inPhase_post, C, Contract.ofReaches_post, PhaseFrame.cfg_mapState]
    exact phase_frame_bindState G exit target (red p) htarget
  have hF : (F.cfg entry).state = some entry := by simp only [PhaseFrame.cfg_eq]
  have hH : (F.cfg (⟨p, entry⟩ : Σ p, Ph p)).state = some ⟨p, entry⟩ := by
    simp only [PhaseFrame.cfg_eq]
  have hpC : C.pre () (F.cfg entry) := by simp only [C, Contract.ofReaches_pre]
  have ht : C.time () (F.cfg entry) ≤ B := by
    apply Contract.ofReaches_time_le
    · exact hF
    · rfl
  have htime : H.time () (F.cfg ⟨p, entry⟩) = C.time () (F.cfg entry) + 1 := by
    simp only [H, Contract.inPhase_time, PhaseFrame.cfg_mapState]
  have hguard : ∀ u < C.time () (F.cfg entry), ∀ q,
      ((Mf p).runFrom (F.cfg entry) u).state = some q → red p q = none := by
    intro u hu q hq
    apply hred q
    intro hm
    exact C.cut () (F.cfg entry) hF hpC u hu (by rw [hq]; exact hm)
  have hprefix := phaseHostTM_run_le Mf q₀ red p (F.cfg entry)
    (C.time () (F.cfg entry)) hguard
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨H.time () (F.cfg ⟨p, entry⟩), by rw [htime]; omega, ?_, ?_, ?_⟩
  · intro u hu hm
    rw [htime] at hu
    have hpref := hprefix u (by omega)
    rw [PhaseFrame.cfg_mapState] at hpref
    rw [hpref, Cfg.mapState_state] at hm
    cases hs : ((Mf p).runFrom (F.cfg entry) u).state with
    | none => exact hYnone (by simpa only [hs, Option.map_none] using hm)
    | some q =>
      exact hYtag ⟨p, q⟩ (by simpa only [hs, Option.map_some] using hm) rfl
  · intro u hu j
    have he := H.env () (F.cfg ⟨p, entry⟩) hH hpre u hu j
    rw [Finset.mem_Icc] at he
    simp only [H, Contract.inPhase_lo, Contract.inPhase_hi, C, Contract.ofReaches_lo,
      Contract.ofReaches_hi, Cfg.mapState_workTapePos, PhaseFrame.cfg_eq] at he
    rw [PhaseFrame.cfg_eq, abs_le]
    dsimp only at he ⊢
    omega
  · rw [← hpost]
    exact H.run () (F.cfg ⟨p, entry⟩) hH hpre

/-- Two bounded runs of the same machine concatenate without a dispatch step when their frame
endpoints agree. Restored intermediate heads give the sum of their radius allowances.

**Proof sketch.** Read both witnesses with `reachesWithin_iff` and put their head predicates
inside the summed radius about the original frame. Restored intermediate heads identify the
second center. Convert with `segment_iff`, cite `Segment.trans`, and read the resulting segment
back as `ReachesWithin`. -/
theorem phase_reaches_trans {S : Type} {x : List Bool} (M : MultiTapeTM 8 Bool S)
    (q₀ q₁ q₂ : S) (X : Set (Option S)) (F G H : PhaseFrame x) (B₁ E₁ B₂ E₂ : ℕ)
    (h₁ : ReachesWithin M (F.cfg q₀) X B₁ E₁ (G.cfg q₁))
    (h₂ : ReachesWithin M (G.cfg q₁) X B₂ E₂ (H.cfg q₂))
    (hh : G.workTapePos = F.workTapePos) :
    ReachesWithin M (F.cfg q₀) X (B₁ + B₂) (E₁ + E₂) (H.cfg q₂) := by
  obtain ⟨t₁, ht₁, hc₁, he₁, hr₁⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h₁
  obtain ⟨t₂, ht₂, hc₂, he₂, hr₂⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h₂
  let P := fun p : Fin 8 → ℤ => ∀ j, |p j - F.workTapePos j| ≤ ((E₁ + E₂ : ℕ) : ℤ)
  have hs₁ : Segment M X P (F.cfg q₀) (G.cfg q₁) t₁ := by
    apply (segment_iff _ _ _ _ _ _).mpr
    refine ⟨hr₁, hc₁, ?_⟩
    intro u hu j
    have he := he₁ u hu j
    simp only [PhaseFrame.cfg_eq] at he ⊢
    exact he.trans (show (E₁ : ℤ) ≤ ((E₁ + E₂ : ℕ) : ℤ) by
      exact_mod_cast Nat.le_add_right E₁ E₂)
  have hs₂ : Segment M X P (G.cfg q₁) (H.cfg q₂) t₂ := by
    apply (segment_iff _ _ _ _ _ _).mpr
    refine ⟨hr₂, hc₂, ?_⟩
    intro u hu j
    have he := he₂ u hu j
    simp only [PhaseFrame.cfg_eq, hh] at he ⊢
    exact he.trans (show (E₂ : ℤ) ≤ ((E₁ + E₂ : ℕ) : ℤ) by
      exact_mod_cast Nat.le_add_left E₂ E₁)
  obtain ⟨hr, hc, he⟩ := (segment_iff _ _ _ _ _ _).mp (Segment.trans hs₁ hs₂)
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t₁ + t₂, by omega, hc, ?_, hr⟩
  intro u hu j
  simpa only [PhaseFrame.cfg_eq] using he u hu j

end WordRAM.Sim
