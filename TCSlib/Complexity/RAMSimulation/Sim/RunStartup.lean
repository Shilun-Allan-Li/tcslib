/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunStep
import TCSlib.Complexity.RAMSimulation.Sim.RunSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Start-up inside the finite simulation host

The start-up runs deterministically under every choice word and takes one stationary dispatch
step into the first RAM instruction. That extra step visits no new work-tape cells, preserving
the leading time and space costs of the word-size witness.

## Main definitions

No additional machine is constructed here.

## Main results

* `WordRAM.Sim.RunSetup.host_initCfg`: the host's initial configuration is the tagged
  start-up entry configuration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; Definition 4.1.)
-/

namespace WordRAM.Sim.RunSetup

open Turing

variable {P : XProgram} {fn : Bool} {Mw : FinTM Bool} (A : RunSetup P fn Mw)

/-- The host starts with the start-up entry tagged by the initial phase; its tapes, heads,
input position and output are exactly the corresponding initial configuration's fields. -/
theorem host_initCfg (x : List Bool) :
    (Turing.Cfg.init A.startEntry x).mapState (fun q => (⟨none, q⟩ : A.State)) =
      A.host.initCfg x := by
  rw [NDTM.initCfg_eq, host_q₀]
  apply Turing.Cfg.ext
  · rw [Cfg.mapState_state, Cfg.init_state, Cfg.init_state, Option.map_some]
  · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
  · funext j p
    rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
  · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]

/-- Any choice word for the start-up, followed by one arbitrary dispatch bit, reaches the
first instruction with the initial RAM encoding. The host's prefix heads are exactly the
start-up heads, and the dispatch endpoint repeats their final positions.

**Proof sketch.** Use `start_correct` for the chosen start-up time and origins. Its phase is
deterministic, so `MultiTapeTM.toNDTM_runWith` identifies every word prefix with that run.
The no-earlier-exit clause supplies the host guard, and `host_phase_dispatch` performs the
one stationary redirect. Encoding and head positions are preserved by its state tag. -/
theorem startup_trajectory (x : List Bool) (W tw sw : ℕ)
    (hW : Mw.ComputesInTime x (Nat.bits W) tw)
    (hS : Mw.tm.spaceUsed (Mw.tm.initCfg x) tw ≤ sw)
    (words : ℕ → List Bool) (hlen : ∀ n, (words n).length = n) (dispatch : ℕ → Bool) :
    ∃ (t : ℕ) (o : Fin 8 → ℤ) (d' : Turing.Cfg (8 + A.extraTapes) Bool A.State x),
      t ≤ tw + A.startCost * (x.length + W ^ 2 + 1) ∧
      A.host.runWith (words t ++ [dispatch t]) (A.host.initCfg x) = d' ∧
      d'.state = some ⟨some (0, false), (A.phases 0).entry⟩ ∧
      Encodes A.width fn {-1} (XCfg.init W x.length) (Fin.castAddEmb A.extraTapes) o d' ∧
      (∀ u ≤ t, ∀ j,
        (A.host.runWith ((words t).take u) (A.host.initCfg x)).workTapePos j =
          (A.startup.runFrom (Turing.Cfg.init A.startEntry x) u).workTapePos j) ∧
      d'.workTapePos = (A.startup.runFrom (Turing.Cfg.init A.startEntry x) t).workTapePos ∧
      A.startup.spaceUsed (Turing.Cfg.init A.startEntry x) t ≤
        sw + A.startCost * (W + (Nat.bits x.length).length + 1) := by
  obtain ⟨t, o, ht, hcut, hexit, he, hspace⟩ := A.start_correct x W tw sw hW hS
  let d₀ : Turing.Cfg (8 + A.extraTapes) Bool A.StartState x := Turing.Cfg.init A.startEntry x
  let e := A.startup.runFrom d₀ t
  let w := words t
  have hw : w.length = t := hlen t
  have hr : (A.phase none).runWith w d₀ = e := by
    rw [phase_none, MultiTapeTM.toNDTM_runWith, hw]
  let q₀ : A.State := ⟨some (0, false), (A.phases 0).entry⟩
  have hred : A.redirect none A.startExit = some q₀ := by
    rw [redirect_none, if_pos rfl]
  have hg : ∀ u < w.length, ∀ q, ((A.phase none).runWith (w.take u) d₀).state = some q →
      A.redirect none q = none := by
    intro u hu q hq
    rw [phase_none, MultiTapeTM.toNDTM_runWith, List.length_take_of_le hu.le] at hq
    have hneq : q ≠ A.startExit := by
      intro heq
      apply hcut u (by omega)
      exact hq.trans (congrArg some heq)
    rw [redirect_none, if_neg hneq]
  obtain ⟨hpre, hfinal⟩ := A.host_phase_dispatch none d₀ e w hr A.startExit hexit q₀ hred hg
    (dispatch t)
  rw [host_initCfg] at hpre hfinal
  refine ⟨t, o, e.mapState (fun _ => q₀), ht, hfinal, ?_, ?_, ?_, ?_, hspace⟩
  · rw [Cfg.mapState_state, hexit, Option.map_some]
  · exact (encodes_mapState A.width fn {-1} (XCfg.init W x.length)
      (Fin.castAddEmb A.extraTapes) o e (fun _ => q₀)).mp he
  · intro u hu j
    have huw : u ≤ w.length := by omega
    rw [hpre u huw, Cfg.mapState_workTapePos, phase_none,
      MultiTapeTM.toNDTM_runWith, List.length_take_of_le huw]
  · funext j
    rw [Cfg.mapState_workTapePos]

/-- Start-up and its dispatch enter the initial RAM encoding with the original additive
startup space bound. The dispatch visits no cell not already visited by the start-up.

**Proof sketch.** Use `startup_trajectory`. Through time `t` the host heads are the start-up
heads; the extra dispatch step repeats the time-`t` positions. Thus
`runSpace_eq_of_clamped_heads` identifies their visited sets exactly, preserving the leading
`sw` term rather than multiplying it by a constant. -/
theorem startup_run (x : List Bool) (W tw sw : ℕ)
    (hW : Mw.ComputesInTime x (Nat.bits W) tw)
    (hS : Mw.tm.spaceUsed (Mw.tm.initCfg x) tw ≤ sw)
    (words : ℕ → List Bool) (hlen : ∀ n, (words n).length = n) (dispatch : ℕ → Bool) :
    ∃ (t : ℕ) (o : Fin 8 → ℤ) (d' : Turing.Cfg (8 + A.extraTapes) Bool A.State x),
      t ≤ tw + A.startCost * (x.length + W ^ 2 + 1) ∧
      A.host.runWith (words t ++ [dispatch t]) (A.host.initCfg x) = d' ∧
      d'.state = some ⟨some (0, false), (A.phases 0).entry⟩ ∧
      Encodes A.width fn {-1} (XCfg.init W x.length) (Fin.castAddEmb A.extraTapes) o d' ∧
      A.host.spaceUsedWith (words t ++ [dispatch t]) (A.host.initCfg x) ≤
        sw + A.startCost * (W + (Nat.bits x.length).length + 1) := by
  obtain ⟨t, o, d', ht, hr, hd, he, hprefix, hheads, hs⟩ :=
    A.startup_trajectory x W tw sw hW hS words hlen dispatch
  have hlen' : (words t ++ [dispatch t]).length = t + 1 := by
    rw [List.length_append, hlen t, List.length_singleton]
  have hspace : A.host.spaceUsedWith (words t ++ [dispatch t]) (A.host.initCfg x) =
      A.startup.spaceUsed (Turing.Cfg.init A.startEntry x) t := by
    apply runSpace_eq_of_clamped_heads
    · rw [hlen']
      exact Nat.le_succ _
    · intro u hu j
      by_cases hut : u ≤ t
      · have huw : u ≤ (words t).length := by rw [hlen]; exact hut
        rw [List.take_append_of_le_length huw, hprefix u hut j, min_eq_left hut]
      · have hue : u = t + 1 := by rw [hlen'] at hu; omega
        have hwhole : (words t ++ [dispatch t]).length ≤ u := by rw [hlen', hue]
        rw [List.take_of_length_le hwhole, hr, hheads, min_eq_right (by omega)]
  exact ⟨t, o, d', ht, hr, hd, he, hspace.trans_le hs⟩

end WordRAM.Sim.RunSetup
