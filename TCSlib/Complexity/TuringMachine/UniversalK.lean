/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Codes2Tape
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `k`-generic universal machine (U2)

[AB09, §1.4.1 and Theorem 1.9]: one universal machine for codes of `k`-work-tape binary
machines, for every `k`, with an overhead linear in the simulated time and a constant depending
on the code only. At `k = 2` it is the two-tape universal machine of the time hierarchy at
`f log f` (plan §2.1; the Hennie–Stearns conversion of [AB09, §1.7] lands machines there); at
`k = 1` it is the self-application universal `U₀` of the space hierarchy
(`Turing.exists_selfUniversal`, its `k = 1` corollary) and the code-first evaluator of
`Turing.universal` (the U-1 re-derivation, deferred). Design: `audits/evidence/u2/U2-design.md`;
the user's decisions of 2026-10-14 (`backlog.md` RD-5).

**Status.** The scheme interface and its two instances are defined and proved, and so is the
startup `Turing.exists_selfStartupTMK`; the other two machine contracts are sorried with their
proof sketches. Their fill builds on H2's step block and its forwarding round loop
`Turing.StepBlock.exists_forwardLoopTM` (H2-F, `Build/StepBlockForward.lean`).

## Design

* **One construction, generic in `k`.** The step block `Turing.StepBlock.roundTM k` simulates one
  transition of any `k`-tape table held as data at a cost `≤ 50 · (|table| + 1)`, a constant for
  a fixed code; H2-F forwards the emissions. Nothing here is specific to one or two work tapes.
* **The scheme interface** `Turing.EffectiveCodeK k`: a total decoding into `k`-tape machines and
  a canonizer computing the fixed serialization `Turing.serializeK` in arbitrary time. The
  received one-tape scheme and the Z3 two-tape scheme are instances. No uniformity is assumed:
  per-code constants absorb the canonizer's time.
* **Two input layouts.** Self-application (`Turing.exists_selfUniversalK`): on `pairEncode α w`
  the coded machine runs on that same input, through the native device, with no copy and no
  position counter. Code first (`Turing.universalK`): on `pairEncode α x` it runs on `x`,
  through H5's bounded-prefix ruler device, at a constant cost per step for a fixed code.
* **Both directions** in both layouts: forward time (and, for self-application, space) ledgers,
  and the converse that every completed output of the universal machine is one of the coded
  machine's.

## Main definitions

* `Turing.EffectiveCodeK`, `Turing.EffectiveCodeK.toFinTM` — the `k`-tape scheme interface;
  `Turing.EffectiveCodeK.ofSerialize` — its constructor from a scheme with its own serialization.
* `Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK` — the received one- and
  two-tape schemes as `k`-tape schemes.

## Main results

* `Turing.EffectiveMachineCode.toK_toFinTM`, `Turing.EffectiveMachineCode2.toK_toFinTM`,
  `Turing.EffectiveMachineCode.toK_machine`, `Turing.EffectiveMachineCode2.toK_machine` — the
  decoded machines agree, by definition.
* `Turing.exists_selfStartupTMK` — the startup, ending at the step block's seam (proved).
* `Turing.exists_selfUniversalK` — U2-U, the self-application universal machine, with time
  `C · (t + 1)`, space `C · (s + 1)` and the converse (sorried).
* `Turing.universalK` — U2-E, the code-first evaluator with time `C · (t + 1)` and the converse
  (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, machine codes; §1.4.1, Theorem 1.9 and its proof:
  the universal machine simulates one step of `M` in a number of steps depending only on `M`'s
  table; §1.7, the two-tape simulation; Exercise 4.1, the space-bounded universal machine.)
-/

namespace Turing

/-! ## The `k`-tape scheme interface -/

/-- **An effective scheme for `k`-work-tape codes** [AB09, §1.4]: a total decoding of every
string `α` into a `k`-work-tape binary machine `machine α` with state space
`Fin (numStates α + 1)`, together with a machine of this development, the canonizer, that
computes from `α` the fixed `k`-record serialization `Turing.serializeK (machine α)` within an
arbitrary time bound `canonizerTime`. As for `Turing.EffectiveMachineCode` (Argument A), the
canonizer targets the fixed, scheme-independent serialization, and its time bound is arbitrary:
fixed-code consumers absorb it into their constants. The received schemes are instances
(`Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK`). -/
structure EffectiveCodeK (k : ℕ) where
  /-- one less than the number of states of the machine a string denotes -/
  numStates : List Bool → ℕ
  /-- the machine a string denotes -/
  machine : (α : List Bool) → MultiTapeTM k Bool (Fin (numStates α + 1))
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serializeK ∘ machine` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => serializeK (machine α)) canonizerTime

/-- The bundled machine a string denotes in a `k`-tape scheme: `k` work tapes, the states
`Fin (numStates α + 1)`, the decoded machine. -/
def EffectiveCodeK.toFinTM {k : ℕ} (E : EffectiveCodeK k) (α : List Bool) : FinTM Bool where
  k := k
  State := Fin (E.numStates α + 1)
  tm := E.machine α

/-- **A `k`-tape scheme from a scheme with its own serialization** (the common constructor of
the two instances below): given a type of coded machines with their state counts and their
`k`-tape machines, a serialization equal to `serializeK` of the machine, a decoding, and a
canonizer computing the serialization of the decoded machine, the `k`-tape scheme with the same
decoding and canonizer. -/
def EffectiveCodeK.ofSerialize {k : ℕ} {Code : Type} (numStates : Code → ℕ)
    (tm : (M : Code) → MultiTapeTM k Bool (Fin (numStates M + 1))) (serialize : Code → List Bool)
    (serialize_eq : ∀ M, serialize M = serializeK (tm M)) (decode : List Bool → Code)
    (canonizer : FinTM Bool) (canonizerTime : ℕ → ℕ)
    (h : canonizer.ComputesFunInTime (fun α => serialize (decode α)) canonizerTime) :
    EffectiveCodeK k where
  numStates α := numStates (decode α)
  machine α := tm (decode α)
  canonizer := canonizer
  canonizerTime := canonizerTime
  canonizer_computes := by
    have e : (fun α => serialize (decode α)) = fun α => serializeK (tm (decode α)) :=
      funext fun α => serialize_eq (decode α)
    exact e ▸ h

/-- **The received one-tape scheme as a `k`-tape scheme** (`k = 1`): the same decoding and the
same canonizer, whose target `CodeTM.serialize` is `serializeK` at one work tape
(`Turing.oneTapeMachineFormat.serialize_eq`). [AB09, §1.4] -/
def EffectiveMachineCode.toK (c : EffectiveMachineCode) : EffectiveCodeK 1 :=
  EffectiveCodeK.ofSerialize CodeTM.numStates CodeTM.tm CodeTM.serialize
    oneTapeMachineFormat.serialize_eq c.decode c.canonizer c.canonizerTime c.canonizer_computes

/-- **The Z3 two-tape scheme as a `k`-tape scheme** (`k = 2`): the same decoding and the same
canonizer, whose target `Code2TM.serialize` is `serializeK` at two work tapes
(`Turing.Code2TM.serialize_eq_serializeK`). [AB09, §1.4] -/
def EffectiveMachineCode2.toK (c : EffectiveMachineCode2) : EffectiveCodeK 2 :=
  EffectiveCodeK.ofSerialize Code2TM.numStates Code2TM.tm Code2TM.serialize
    Code2TM.serialize_eq_serializeK c.decode c.canonizer c.canonizerTime c.canonizer_computes

/-- The one-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode.toK_toFinTM (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := rfl

/-- The two-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode2.toK_toFinTM (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := rfl

/-- The one-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode.toK_machine (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := rfl

/-- The two-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode2.toK_machine (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := rfl

/-! ## U2-S: the startup -/

/-- The canonizer, with the public cleanup machine restarted in its cleaning state. -/
private def ss_cleanCanonizer (F : FinTM Bool) : FinTM Bool where
  k := F.k + F.k
  State := Complexity.LogProg.CleanSt F.State F.k
  tm := { Complexity.LogProg.cleanTM F.tm F.tm.q₀ with q₀ := .init F.tm.q₀ }

/-- The bundled cleanup run is the run from the public cleaning entry. -/
private theorem ss_cleanCanonizer_run (F : FinTM Bool) (α : List Bool) (t : ℕ) :
    (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t =
      (Complexity.LogProg.cleanTM F.tm F.tm.q₀).runFrom
        (Cfg.init (.init F.tm.q₀) α) t := by
  change ({ Complexity.LogProg.cleanTM F.tm F.tm.q₀ with q₀ := .init F.tm.q₀ } :
    MultiTapeTM (F.k + F.k) Bool (Complexity.LogProg.CleanSt F.State F.k)).runFrom _ _ = _
  rw [MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀]

/-- Cleanup preserves a completed computation and blanks every work tape.

**Proof sketch.** Bound the original run's visited set on each tape by their finite
maximum. Apply the public cleanup theorem, then use the restart equations. -/
private theorem ss_cleanCanonizer_halts (F : FinTM Bool) (α out : List Bool) (t : ℕ)
    (h : F.ComputesInTime α out t) :
    ∃ u, ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).state =
        none ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).output =
        out ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).workTapePos =
        (fun _ => 0) := by
  classical
  have hc := (FinTM.computesInTime_iff F α out t).mp h
  rw [MultiTapeTM.initCfg_eq] at hc
  let s := Finset.univ.sup fun i : Fin F.k =>
    (F.tm.visitedByTapeHead (Cfg.init F.tm.q₀ α) t i).card
  obtain ⟨u, hu, hout, hblank, hpos, _⟩ :=
    Complexity.LogProg.cleanTM_run F.tm F.tm.q₀ F.tm.q₀ α t hc.1 s
      (fun i => Finset.le_sup
        (f := fun j : Fin F.k => (F.tm.visitedByTapeHead (Cfg.init F.tm.q₀ α) t j).card)
        (Finset.mem_univ i))
  refine ⟨u, ?_⟩
  simpa only [ss_cleanCanonizer_run] using ⟨hu, hout.trans hc.2, hblank, hpos⟩

/-- A string-dependent time is bounded by a function of string length. -/
private theorem ss_lengthBound (time : List Bool → ℕ) :
    ∃ bound : ℕ → ℕ, ∀ α, time α ≤ bound α.length := by
  classical
  refine ⟨fun n => Finset.univ.sup (fun f : Fin n → Bool => time (List.ofFn f)), ?_⟩
  intro α
  simpa only [List.ofFn_get] using
    (Finset.le_sup (f := fun f : Fin α.length → Bool => time (List.ofFn f))
      (Finset.mem_univ α.get))

/-- A total canonizer remains total after cleanup, at a bound depending only on length;
the same bound leaves every work tape blank and every work head at zero.

**Proof sketch.** Choose each input's cleaned halting time and take a finite maximum
at each input length. Absorbing halting preserves the output and cleanup at the maximum. -/
private theorem ss_cleanCanonizer_computes (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) :
    ∃ bound, (ss_cleanCanonizer F).ComputesFunInTime f bound ∧ ∀ α,
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
        (bound α.length)).workTapes = (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
        (bound α.length)).workTapePos = (fun _ => 0) := by
  classical
  have hex := fun α => ss_cleanCanonizer_halts F α (f α) (τ α.length)
    ((FinTM.computesFunInTime_iff F f τ).mp hF α)
  choose time htime using hex
  obtain ⟨bound, hbound⟩ := ss_lengthBound time
  have hfreeze (α : List Bool) :
      (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) (bound α.length) =
        (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) (time α) := by
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (hbound α)
    calc
      _ = (ss_cleanCanonizer F).tm.runFrom
          ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
            (time α)) extra := by rw [heq, MultiTapeTM.runFrom_add]
      _ = _ := MultiTapeTM.runFrom_of_halt _ (htime α).1
  refine ⟨bound, (FinTM.computesFunInTime_iff _ _ _).mpr ?_, ?_⟩
  · intro α
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [hfreeze α]
    exact ⟨(htime α).1, (htime α).2.1⟩
  · intro α
    rw [hfreeze α]
    exact (htime α).2.2

/-- A buffered second-phase configuration halts exactly when its source does. -/
private theorem ss_bufferedHalt_iff (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    (FinTM.bufferedSecondCfg M₁ M₂ c b p tapes heads).state = none ↔ c.state = none := by
  rw [FinTM.bufferedSecondCfg_state]
  simp only [FinTM.bufferedCompTM_State, Option.map_eq_none_iff]

/-- A first halt of the virtual canonizer is a first halt of the prefix canonizer,
after the fixed prefix phase, uniformly over all suffixes.

**Proof sketch.** The exact prefix formula identifies the state after the prefix phase.
Before that phase ends, absorbing halting and its live final state exclude a halt. -/
private theorem ss_prefix_first_halt (F : FinTM Bool) (α : List Bool) (t : ℕ)
    (hhalt : (F.tm.runFrom (F.tm.initCfg α) t).state = none)
    (hlive : ∀ u < t, (F.tm.runFrom (F.tm.initCfg α) u).state ≠ none) (w : List Bool) :
    ((prefixCanonTM F).tm.runFrom ((prefixCanonTM F).tm.initCfg (pairEncode α w))
      (3 * α.length + 4 + t)).state = none ∧
    ∀ u < 3 * α.length + 4 + t,
      ((prefixCanonTM F).tm.runFrom ((prefixCanonTM F).tm.initCfg (pairEncode α w)) u).state ≠
        none := by
  rw [prefixCanonTM_eq]
  constructor
  · obtain ⟨b, hb⟩ := prefixCanon_run F α w t
    simp only [prefixCanonTM_eq] at hb
    rw [hb, ss_bufferedHalt_iff]
    exact hhalt
  · intro u hu
    by_cases hpre : u < 3 * α.length + 4
    · have hs := prefixCanon_start F α w
      simp only [prefixCanonTM_eq] at hs
      have hstart :
          ((FinTM.bufferedCompTM universalPrefixTM F).tm.runFrom
            ((FinTM.bufferedCompTM universalPrefixTM F).tm.initCfg (pairEncode α w))
            (3 * α.length + 4)).state ≠ none := by
        intro h
        rw [hs, ss_bufferedHalt_iff, MultiTapeTM.initCfg_eq, Cfg.init_state] at h
        exact Option.some_ne_none F.tm.q₀ h
      exact MultiTapeTM.runFrom_state_ne_none_of_le _ _ _ hstart u (by omega)
    · obtain ⟨b, hb⟩ := prefixCanon_run F α w (u - (3 * α.length + 4))
      simp only [prefixCanonTM_eq] at hb
      rw [Nat.add_sub_of_le (by omega : 3 * α.length + 4 ≤ u)] at hb
      intro h
      rw [hb, ss_bufferedHalt_iff] at h
      exact hlive (u - (3 * α.length + 4)) (by omega) h

/-- The cleaned canonizer's first halt has the completed output and clean scratch.

**Proof sketch.** The public first-halt theorem identifies its configuration with the
one at the cleaned length bound, including all fields of that configuration. -/
private theorem ss_cleanCanonizer_first_halt (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) (α : List Bool) :
    ∃ t, ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).state =
        none ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).output =
        f α ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapePos =
        (fun _ => 0) ∧
      ∀ u < t, ((ss_cleanCanonizer F).tm.runFrom
        ((ss_cleanCanonizer F).tm.initCfg α) u).state ≠ none := by
  obtain ⟨bound, hfun, hclean⟩ := ss_cleanCanonizer_computes F f τ hF
  have hc := (FinTM.computesInTime_iff _ _ _ _).mp
    ((FinTM.computesFunInTime_iff _ _ _).mp hfun α)
  obtain ⟨t, _, hbefore, hsame⟩ := MultiTapeTM.exists_first_halt _ _ hc.1
  refine ⟨t, ?_, ?_, ?_, ?_, hbefore⟩
  · rw [hsame]
    exact hc.1
  · rw [hsame]
    exact hc.2
  · rw [hsame]
    exact (hclean α).1
  · rw [hsame]
    exact (hclean α).2

/-- Capturing a fresh run starts with blank host tapes and zero work heads.

**Proof sketch.** Partition host tapes into selected tapes, the capture tape, and the frame.
The selected tapes inherit the blank initial configuration; the empty captured output makes
its tape blank; the frame is blank by construction. Compare all configuration fields. -/
private theorem ss_captureInitial {m n : ℕ} {S : Type} (M : MultiTapeTM m Bool S)
    (ι : Fin m ↪ Fin n) (cap : Fin n) (hcap : cap ∉ Set.range ι) (x : List Bool) :
    (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
      (M.initCfg x)).mapState Sum.inl =
      Cfg.init (Sum.inl M.q₀ : S ⊕ Unit) x := by
  classical
  have hfields (j : Fin n) :
      (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (M.initCfg x)).workTapes j = (fun _ => none) ∧
      (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (M.initCfg x)).workTapePos j = 0 := by
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedSilentCfg_selected_tape, embedSilentCfg_selected_pos,
        MultiTapeTM.initCfg_eq]
      exact ⟨funext fun z => Cfg.init_workTapes _ _ i z, Cfg.init_workTapePos _ _ i⟩
    · by_cases he : j = cap
      · subst j
        have hh := embedSilentCfg_cap ι cap hcap (fun _ _ => none) (fun _ => 0)
          [] [] (M.initCfg x)
        simpa only [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append,
          FinTM.bufferTape_nil, List.length_nil, Nat.cast_zero] using hh
      · exact embedSilentCfg_unselected ι cap (fun _ _ => none) (fun _ => 0)
          [] [] (M.initCfg x) j hj he
  apply Cfg.ext
  · rw [Cfg.mapState_state, embedSilentCfg_state, MultiTapeTM.initCfg_eq,
      Cfg.init_state, Option.map_some, Cfg.init_state]
  · rw [Cfg.mapState_inputPos, embedSilentCfg_inputPos, MultiTapeTM.initCfg_eq,
      Cfg.init_inputPos, Cfg.init_inputPos]
  · funext j z
    rw [Cfg.mapState_workTapes, Cfg.init_workTapes, (hfields j).1]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, (hfields j).2]
  · rw [Cfg.mapState_output, embedSilentCfg_output, Cfg.init_output]

/-- The returning capture host, restarted in the source's initial state. -/
private def ss_captureTM (F : FinTM Bool) {n : ℕ} (ι : Fin F.k ↪ Fin n) (cap : Fin n) :
    MultiTapeTM n Bool (F.State ⊕ Unit) :=
  { embedSilentRetTM ι cap F.tm with q₀ := Sum.inl F.tm.q₀ }

/-- The returning capture reaches its anchor exactly at the source's first halt and
is silent throughout. Its final tapes are the public silent embedding's exact tapes.

**Proof sketch.** Identify the blank initial configuration, use the returning embedding's
through-halt contract, and project its output field before and at the return. -/
private theorem ss_capture_run (F : FinTM Bool) {n : ℕ} (ι : Fin F.k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (x : List Bool) (t : ℕ)
    (hlive : ∀ u < t, (F.tm.runFrom (F.tm.initCfg x) u).state ≠ none)
    (hhalt : (F.tm.runFrom (F.tm.initCfg x) t).state = none) :
    (ss_captureTM F ι cap).runFrom ((ss_captureTM F ι cap).initCfg x) t =
      { embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
          (F.tm.runFrom (F.tm.initCfg x) t) with state := some (Sum.inr ()) } ∧
    (∀ u < t, ((ss_captureTM F ι cap).runFrom
      ((ss_captureTM F ι cap).initCfg x) u).state ≠ some (Sum.inr ())) ∧
    (∀ u ≤ t, ((ss_captureTM F ι cap).runFrom
      ((ss_captureTM F ι cap).initCfg x) u).output = []) := by
  have hinit : (F.tm.initCfg x).state ≠ none := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have hr := embedSilentRetTM_run ι cap hcap F.tm (fun _ _ => none) (fun _ => 0)
    [] [] (F.tm.initCfg x) t hinit hlive hhalt
  simp only [MultiTapeTM.initCfg_eq] at hr
  simp only [ss_captureTM, MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀,
    ← ss_captureInitial F.tm ι cap hcap x]
  refine ⟨hr.2.1, hr.2.2, ?_⟩
  intro u hu
  rcases lt_or_eq_of_le hu with hlt | rfl
  · rw [hr.1 u hlt, Cfg.mapState_output, embedSilentCfg_output]
  · simp only [hr.2.1, embedSilentCfg_output]

/-- With the prefix parser's empty left block, index zero is the buffer and every other
index belongs to the constant right block.

**Proof sketch.** Cast the composite index to the public block partition. Its value is either
zero, the buffer index, or one plus an index of the right block; apply the corresponding
published projection equation. -/
private theorem ss_tapeBlocks_zeroLeft {A : Type} (F : FinTM Bool)
    (left : Fin universalPrefixTM.k → A) (buffer right : A)
    (i : Fin (FinTM.bufferedCompTM universalPrefixTM F).k) :
    FinTM.tapeBlocks left buffer (fun _ : Fin F.k => right)
        (Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i) =
      if i.val = 0 then buffer else right := by
  have hp := universalPrefixTM_k
  have hk := FinTM.bufferedCompTM_k universalPrefixTM F
  have hi := i.isLt
  by_cases hz : i.val = 0
  · have he : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i =
        Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k (0 : Fin 1)) := by
      apply Fin.ext
      simp only [Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, Fin.val_zero]
      omega
    rw [he, FinTM.tapeBlocks_buffer, if_pos hz]
  · let j : Fin F.k := ⟨i.val - 1, by omega⟩
    have he : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i =
        Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 j) := by
      apply Fin.ext
      simp only [Fin.coe_cast, Fin.coe_natAdd]
      dsimp only [j]
      omega
    rw [he, FinTM.tapeBlocks_right, if_neg hz]

/-- After the canonizer's work tapes have been cleared, the prefix composite keeps only
the original code buffer, whose head is the virtual input position minus one.

**Proof sketch.** Read the exact prefix run through the published composite fields at its own
index type. The empty parser block leaves index zero for the code buffer; the cleaned right
block contributes blank tapes and zero heads. -/
private theorem ss_prefix_return_fields (F : FinTM Bool) (α w : List Bool) (t : ℕ)
    (hblank : (F.tm.runFrom (F.tm.initCfg α) t).workTapes = (fun _ _ => none))
    (hheads : (F.tm.runFrom (F.tm.initCfg α) t).workTapePos = (fun _ => 0)) :
    let c := F.tm.runFrom (F.tm.initCfg α) t
    let G := FinTM.bufferedCompTM universalPrefixTM F
    let d := G.tm.runFrom (G.tm.initCfg (pairEncode α w)) (3 * α.length + 4 + t)
    d.inputPos.val = 2 * α.length + 3 ∧ d.output = c.output ∧
      (∀ i, d.workTapes i = if i.val = 0 then FinTM.bufferTape α else (fun _ => none)) ∧
      ∀ i, d.workTapePos i = if i.val = 0 then (c.inputPos.val : ℤ) - 1 else 0 := by
  dsimp only
  obtain ⟨b, hb⟩ := prefixCanon_run F α w t
  simp only [prefixCanonTM_eq] at hb
  rw [hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FinTM.bufferedSecondCfg_inputPos]
  · rw [FinTM.bufferedSecondCfg_output]
  · intro i
    rw [FinTM.bufferedSecondCfg_workTapes_cast, hblank]
    exact ss_tapeBlocks_zeroLeft F _ _ _ i
  · intro i
    rw [FinTM.bufferedSecondCfg_workTapePos_cast, hheads]
    exact ss_tapeBlocks_zeroLeft F _ _ _ i

/-- Capturing the cleaned prefix has a code-dependent first return, silence, and a
uniform space bound. The final configuration is expressed through the prefix run;
its cleaned source data are retained for the layout normalization below.

**Proof sketch.** Select the cleaned canonizer's first halt before quantifying the suffix.
The prefix first-halt lemma and the returning capture contract give the claimed run. -/
private theorem ss_capturedPrefix_run (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) {n : ℕ}
    (ι : Fin (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (α : List Bool) :
    let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)
    let R := ss_captureTM G ι cap
    ∃ t : ℕ,
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).output =
        f α ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapePos =
        (fun _ => 0) ∧ ∀ w : List Bool,
      R.runFrom (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) =
        { embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
            (G.tm.runFrom (G.tm.initCfg (pairEncode α w))
              (3 * α.length + 4 + t)) with state := some (Sum.inr ()) } ∧
      (∀ u < 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
      R.spaceUsed (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) ≤
        n * (3 * α.length + 4 + t + 1) := by
  dsimp only
  obtain ⟨t, ht, hout, hblank, hheads, hlive⟩ := ss_cleanCanonizer_first_halt F f τ hF α
  refine ⟨t, hout, hblank, hheads, fun w => ?_⟩
  have hp := ss_prefix_first_halt (ss_cleanCanonizer F) α t ht hlive w
  simp only [prefixCanonTM_eq] at hp
  have hr := ss_capture_run
    (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)) ι cap hcap
    (pairEncode α w) (3 * α.length + 4 + t) hp.2 hp.1
  exact ⟨hr.1, hr.2.1, hr.2.2, MultiTapeTM.spaceUsed_le_mul_succ _ _ _⟩

/-- The returned capture has exactly the code buffer, the captured result, and blank scratch.
Its code-buffer head is a code-dependent position between minus one and the code length.

**Proof sketch.** Retain the cleaned source's output and blankness at the first halt chosen
before the suffix. Project the exact captured return through the selected, capture, and frame
equations, and normalize the source fields with the cast-indexed composite equations. The
source input position determines the buffer head independently of the suffix. -/
private theorem ss_capturedPrefix_fields (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) {n : ℕ}
    (ι : Fin (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (α : List Bool) :
    let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)
    let R := ss_captureTM G ι cap
    ∃ t p : ℕ, p ≤ α.length + 1 ∧ ∀ w : List Bool,
      let d := R.runFrom (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t)
      d.state = some (Sum.inr ()) ∧ d.inputPos.val = 2 * α.length + 3 ∧
      (∀ i, d.workTapes (ι i) =
        if i.val = 0 then FinTM.bufferTape α else (fun _ => none)) ∧
      (∀ i, d.workTapePos (ι i) = if i.val = 0 then (p : ℤ) - 1 else 0) ∧
      (d.workTapes cap = FinTM.bufferTape (f α) ∧ d.workTapePos cap = (f α).length) ∧
      (∀ j, j ∉ Set.range ι → j ≠ cap →
        d.workTapes j = (fun _ => none) ∧ d.workTapePos j = 0) ∧
      (∀ u < 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
      R.spaceUsed (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) ≤
        n * (3 * α.length + 4 + t + 1) := by
  dsimp only
  obtain ⟨t, hout, hblank, hheads, hret⟩ := ss_capturedPrefix_run F f τ hF ι cap hcap α
  refine ⟨t, ((ss_cleanCanonizer F).tm.runFrom
    ((ss_cleanCanonizer F).tm.initCfg α) t).inputPos.val, ?_, fun w => ?_⟩
  · have h := ((ss_cleanCanonizer F).tm.runFrom
      ((ss_cleanCanonizer F).tm.initCfg α) t).inputPos.isLt
    omega
  · obtain ⟨hr, hcut, hsilent, hspace⟩ := hret w
    have hf := ss_prefix_return_fields (ss_cleanCanonizer F) α w t hblank hheads
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcut, hsilent, hspace⟩
    · rw [hr]
    · rw [hr]
      rw [embedSilentCfg_inputPos]
      exact hf.1
    · intro i
      rw [hr]
      rw [embedSilentCfg_selected_tape]
      exact hf.2.2.1 i
    · intro i
      rw [hr]
      rw [embedSilentCfg_selected_pos]
      exact hf.2.2.2 i
    · rw [hr]
      have hc := embedSilentCfg_cap ι cap hcap (fun _ _ => none) (fun _ => 0)
        [] [] ((FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).tm.runFrom
          ((FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).tm.initCfg
            (pairEncode α w)) (3 * α.length + 4 + t))
      simpa only [List.nil_append, hf.2.1, hout] using hc
    · intro j hj hjc
      rw [hr]
      exact embedSilentCfg_unselected ι cap (fun _ _ => none) (fun _ => 0) [] [] _ j hj hjc

/-- The public seam-layout machine redistributes a canonical serialization from its right
blank, at one time chosen before the input and the ambient configuration.

**Proof sketch.** Instantiate the layout contract with the state-count bits, unary initial
state, and transition table. The published serialization and unary-word equations identify
its source word and its two output words. -/
private theorem ss_serialized_layout (n : ℕ) (src tbl sm : Fin n)
    (hst : src ≠ tbl) (hss : src ≠ sm) (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM n Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {k m : ℕ} (M : MultiTapeTM k Bool (Fin (m + 1))),
        ∃ T ≤ C * ((serializeK M).length + 1),
          ∀ {z : List Bool} (d : Cfg n Bool Q z),
            d.state = some entry →
            d.workTapes src = FinTM.bufferTape (serializeK M) →
            d.workTapePos src = (serializeK M).length →
            d.workTapes tbl = (fun _ => none) → d.workTapePos tbl = 0 →
            d.workTapes sm = (fun _ => none) → d.workTapePos sm = 0 →
            (L.runFrom d T).state = some done ∧
            (L.runFrom d T).inputPos = d.inputPos ∧
            (L.runFrom d T).workTapes =
              Function.update (Function.update (Function.update d.workTapes src
                (fun _ => none)) tbl (FinTM.bufferTape (tableBitsK M.tr)))
                sm (fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)) ∧
            (L.runFrom d T).workTapePos =
              Function.update (Function.update (Function.update d.workTapePos src 0) tbl 0)
                sm 0 ∧
            (∀ u ≤ T, (L.runFrom d u).output = d.output) ∧
            ∀ u < T, (L.runFrom d u).state ≠ some done := by
  obtain ⟨Q, hQ, hD, L, entry, done, C, hL⟩ := exists_seamLayoutTM n src tbl sm hst hss hts
  refine ⟨Q, hQ, hD, L, entry, done, C, ?_⟩
  intro k m M
  have hw := serializeK_eq M
  rw [unaryFin_eq] at hw
  have h := hL m.bits (tableBitsK M.tr) M.q₀.val (serializeK M).length (by rw [← hw])
  rw [← hw] at h
  simpa only [← unaryFin_eq M.q₀] using h

/-- A one-step move of the tested head when its cell is blank. The catalog rows do not
supply this conditional single step; it joins two skips and restores an empty buffer's head.
The action itself is the public one-tape action. -/
private def ss_bufferLeaf (n : ℕ) (i : Fin n) (emptyMove : SignType) :
    MultiTapeTM n Bool Bool where
  q₀ := false
  tr := fun _ _ work =>
    tapeAction i 0 none (if work i = none then emptyMove else 0)
      true

/-- The buffer leaf performs its conditional move in one silent step, with every other
tape and head fixed; its exit is absent before that step.

**Proof sketch.** Apply the public one-step tape-action equation. Before time one there is
only the entry configuration, whose false state is distinct from the true exit. -/
private theorem ss_bufferLeaf_run {n : ℕ} (i : Fin n) (emptyMove : SignType)
    {z : List Bool} (d : Cfg n Bool Bool z) (hstate : d.state = some false) :
    (ss_bufferLeaf n i emptyMove).runFrom d 1 =
      { d with
        state := some true
        workTapePos := Function.update d.workTapePos i
          (d.workTapePos i + if d.workTapeSymbols i = none then (emptyMove : ℤ) else 0) } ∧
      ∀ u < 1, ((ss_bufferLeaf n i emptyMove).runFrom d u).state ≠ some true := by
  constructor
  · rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    have h := step_of_tapeAction_move (ss_bufferLeaf n i emptyMove) d i 0
      (if d.workTapeSymbols i = none then emptyMove else 0) hstate rfl
    simpa only [moveInputPos_zero, apply_ite, SignType.coe_zero] using h
  · intro u hu
    have hu0 : u = 0 := by omega
    rw [hu0, MultiTapeTM.runFrom_zero, hstate]
    simp only [ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- The first rightward skip starts at the source's virtual input position minus one.
At the left blank it moves to zero; at a nonnegative position it skips the remaining suffix.

**Proof sketch.** For virtual position zero, use the empty-word instance of the catalog
skip at the left blank. Otherwise, use the dropped suffix and the public buffer equation.
The catalog supplies both the framed endpoint and the first-return cut. -/
private theorem ss_bufferSkip_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    (skipTM n i).runFrom d (v.length + 1) =
      { d with
        state := some .done
        workTapePos := Function.update d.workTapePos i
          (if p = 0 then 0 else (α.length : ℤ) + 1) } ∧
      ∀ u < v.length + 1, ((skipTM n i).runFrom d u).state ≠ some .done := by
  dsimp only
  have hw : ∀ q : ℤ, 0 ≤ q → q ≤
      ((if p = 0 then [] else α.drop (p - 1)).length : ℤ) →
      d.workTapes i (d.workTapePos i + q) =
        FinTM.bufferTape (if p = 0 then [] else α.drop (p - 1)) q := by
    intro q hq hqv
    rw [hbuf, hpos]
    by_cases h : p = 0
    · subst p
      simp only [ite_true, List.length_nil, Nat.cast_zero] at hqv ⊢
      have hq0 : q = 0 := by omega
      rw [hq0]
      simp only [Int.zero_sub, add_zero, FinTM.bufferTape_left, FinTM.bufferTape_nil]
    · simp only [if_neg h] at hqv ⊢
      rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos hq,
        if_pos (by omega), List.getElem?_drop]
      congr 1
      omega
  obtain ⟨hr, hc, _⟩ := skipTM_run_ofCfg i _ d hstate hw
  have he : d.workTapePos i +
      ((if p = 0 then [] else α.drop (p - 1)).length : ℤ) + 1 =
      if p = 0 then 0 else (α.length : ℤ) + 1 := by
    rw [hpos]
    by_cases h : p = 0
    · subst p
      simp only [ite_true, List.length_nil, Nat.cast_zero]
      omega
    · simp only [if_neg h, List.length_drop]
      omega
  rw [he] at hr
  exact ⟨hr, hc⟩

/-- The second part of the rightward positioning pass: step left at a blank, then skip.
It is the existing seam constructor applied to the one-step leaf and the catalog skip. -/
private def ss_bufferAdvance (n : ℕ) (i : Fin n) :
    MultiTapeTM n Bool (Bool ⊕ SeekPhase) :=
  seamCompTM (ss_bufferLeaf n i .neg) true (skipTM n i) .run

/-- After the first skip, the conditional left step and second skip reach one beyond the
right delimiter of a nonempty word. For the empty word they preserve the virtual position.

**Proof sketch.** Read blankness through the configuration and buffer equations. At position
zero of a nonempty word the leaf stays put and the skip crosses the word; otherwise the leaf
steps left and the empty-word skip steps right again. The public seam theorem supplies the
joined run and its first-return cut, preserving every ambient field. -/
private theorem ss_bufferAdvance_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool Bool z)
    (hstate : d.state = some false) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if p = 0 then 0 else (α.length : ℤ) + 1) :
    let v := if p = 0 then α else []
    (ss_bufferAdvance n i).runFrom (d.mapState Sum.inl) (v.length + 3) =
      ⟨some (Sum.inr .done), d.inputPos, d.workTapes,
        Function.update d.workTapePos i
          (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩ ∧
      ∀ u < v.length + 3,
        ((ss_bufferAdvance n i).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr .done) := by
  dsimp only
  let a : Cfg n Bool Bool z :=
    { d with
      state := some true
      workTapePos := Function.update d.workTapePos i
        (d.workTapePos i + if d.workTapeSymbols i = none then (-1 : ℤ) else 0) }
  obtain ⟨hr, hc⟩ := ss_bufferLeaf_run i .neg d hstate
  change (ss_bufferLeaf n i .neg).runFrom d 1 = a at hr
  let b := a.mapState (fun _ => SeekPhase.run)
  have hba : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  have hbp : b.workTapePos i =
      if p = 0 then (if α = [] then -1 else 0) else (α.length : ℤ) := by
    rw [Cfg.mapState_workTapePos]
    dsimp only [a]
    rw [Function.update_self, Cfg.workTapeSymbols_eq, hbuf, hpos]
    by_cases h : p = 0
    · simp only [if_pos h]
      cases α with
      | nil => simp only [FinTM.bufferTape_nil, ite_true]; omega
      | cons x xs =>
        rw [show (0 : ℤ) = (0 : ℕ) by rfl, FinTM.bufferTape_nat]
        simp only [List.getElem?_cons_zero, reduceCtorEq, if_false, List.cons_ne_nil,
          Nat.cast_zero, add_zero]
    · rw [if_neg h]
      have hn : FinTM.bufferTape α ((α.length : ℤ) + 1) = none := by
        rw [show (α.length : ℤ) + 1 = ((α.length + 1 : ℕ) : ℤ) by omega,
          FinTM.bufferTape_nat, List.getElem?_eq_none_iff]
        omega
      rw [hn, if_pos rfl]
      omega
  have hw : ∀ q : ℤ, 0 ≤ q →
      q ≤ ((if p = 0 then α else []).length : ℤ) →
      b.workTapes i (b.workTapePos i + q) =
        FinTM.bufferTape (if p = 0 then α else []) q := by
    intro q hq hqv
    rw [hba, hbp]
    by_cases h : p = 0
    · simp only [if_pos h] at hqv ⊢
      by_cases ha : α = []
      · subst α
        simp only [FinTM.bufferTape_nil]
      · rw [if_neg ha, zero_add]
    · simp only [if_neg h, List.length_nil, Nat.cast_zero] at hqv ⊢
      have hq0 : q = 0 := by omega
      rw [hq0, add_zero, FinTM.bufferTape_nat, List.getElem?_eq_none (by omega),
        FinTM.bufferTape_nil]
  have hbstate : b.state = some .run := by
    rw [Cfg.mapState_state]
    rfl
  obtain ⟨hs, hscut, _⟩ := skipTM_run_ofCfg i _ b hbstate hw
  have he : b.workTapePos i + ((if p = 0 then α else []).length : ℤ) + 1 =
      if α = [] then (p : ℤ) else (α.length : ℤ) + 1 := by
    rw [hbp]
    by_cases h : p = 0
    · simp only [if_pos h]
      by_cases ha : α = []
      · subst α
        simp only [ite_true, List.length_nil, Nat.cast_zero]
        omega
      · simp only [if_neg ha]
        omega
    · simp only [if_neg h, List.length_nil, Nat.cast_zero]
      by_cases ha : α = []
      · subst α
        simp only [ite_true, List.length_nil, Nat.cast_zero] at hp ⊢
        omega
      · simp only [if_neg ha, add_zero]
  have hrun := seamCompTM_run_ofCfg (ss_bufferLeaf n i .neg) true (skipTM n i)
    .run hr rfl hc hs
  have hcut := seamCompTM_firstReturn_ofCfg (ss_bufferLeaf n i .neg) true (skipTM n i)
    .run .done hr rfl hc hs rfl hscut
  have ht : 1 + 1 + ((if p = 0 then α else []).length + 1) =
      (if p = 0 then α else []).length + 3 := by omega
  rw [ht] at hrun hcut
  refine ⟨hrun.trans ?_, hcut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, he]
    change Function.update b.workTapePos i _ j = _
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Position the code buffer for the backward catalog row, using three existing phases. -/
private def ss_bufferSeek (n : ℕ) (i : Fin n) :
    MultiTapeTM n Bool (SeekPhase ⊕ (Bool ⊕ SeekPhase)) :=
  seamCompTM (skipTM n i) .done (ss_bufferAdvance n i) (Sum.inl false)

/-- The two skips and their intervening conditional step find the right edge, with a time
that depends only on the code and its chosen virtual position.

**Proof sketch.** The first catalog skip has the dropped-suffix time. The proved advance
then has the whole-word or empty-word time. Compose their framed contracts by the general
seam equations and read the final head update through the state-map field equations. -/
private theorem ss_bufferSeek_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    let w := if p = 0 then α else []
    (ss_bufferSeek n i).runFrom (d.mapState Sum.inl) (v.length + w.length + 5) =
      ⟨some (Sum.inr (Sum.inr .done)), d.inputPos, d.workTapes,
        Function.update d.workTapePos i
          (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩ ∧
      ∀ u < v.length + w.length + 5,
        ((ss_bufferSeek n i).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr (Sum.inr .done)) := by
  dsimp only
  obtain ⟨hr, hc⟩ := ss_bufferSkip_run i α p hp d hstate hbuf hpos
  let a : Cfg n Bool SeekPhase z :=
    { d with
      state := some .done
      workTapePos := Function.update d.workTapePos i
        (if p = 0 then 0 else (α.length : ℤ) + 1) }
  let b := a.mapState (fun _ => false)
  have hbstate : b.state = some false := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if p = 0 then 0 else (α.length : ℤ) + 1 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferAdvance_run i α p hp b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : Bool → Bool ⊕ SeekPhase) =
      a.mapState (fun _ => Sum.inl false) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (skipTM n i) .done (ss_bufferAdvance n i)
    (Sum.inl false) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (skipTM n i) .done (ss_bufferAdvance n i)
    (Sum.inl false) (Sum.inr .done) hr rfl hc ha rfl hacut
  have ht : (if p = 0 then [] else α.drop (p - 1)).length + 1 + 1 +
      ((if p = 0 then α else []).length + 3) =
      (if p = 0 then [] else α.drop (p - 1)).length +
        (if p = 0 then α else []).length + 5 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- The backward catalog row restores the first cell of a nonempty buffer and the
original position of an empty buffer, preserving the full surrounding configuration.

**Proof sketch.** For a nonempty word the forward endpoint is one beyond its right blank,
so the catalog precondition is the buffer itself. For an empty word all cells are blank.
The resulting head formula is the catalog's subtraction of the word length and one. -/
private theorem ss_bufferBack_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    {z : List Bool} (d : Cfg n Bool SeekPhase z) (hstate : d.state = some .run)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1) :
    (skipBackTM n i).runFrom d (α.length + 3) =
      { d with
        state := some .done
        workTapePos := Function.update d.workTapePos i
          (if α = [] then (p : ℤ) - 1 else 0) } ∧
      ∀ u < α.length + 3, ((skipBackTM n i).runFrom d u).state ≠ some .done := by
  have he : d.workTapePos i - (α.length : ℤ) - 1 =
      if α = [] then (p : ℤ) - 1 else 0 := by
    rw [hpos]
    by_cases ha : α = []
    · subst α
      simp only [ite_true, List.length_nil, Nat.cast_zero, sub_zero]
    · simp only [if_neg ha]
      omega
  obtain ⟨hr, hc, _⟩ := skipBackTM_run_ofCfg i α d hstate (by
    intro q _ _
    rw [hbuf, he]
    by_cases ha : α = []
    · subst α
      simp only [FinTM.bufferTape_nil]
    · rw [if_neg ha, zero_add])
  rw [he] at hr
  exact ⟨hr, hc⟩

/-- Restore the empty word's origin if necessary, then clear through the catalog row.
The parameter is the virtual position chosen for the empty code, fixed for the machine. -/
private def ss_bufferClear (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool (Bool ⊕ SweepPhase) :=
  seamCompTM (ss_bufferLeaf n i (if emptyPos = 0 then .pos else 0)) true
    (clearTM n i) .sweep

/-- The final buffer phases erase the code and put its head at zero. The empty code uses
its one fixed virtual position, so the machine does not depend on the input suffix.

**Proof sketch.** A nonempty buffer has a symbol at zero, so the leaf does not move. On an
empty buffer, the fixed position is zero or one and the conditional step restores zero.
The catalog clear then erases the word interval; outside that interval the public buffer
formula is already blank. Compose by the framed seam and its first-return theorem. -/
private theorem ss_bufferClear_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : α = [] → p = emptyPos)
    {z : List Bool} (d : Cfg n Bool Bool z) (hstate : d.state = some false)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) - 1 else 0) :
    (ss_bufferClear n i emptyPos).runFrom (d.mapState Sum.inl) (2 * α.length + 4) =
      ⟨some (Sum.inr .done), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < 2 * α.length + 4,
        ((ss_bufferClear n i emptyPos).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr .done) := by
  let mv : SignType := if emptyPos = 0 then .pos else 0
  let a : Cfg n Bool Bool z :=
    { d with
      state := some true
      workTapePos := Function.update d.workTapePos i
        (d.workTapePos i + if d.workTapeSymbols i = none then (mv : ℤ) else 0) }
  obtain ⟨hr, hc⟩ := ss_bufferLeaf_run i mv d hstate
  change (ss_bufferLeaf n i mv).runFrom d 1 = a at hr
  have haheads : a.workTapePos = Function.update d.workTapePos i 0 := by
    have hm : d.workTapePos i +
        (if d.workTapeSymbols i = none then (mv : ℤ) else 0) = 0 := by
      rw [Cfg.workTapeSymbols_eq, hbuf, hpos]
      by_cases ha : α = []
      · rw [if_pos ha, hp ha]
        subst α
        simp only [FinTM.bufferTape_nil, ite_true]
        by_cases h : emptyPos = 0
        · simp only [mv, if_pos h, SignType.pos_eq_one, SignType.coe_one, h, Nat.cast_zero]
          omega
        · have h1 : emptyPos = 1 := by omega
          simp only [mv, if_neg h, SignType.coe_zero, h1, Nat.cast_one]
          omega
      · rw [if_neg ha]
        cases α with
        | nil => exact False.elim (ha rfl)
        | cons x xs =>
          rw [show (0 : ℤ) = (0 : ℕ) by rfl, FinTM.bufferTape_nat]
          simp only [List.getElem?_cons_zero, reduceCtorEq, if_false, Nat.cast_zero,
            add_zero]
    dsimp only [a]
    rw [hm]
  let b := a.mapState (fun _ => SweepPhase.sweep)
  have hbstate : b.state = some .sweep := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = 0 := by
    rw [Cfg.mapState_workTapePos, haheads, Function.update_self]
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨hs, hscut, _⟩ := clearTM_run_ofCfg i α b hbstate (by
    intro q _ _
    rw [hbbuf, hbpos, zero_add])
  have hrun := seamCompTM_run_ofCfg (ss_bufferLeaf n i mv) true (clearTM n i)
    .sweep hr rfl hc hs
  have hcut := seamCompTM_firstReturn_ofCfg (ss_bufferLeaf n i mv) true (clearTM n i)
    .sweep .done hr rfl hc hs rfl hscut
  have ht : 1 + 1 + (2 * α.length + 2) = 2 * α.length + 4 := by omega
  rw [ht] at hrun hcut
  refine ⟨hrun.trans ?_, hcut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    by_cases hj : j = i
    · subst j
      simp only [hbpos, zero_add, Function.update_self, true_and]
      by_cases hq : 0 ≤ q ∧ q < (α.length : ℤ)
      · rw [if_pos hq]
      · rw [if_neg hq, hbbuf, FinTM.bufferTape_eq]
        by_cases hq0 : 0 ≤ q
        · rw [if_pos hq0, List.getElem?_eq_none (by omega)]
        · rw [if_neg hq0]
    · simp only [hj, false_and, if_false, Function.update_of_ne hj]
      rw [Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, haheads]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Backward positioning followed by the fixed-origin clear, joined by the public seam. -/
private def ss_bufferFinish (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
  seamCompTM (skipBackTM n i) .done (ss_bufferClear n i emptyPos) (Sum.inl false)

/-- The backward pass and clear erase a buffer from the forward pass's endpoint.

**Proof sketch.** Apply the backward catalog specialization, then the proved fixed-origin
clear. The public seam transports their first-return cuts. Its state-map equations and
idempotence of a head update identify the framed endpoint. -/
private theorem ss_bufferFinish_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : α = [] → p = emptyPos)
    {z : List Bool} (d : Cfg n Bool SeekPhase z) (hstate : d.state = some .run)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1) :
    (ss_bufferFinish n i emptyPos).runFrom (d.mapState Sum.inl) (3 * α.length + 8) =
      ⟨some (Sum.inr (Sum.inr .done)), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < 3 * α.length + 8,
        ((ss_bufferFinish n i emptyPos).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr (Sum.inr .done)) := by
  obtain ⟨hr, hc⟩ := ss_bufferBack_run i α p d hstate hbuf hpos
  let a : Cfg n Bool SeekPhase z :=
    { d with
      state := some .done
      workTapePos := Function.update d.workTapePos i
        (if α = [] then (p : ℤ) - 1 else 0) }
  let b := a.mapState (fun _ => false)
  have hbstate : b.state = some false := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if α = [] then (p : ℤ) - 1 else 0 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferClear_run i emptyPos he α p hp b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : Bool → Bool ⊕ SweepPhase) =
      a.mapState (fun _ => Sum.inl false) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (skipBackTM n i) .done (ss_bufferClear n i emptyPos)
    (Sum.inl false) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (skipBackTM n i) .done
    (ss_bufferClear n i emptyPos) (Sum.inl false) (Sum.inr .done) hr rfl hc ha rfl hacut
  have ht : α.length + 3 + 1 + (2 * α.length + 4) = 3 * α.length + 8 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    have hbtapes : b.workTapes = d.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hbtapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Clear the captured code buffer from any of its possible virtual input positions.
All positioning and erasure phases are joined by existing seam constructors. -/
private def ss_bufferCleanup (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool
      ((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) :=
  seamCompTM (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run)

/-- The complete code-buffer cleanup is uniform in the suffix and ambient configuration.
Its only fixed parameter is the virtual position assigned to the empty code.

**Proof sketch.** The forward sequence positions the head for the backward pass. The
backward and clear sequence restores zero and erases the buffer. Join the two proved
contracts with the general seam theorem; sum their code-dependent times. The inherited
first-return theorem makes the final right-tagged exit fresh until that time. -/
private theorem ss_bufferCleanup_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : p ≤ α.length + 1)
    (hpe : α = [] → p = emptyPos) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    let w := if p = 0 then α else []
    let T := v.length + w.length + 3 * α.length + 14
    (ss_bufferCleanup n i emptyPos).runFrom
      ((d.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
        Sum.inl) T =
      ⟨some (Sum.inr (Sum.inr (Sum.inr .done))), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < T, ((ss_bufferCleanup n i emptyPos).runFrom
        ((d.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
          Sum.inl) u).state ≠ some (Sum.inr (Sum.inr (Sum.inr .done))) := by
  dsimp only
  obtain ⟨hr, hc⟩ := ss_bufferSeek_run i α p hp d hstate hbuf hpos
  let a : Cfg n Bool (SeekPhase ⊕ (Bool ⊕ SeekPhase)) z :=
    ⟨some (Sum.inr (Sum.inr .done)), d.inputPos, d.workTapes,
      Function.update d.workTapePos i
        (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩
  let b := a.mapState (fun _ => SeekPhase.run)
  have hbstate : b.state = some .run := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferFinish_run i emptyPos he α p hpe b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SweepPhase)) =
      a.mapState (fun _ => Sum.inl .run) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run) (Sum.inr (Sum.inr .done))
    hr rfl hc ha rfl hacut
  have ht : (if p = 0 then [] else α.drop (p - 1)).length +
      (if p = 0 then α else []).length + 5 + 1 + (3 * α.length + 8) =
      (if p = 0 then [] else α.drop (p - 1)).length +
        (if p = 0 then α else []).length + 3 * α.length + 14 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    have hbtapes : b.workTapes = d.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hbtapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- The native rewind has a separate pre-exit anchor so that the final exit is fresh. -/
private inductive ss_RewindState where
  | enter | scan | stop | done
  deriving DecidableEq, Fintype

/-- A native input-only leaf; its scan is handled by the published rewind contracts. -/
private def ss_inputRewind (n : ℕ) : MultiTapeTM n Bool ss_RewindState where
  q₀ := .enter
  tr := fun q inp _ => match q with
    | .enter => FinTM.controlAction .neg (some .scan)
    | .scan => match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos (some .stop)
    | .stop => FinTM.controlAction 0 (some .done)
    | .done => FinTM.controlAction 0 (some .done)

/-- The final rewind anchor is stationary for every further time.

**Proof sketch.** Its own transition is a zero control action. Induction through the public
successor equation preserves the configuration; the control-action equation fixes its fields. -/
private theorem ss_inputRewind_done {n : ℕ} {z : List Bool}
    (d : Cfg n Bool ss_RewindState z) (hd : d.state = some .done) (t : ℕ) :
    (ss_inputRewind n).runFrom d t = d := by
  have hs : (ss_inputRewind n).step d = d := by
    rw [MultiTapeTM.step_of_some hd]
    change (FinTM.controlAction 0 (some ss_RewindState.done)).apply d = d
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    apply Cfg.ext
    · exact hd.symm
    · rfl
    · rfl
    · rfl
    · rfl
  induction t with
  | zero => exact MultiTapeTM.runFrom_zero
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih, hs]

/-- The native input rewind returns at an exact position-dependent time, with a first exit
and fixed work heads throughout. Its time is independent of the input's suffix.

**Proof sketch.** One left step puts the input head within the word. The public scan equation
then reaches the pre-exit anchor after exactly the old position plus one steps. An earlier
final exit would be stationary and contradict that anchor. The public rewind-head theorem
has the same pre-exit time, since leaving that anchor enters the stationary final exit.
One final stationary step completes the run. -/
private theorem ss_inputRewind_run {n : ℕ} {z : List Bool}
    (d : Cfg n Bool ss_RewindState z) (hd : d.state = some .enter)
    (hp : 0 < d.inputPos.val) :
    (ss_inputRewind n).runFrom d (d.inputPos.val + 2) =
      { d with state := some .done, inputPos := 1 } ∧
      (∀ u < d.inputPos.val + 2,
        ((ss_inputRewind n).runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ d.inputPos.val + 2,
        ((ss_inputRewind n).runFrom d u).workTapePos = d.workTapePos := by
  let M := ss_inputRewind n
  let c : Cfg n Bool ss_RewindState z :=
    { d with state := some .scan, inputPos := moveInputPos d.inputPos .neg }
  have hstep : M.step d = c := by
    rw [MultiTapeTM.step_of_some hd]
    change (FinTM.controlAction .neg (some ss_RewindState.scan)).apply d = c
    rw [FinTM.controlAction_apply]
  have hcp : c.inputPos.val ≤ z.length := by
    dsimp only [c]
    rw [FinTM.moveInputPos_neg_val]
    have := d.inputPos.isLt
    omega
  have hscan := FinTM.rewind_scan M .scan (some .stop)
    (fun inp _ => by cases inp <;> rfl) c rfl hcp
  have ht : 1 + (c.inputPos.val + 1) = d.inputPos.val + 1 := by
    dsimp only [c]
    rw [FinTM.moveInputPos_neg_val]
    omega
  have hstop : M.runFrom d (d.inputPos.val + 1) =
      { d with state := some .stop, inputPos := 1 } := by
    rw [← ht, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step' (cfg := d) (t := 0),
      MultiTapeTM.runFrom_zero, hstep, hscan]
  have hlast : ∀ (a : Cfg n Bool ss_RewindState z), a.state = some .stop →
      M.step a = { a with state := some .done } := by
    intro a ha
    rw [MultiTapeTM.step_of_some ha]
    change (FinTM.controlAction 0 (some ss_RewindState.done)).apply a = _
    rw [FinTM.controlAction_apply, moveInputPos_zero]
  have hcut : ∀ u ≤ d.inputPos.val + 1, (M.runFrom d u).state ≠ some .done := by
    intro u hu hdone
    have hf := ss_inputRewind_done (M.runFrom d u) hdone (d.inputPos.val + 1 - u)
    have hsum : u + (d.inputPos.val + 1 - u) = d.inputPos.val + 1 := by omega
    rw [← MultiTapeTM.runFrom_add, hsum, hstop] at hf
    have heq := congrArg Cfg.state hf
    rw [hdone] at heq
    cases heq
  have hret : M.runFrom d (d.inputPos.val + 2) =
      { d with state := some .done, inputPos := 1 } := by
    rw [show d.inputPos.val + 2 = (d.inputPos.val + 1) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', hstop, hlast _ rfl]
  obtain ⟨r, hr, hrun, hheads⟩ := FinTM.rewind_heads M .enter .scan (some .stop)
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) d hd
  have htime : r = d.inputPos.val + 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx : (M.runFrom d (r + 1)).state = some .done := by
        rw [MultiTapeTM.runFrom_succ_eq_step', hrun, hlast _ rfl]
      exact hcut (r + 1) (by omega) hx
    · have hf := ss_inputRewind_done
        ({ d with state := some .done, inputPos := 1 } : Cfg n Bool ss_RewindState z)
        rfl (r - (d.inputPos.val + 2))
      have hsum : d.inputPos.val + 2 + (r - (d.inputPos.val + 2)) = r := by omega
      rw [← hret, ← MultiTapeTM.runFrom_add, hsum, hrun, hret] at hf
      have heq := congrArg Cfg.state hf
      cases heq
  refine ⟨hret, fun u hu => hcut u (by omega), ?_⟩
  intro u hu
  by_cases h : u ≤ d.inputPos.val + 1
  · exact hheads u (by omega)
  · have heq : u = d.inputPos.val + 2 := by omega
    rw [heq, hret]

/-- A live configuration's state map preserves its physical frame, read through the public
field equations rather than through the definition of state renaming.

**Proof sketch.** Configuration extensionality reduces to the five published field equations;
the live-state equation reduces the option map to one constructor. -/
private theorem ss_live_map {n : ℕ} {P Q : Type} {z : List Bool}
    (d : Cfg n Bool P z) (q : P) (hq : d.state = some q) (f : P → Q) :
    d.mapState f = ⟨some (f q), d.inputPos, d.workTapes, d.workTapePos, d.output⟩ := by
  apply Cfg.ext
  · rw [Cfg.mapState_state, hq, Option.map_some]
  · exact Cfg.mapState_inputPos _ _
  · funext i p
    exact Cfg.mapState_workTapes _ _ _ _
  · funext i
    exact Cfg.mapState_workTapePos _ _ _
  · exact Cfg.mapState_output _ _

/-- Selected code and capture cells give a two-update normal form for any field.

**Proof sketch.** At the capture index use its equation. In the selected block, injectivity
identifies index zero; every other selected field has the background value. Outside both
blocks use the framing equation. This single argument applies to tapes and head positions. -/
private theorem ss_block_updates {A : Type} {m n : ℕ} (ι : Fin m ↪ Fin n)
    (cap : Fin n) (zero : Fin m) (hz : zero.val = 0)
    (f : Fin n → A) (base code captured : A)
    (hsel : ∀ j, f (ι j) = if j.val = 0 then code else base)
    (hc : f cap = captured)
    (ho : ∀ j, j ∉ Set.range ι → j ≠ cap → f j = base) :
    f = Function.update (Function.update (fun _ => base) (ι zero) code) cap captured := by
  funext j
  by_cases hj : j = cap
  · subst j
    rw [hc, Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hs : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hs
      rw [hsel]
      by_cases hi : i = zero
      · subst i
        rw [hz, if_pos rfl, Function.update_self]
      · have hival : i.val ≠ 0 := by
          intro h
          exact hi (Fin.ext (h.trans hz.symm))
        have hislot : ι i ≠ ι zero := fun h => hi (ι.injective h)
        rw [if_neg hival, Function.update_of_ne hislot]
    · have hjz : j ≠ ι zero := by
        intro h
        exact hs ⟨zero, h.symm⟩
      rw [ho j hs hj, Function.update_of_ne hjz]

/-- The source block sits after the simulated tapes, table, and summary. -/
private def ss_sourceSlot (m k : ℕ) : Fin m ↪ Fin ((m + 1) + (k + 2)) where
  toFun i := ⟨k + 2 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change k + 2 + i.val = k + 2 + j.val at hv
    omega

/-- The capture tape is last, beyond the source block. -/
private def ss_captureTape (m k : ℕ) : Fin ((m + 1) + (k + 2)) :=
  ⟨k + 2 + m, by omega⟩

/-- The capture tape is separate, and all first `k + 2` tapes lie outside both blocks.

**Proof sketch.** Every selected index lies between `k + 2` and `k + 2 + m - 1`.
The capture index is `k + 2 + m`, and each reserved index is smaller than `k + 2`. -/
private theorem ss_capture_indices (m k : ℕ) :
    ss_captureTape m k ∉ Set.range (ss_sourceSlot m k) ∧
    ∀ j : Fin ((m + 1) + (k + 2)), j.val < k + 2 →
      j ∉ Set.range (ss_sourceSlot m k) ∧ j ≠ ss_captureTape m k := by
  have hs (i : Fin m) : k + 2 ≤ (ss_sourceSlot m k i).val ∧
      (ss_sourceSlot m k i).val < (ss_captureTape m k).val := by
    change k + 2 ≤ k + 2 + i.val ∧ k + 2 + i.val < k + 2 + m
    omega
  constructor
  · rintro ⟨i, hi⟩
    have := (hs i).2
    rw [hi] at this
    exact (lt_irrefl _ this)
  · intro j hj
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      have := (hs i).1
      rw [hi] at this
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = k + 2 + m at hv
      omega

/-- **U2-S, the `k`-generic startup** (the startup of `Turing.exists_selfStartupTM`, generic in
the work-tape count). For a `k`-tape scheme `E` there is a binary machine with `K + (k + 2)` work
tapes and an exit state such that for every code `α` there are a time `T` and a space bound `B`,
**depending on `α` only**, with the following property on every input `pairEncode α w`. At time
`T`, and not earlier, it is at its exit with:
* the input head at position `1`, `Cfg.init`'s position, and the output empty, having emitted
  nothing before;
* tapes `0, …, k - 1`, the simulated work tapes, blank, and tape `k` holding the canonical table
  `Turing.tableBitsK` of the decoded machine;
* tape `k + 1` holding the decoded machine's initial state in unary from cell `2` (cells `0`
  and `1` blank), the step block's summary tape for an empty output;
* every other tape blank and every head at `0`.

Up to `T` it has visited at most `B` cells. This configuration is the step block's seam
(`Turing.StepBlock.Rep`) for the decoded machine's initial configuration on the same input, and
its restriction to the first `k + 2` tapes is H2-F's encoding `Turing.StepBlock.forwardLoopCfg` of
that configuration. [AB09, §1.4.1, Theorem 1.9]

**Proof sketch.** As `Turing.exists_selfStartupTM`'s, at `k` mirrored tapes. Extract and
canonize: the prefix parser composed with the scheme's canonizer by buffered composition, its
emissions captured on a scratch tape (the pattern of `Turing.universalCanonTM` and
`Turing.universalCaptureTM`, with `E.canonizer` in place of the one-tape scheme's); it ends after
`3|α| + 4 + E.canonizerTime |α|` steps with `serializeK (E.machine α)` captured and the input
head at `2|α| + 3`. Skip the doubled state count and the separator of
`serializeK = pairEncode n.bits (unaryFin q₀ ++ tableBitsK tr)`, copy the unary initial state to
tape `k + 1` at offset `2` and the table to tape `k`; clear the scratch and the buffer. Rewind the
input head to position `1` (`Turing.FinTM.timed_rewind`, `2|α| + 5` steps). Every phase depends
on `α` only, so `T` and `B` do (`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's
halting time bounds its cells).

**Implementation.** The scheme's canonizer runs behind the public cleaner, which blanks its work
tapes and returns its heads, and the capture uses that machine's first halting time `t α`
(`Turing.MultiTapeTM.exists_first_halt`): the capture ends after `3|α| + 4 + t α` steps rather
than at the bound `E.canonizerTime |α|`. The code buffer is cleared by the catalog skip, skip back
and clear around a one-step move that acts only on a blank cell; on the empty code the buffer is
all blank, so the canonizer's final head position on the empty code is a fixed parameter of the
machine, chosen from `E`. The input head is rewound by `Turing.FinTM.rewind_scan` and
`Turing.FinTM.rewind_heads`, in `2|α| + 5` steps. -/
theorem exists_selfStartupTMK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P),
      ∀ α : List Bool, ∃ T B : ℕ, ∀ w : List Bool,
        R.runFrom (R.initCfg (pairEncode α w)) T =
          ⟨some exit, 1,
            fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
              else if j.val = k + 1 then
                fun p => FinTM.bufferTape (unaryFin (E.machine α).q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit) ∧
        (∀ u ≤ T, (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  classical
  let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer E.canonizer)
  let n := (G.k + 1) + (k + 2)
  let ι := ss_sourceSlot G.k k
  let cap := ss_captureTape G.k k
  have hcap : cap ∉ Set.range ι := (ss_capture_indices G.k k).1
  have hm : 0 < G.k := by
    dsimp only [G]
    rw [FinTM.bufferedCompTM_k, universalPrefixTM_k]
    omega
  let zero : Fin G.k := ⟨0, hm⟩
  let code := ι zero
  let tbl : Fin n := ⟨k, by dsimp only [n]; omega⟩
  let sm : Fin n := ⟨k + 1, by dsimp only [n]; omega⟩
  have htbl := (ss_capture_indices G.k k).2 tbl (by dsimp only [tbl]; omega)
  have hsm := (ss_capture_indices G.k k).2 sm (by dsimp only [sm]; omega)
  have hts : tbl ≠ sm := by
    intro h
    have hv := congrArg Fin.val h
    dsimp only [tbl, sm] at hv
    omega
  have hct : code ≠ tbl := fun h => htbl.1 ⟨zero, h⟩
  have hcs : code ≠ sm := fun h => hsm.1 ⟨zero, h⟩
  have hcc : code ≠ cap := fun h => hcap ⟨zero, h⟩
  let A := ss_captureTM G ι cap
  have hcapture := fun α => ss_capturedPrefix_fields E.canonizer
    (fun β => serializeK (E.machine β)) E.canonizerTime E.canonizer_computes ι cap hcap α
  dsimp only at hcapture
  choose t p hp hc using hcapture
  have hp0 : p [] ≤ 1 := by simpa only [List.length_nil, zero_add] using hp []
  obtain ⟨Q, hQ, hD, L, entry, done, C, hL⟩ :=
    ss_serialized_layout n cap tbl sm htbl.2.symm hsm.2.symm hts
  letI := hQ
  letI := hD
  let J := ss_bufferCleanup n code (p [])
  let jentry : (SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
    Sum.inl (Sum.inl .run)
  let jexit : (SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
    Sum.inr (Sum.inr (Sum.inr .done))
  let B := seamCompTM J jexit (ss_inputRewind n) .enter
  let D := seamCompTM L done B (Sum.inl jentry)
  let W := seamCompTM A (Sum.inr ()) D (Sum.inl entry)
  let R := { W with q₀ := Sum.inl A.q₀ }
  let exit : (G.State ⊕ Unit) ⊕ Q ⊕
      (((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) ⊕
        ss_RewindState) := Sum.inr (Sum.inr (Sum.inr .done))
  refine ⟨G.k + 1, _, inferInstance, inferInstance, R, exit, ?_⟩
  intro α
  obtain ⟨l, hl, hlayout⟩ := hL (E.machine α)
  let a := 3 * α.length + 4 + t α
  let v := if p α = 0 then [] else α.drop (p α - 1)
  let w₀ := if p α = 0 then α else []
  let b := v.length + w₀.length + 3 * α.length + 14
  let r := 2 * α.length + 5
  let T := a + 1 + (l + 1 + (b + 1 + r))
  refine ⟨T, n * (T + 1), ?_⟩
  intro w
  let d₀ := A.initCfg (pairEncode α w)
  let d₁ := A.runFrom d₀ a
  obtain ⟨hstate, hip, hsel, hheads, hcapt, hother, hcut, hsil, _⟩ := hc α w
  have hs₁ : d₁.state = some (Sum.inr ()) := hstate
  have ht₁ : d₁.workTapes = Function.update
      (Function.update (fun _ => fun _ => none) code (FinTM.bufferTape α))
      cap (FinTM.bufferTape (serializeK (E.machine α))) :=
    ss_block_updates ι cap zero rfl _ _ _ _ hsel hcapt.1
      (fun j hj hjc => (hother j hj hjc).1)
  have hh₁ : d₁.workTapePos = Function.update
      (Function.update (fun _ => 0) code ((p α : ℤ) - 1))
      cap (serializeK (E.machine α)).length :=
    ss_block_updates ι cap zero rfl _ _ _ _ hheads hcapt.2
      (fun j hj hjc => (hother j hj hjc).2)
  have ho₁ : d₁.output = [] := hsil a le_rfl
  let d₂ := d₁.mapState (fun _ => entry)
  have hd₂ : d₂.state = some entry := by
    rw [Cfg.mapState_state, hs₁, Option.map_some]
  have ht₂ (j : Fin n) : d₂.workTapes j = d₁.workTapes j := by
    funext q
    exact Cfg.mapState_workTapes _ _ _ _
  have hh₂ (j : Fin n) : d₂.workTapePos j = d₁.workTapePos j :=
    Cfg.mapState_workTapePos _ _ _
  obtain ⟨hs₃, hi₃, ht₃, hh₃, ho₃, hcut₃⟩ := hlayout d₂ hd₂
    ((ht₂ cap).trans hcapt.1) ((hh₂ cap).trans hcapt.2)
    ((ht₂ tbl).trans (hother tbl htbl.1 htbl.2).1)
    ((hh₂ tbl).trans (hother tbl htbl.1 htbl.2).2)
    ((ht₂ sm).trans (hother sm hsm.1 hsm.2).1)
    ((hh₂ sm).trans (hother sm hsm.1 hsm.2).2)
  let d₃ := L.runFrom d₂ l
  let c : Cfg n Bool SeekPhase (pairEncode α w) :=
    ⟨some .run, d₃.inputPos, d₃.workTapes, d₃.workTapePos, d₃.output⟩
  have hbuf : c.workTapes code = FinTM.bufferTape α := by
    change d₃.workTapes code = _
    rw [ht₃, Function.update_of_ne hcs, Function.update_of_ne hct,
      Function.update_of_ne hcc, ht₂]
    exact (hsel zero).trans (if_pos rfl)
  have hpos : c.workTapePos code = (p α : ℤ) - 1 := by
    change d₃.workTapePos code = _
    rw [hh₃, Function.update_of_ne hcs, Function.update_of_ne hct,
      Function.update_of_ne hcc, hh₂]
    exact (hheads zero).trans (if_pos rfl)
  obtain ⟨hj, hjcut⟩ := ss_bufferCleanup_run code (p []) hp0 α (p α) (hp α)
    (fun h => congrArg p h) c rfl hbuf hpos
  have hjstart :
      ((c.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
        Sum.inl) = d₃.mapState (fun _ => jentry) := by
    rw [ss_live_map c .run rfl,
      ss_live_map _ (Sum.inl .run) rfl, ss_live_map d₃ done hs₃]
  rw [hjstart] at hj hjcut
  let d₄ : Cfg n Bool
      ((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)))
      (pairEncode α w) :=
    ⟨some jexit, d₃.inputPos, Function.update d₃.workTapes code (fun _ => none),
      Function.update d₃.workTapePos code 0, d₃.output⟩
  change J.runFrom (d₃.mapState (fun _ => jentry)) b = d₄ at hj
  change ∀ u < b, (J.runFrom (d₃.mapState (fun _ => jentry)) u).state ≠ some jexit at hjcut
  let d₅ := d₄.mapState (fun _ => ss_RewindState.enter)
  have hd₅ : d₅.state = some .enter := by rw [Cfg.mapState_state]; rfl
  have hi₅ : d₅.inputPos.val = 2 * α.length + 3 := by
    rw [Cfg.mapState_inputPos]
    change d₃.inputPos.val = _
    rw [hi₃, Cfg.mapState_inputPos]
    exact hip
  obtain ⟨hrew, hrewcut, _⟩ := ss_inputRewind_run d₅ hd₅ (by omega)
  have htime : d₅.inputPos.val + 2 = r := by dsimp only [r]; omega
  rw [htime] at hrew hrewcut
  have hb := seamCompTM_run_ofCfg J jexit (ss_inputRewind n) .enter hj rfl hjcut hrew
  have hbcut := seamCompTM_firstReturn_ofCfg J jexit (ss_inputRewind n) .enter .done
    hj rfl hjcut hrew rfl hrewcut
  have hbstart : (d₃.mapState (fun _ => jentry)).mapState
      (Sum.inl : _ → _ ⊕ ss_RewindState) = d₃.mapState (fun _ => Sum.inl jentry) := by
    rw [ss_live_map d₃ done hs₃, ss_live_map _ jentry rfl, ss_live_map d₃ done hs₃]
  rw [hbstart] at hb hbcut
  have hd := seamCompTM_run_ofCfg L done B (Sum.inl jentry) rfl hs₃ hcut₃ hb
  have hdcut := seamCompTM_firstReturn_ofCfg L done B (Sum.inl jentry) (Sum.inr .done)
    rfl hs₃ hcut₃ hb (by rw [Cfg.mapState_state]; rfl) hbcut
  have hdstart : (d₁.mapState (fun _ => entry)).mapState
      (Sum.inl : Q → Q ⊕
        (((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) ⊕
          ss_RewindState)) = d₁.mapState (fun _ => Sum.inl entry) := by
    rw [ss_live_map d₁ (Sum.inr ()) hs₁, ss_live_map _ entry rfl,
      ss_live_map d₁ (Sum.inr ()) hs₁]
  rw [hdstart] at hd hdcut
  have hw := seamCompTM_run_ofCfg A (Sum.inr ()) D (Sum.inl entry) rfl hs₁ hcut hd
  have hwcut := seamCompTM_firstReturn_ofCfg A (Sum.inr ()) D (Sum.inl entry)
    (Sum.inr (Sum.inr .done)) rfl hs₁ hcut hd
    (by rw [Cfg.mapState_state, Cfg.mapState_state]; rfl) hdcut
  have hinit : R.initCfg (pairEncode α w) = d₀.mapState Sum.inl := by
    apply Cfg.ext
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_state, Cfg.mapState_state,
        d₀, Option.map_some]
      rfl
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_inputPos, Cfg.mapState_inputPos,
        d₀]
    · funext j q
      simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes, Cfg.mapState_workTapes,
        d₀]
    · funext j
      simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos,
        Cfg.mapState_workTapePos, d₀]
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_output, Cfg.mapState_output,
        d₀]
  have htfinal : Function.update d₃.workTapes code (fun _ => none) =
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
        else if j.val = k + 1 then
          fun q => FinTM.bufferTape (unaryFin (E.machine α).q₀) (q - 2)
        else fun _ => none := by
    funext j q
    rw [ht₃]
    have hdtapes : d₂.workTapes = d₁.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hdtapes, ht₁]
    by_cases hjt : j = tbl
    · subst j
      simp only [tbl, Function.update_of_ne hct.symm, Function.update_of_ne hts,
        Function.update_self, ite_true]
    · have hjtv : j.val ≠ k := fun h => hjt (Fin.ext h)
      by_cases hjs : j = sm
      · subst j
        simp only [sm, Function.update_of_ne hcs.symm, Function.update_self,
          if_neg hjtv, ite_true]
      · have hjsv : j.val ≠ k + 1 := fun h => hjs (Fin.ext h)
        simp only [if_neg hjtv, if_neg hjsv]
        by_cases hjc : j = code
        · subst j
          rw [Function.update_self]
        · rw [Function.update_of_ne hjc, Function.update_of_ne hjs,
            Function.update_of_ne hjt, Function.update_idem]
          by_cases hjcap : j = cap
          · subst j
            rw [Function.update_self]
          · rw [Function.update_of_ne hjcap, Function.update_of_ne hjc]
  have hhfinal : Function.update d₃.workTapePos code 0 = fun _ => 0 := by
    funext j
    rw [hh₃]
    have hdheads : d₂.workTapePos = d₁.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hdheads, hh₁]
    by_cases hjc : j = code
    · subst j
      rw [Function.update_self]
    · rw [Function.update_of_ne hjc]
      by_cases hjs : j = sm
      · subst j
        rw [Function.update_self]
      · rw [Function.update_of_ne hjs]
        by_cases hjt : j = tbl
        · subst j
          rw [Function.update_self]
        · rw [Function.update_of_ne hjt, Function.update_idem]
          by_cases hjcap : j = cap
          · subst j
            rw [Function.update_self]
          · rw [Function.update_of_ne hjcap, Function.update_of_ne hjc]
  have hofinal : d₃.output = [] := by
    rw [ho₃ l le_rfl, Cfg.mapState_output]
    exact ho₁
  have hfinal : R.runFrom (R.initCfg (pairEncode α w)) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
          else if j.val = k + 1 then
            fun q => FinTM.bufferTape (unaryFin (E.machine α).q₀) (q - 2)
          else fun _ => none,
        fun _ => 0, []⟩ := by
    rw [hinit, MultiTapeTM.runFrom_with_q₀]
    rw [hw]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
      rfl
    · simp only [Cfg.mapState_inputPos]
    · funext j q
      simp only [Cfg.mapState_workTapes]
      rw [Cfg.mapState_workTapes]
      exact congrFun (congrFun htfinal j) q
    · funext j
      simp only [Cfg.mapState_workTapePos]
      rw [Cfg.mapState_workTapePos]
      exact congrFun hhfinal j
    · simp only [Cfg.mapState_output]
      rw [Cfg.mapState_output]
      exact hofinal
  refine ⟨hfinal, ?_, ?_, MultiTapeTM.spaceUsed_le_mul_succ R _ T⟩
  · intro u hu
    rw [hinit, MultiTapeTM.runFrom_with_q₀]
    exact hwcut u hu
  · intro u hu
    have hpre := MultiTapeTM.output_prefix R (R.initCfg (pairEncode α w)) hu
    rw [hfinal] at hpre
    exact List.prefix_nil.mp hpre

/-! ## U2-U: the self-application universal machine -/

/-- The startup's endpoint tapes, restricted to the forwarding loop's `k + 2`, are the encoding's
tapes at the decoded machine's initial configuration.

**Proof sketch.** Split the tape index into a mirrored tape and one of the two
auxiliary tapes. The initial mirrored tapes are blank; the table is unchanged,
and the summary agrees cell by cell, including its blank cell at zero. -/
private theorem uk_encode_init_tapes {k n : ℕ} {Q : Type} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) (j : Fin (k + 2)) :
    (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapes j =
      if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
      else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
      else fun _ => none := by
  have hw : (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapes j =
      Fin.addCases (motive := fun _ => ℤ → Option Bool) (M.initCfg x).workTapes (fun j =>
        if j = 0 then FinTM.bufferTape (tableBitsK M.tr)
        else StepBlock.summaryCells none (((M.initCfg x).state.map unaryFin).getD [])) j :=
    funext fun a => StepBlock.forwardLoopCfg_workTapes entry M (M.initCfg x) j a
  rw [hw]
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
  · rw [Fin.addCases_left, MultiTapeTM.initCfg_eq]
    have h1 : (Fin.castAdd 2 i).val ≠ k := by simp only [Fin.coe_castAdd]; omega
    have h2 : (Fin.castAdd 2 i).val ≠ k + 1 := by simp only [Fin.coe_castAdd]; omega
    rw [if_neg h1, if_neg h2]
    funext p
    rw [Cfg.init_workTapes]
  · rw [Fin.addCases_right, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some,
      Option.getD_some]
    by_cases h : j' = 0
    · subst h
      have h1 : (Fin.natAdd k (0 : Fin 2)).val = k := by simp only [Fin.coe_natAdd]; omega
      rw [if_pos rfl, if_pos h1]
    · have hj : j' = 1 := by omega
      subst hj
      have h1 : (Fin.natAdd k (1 : Fin 2)).val ≠ k := by simp only [Fin.coe_natAdd]; omega
      have h2 : (Fin.natAdd k (1 : Fin 2)).val = k + 1 := by simp only [Fin.coe_natAdd]; omega
      rw [if_neg (by decide), if_neg h1, if_pos h2]
      funext p
      rw [StepBlock.summaryCells_eq]
      by_cases hp : p = 0
      · rw [if_pos hp, hp]
        exact (FinTM.bufferTape_of_neg _ (by omega)).symm
      · rw [if_neg hp]

/-- The encoding of the initial configuration is at `entry`, with input head `1`, every head at
`0` and an empty output. -/
private theorem uk_encode_init_fields {k n : ℕ} {Q : Type} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) :
    (StepBlock.forwardLoopCfg entry M (M.initCfg x)).state = some entry ∧
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)).inputPos.val = 1 ∧
      (∀ j, (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapePos j = 0) ∧
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)).output = [] := by
  refine ⟨?_, ?_, fun j => ?_, ?_⟩
  · rw [StepBlock.forwardLoopCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some]
  · rw [StepBlock.forwardLoopCfg_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]; rfl
  · rw [StepBlock.forwardLoopCfg_workTapePos]
    refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
    · rw [Fin.addCases_left, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
    · rw [Fin.addCases_right]
  · rw [StepBlock.forwardLoopCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output]

/-- An encoded configuration is halted exactly when the source is, and carries its output. -/
private theorem uk_encode_halt {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    ((StepBlock.forwardLoopCfg entry M c).state = none ↔ c.state = none) ∧
      (StepBlock.forwardLoopCfg entry M c).output = c.output := by
  rw [StepBlock.forwardLoopCfg_state, StepBlock.forwardLoopCfg_output, Option.map_eq_none_iff]
  exact ⟨Iff.rfl, rfl⟩


/-- Embedding the initial loop configuration in the first tapes gives the startup's
endpoint, with its state replaced by the loop entry.

**Proof sketch.** Use the public reconstruction theorem for the emitting embedding.
The selected tapes and heads are the initial encoding's fields. An unselected
tape has index at least `k + 2`, so both tests in the startup layout are false. -/
private theorem uk_embed_init {k n K : ℕ} {P Q : Type} (exit : P) (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) :
    embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
      (fun _ _ => none) (fun _ => 0) []
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)) =
        (⟨some exit, 1,
          fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
            else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
            else fun _ => none,
          fun _ => 0, []⟩ : Cfg (K + (k + 2)) Bool P x).mapState (fun _ => entry) := by
  apply embedEmitCfg_eq
  · rw [Cfg.mapState_state]
    exact (uk_encode_init_fields entry M x).1
  · apply Fin.ext
    rw [Cfg.mapState_inputPos]
    exact (uk_encode_init_fields entry M x).2.1
  · rw [List.nil_append, Cfg.mapState_output]
    exact (uk_encode_init_fields entry M x).2.2.2
  · intro i
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      exact congrFun (uk_encode_init_tapes entry M x i) a
    · rw [Cfg.mapState_workTapePos]
      exact (uk_encode_init_fields entry M x).2.2.1 i
  · intro j hj
    have hjge : k + 2 ≤ j.val := by
      by_contra h
      have hlt : j.val < k + 2 := by omega
      apply hj
      refine ⟨⟨j.val, hlt⟩, ?_⟩
      apply Fin.ext
      rfl
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      dsimp only
      rw [if_neg (by omega : j.val ≠ k), if_neg (by omega : j.val ≠ k + 1)]
    · rw [Cfg.mapState_workTapePos]

/-- The startup followed by the emitting loop on the first `k + 2` tapes. -/
private noncomputable def uk_loopTM {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) :
    MultiTapeTM (K + (k + 2)) Bool (P ⊕ Q) :=
  { seamCompTM R exit
      (embedEmitTM (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2))) L) entry with
    q₀ := Sum.inl R.q₀ }

/-- Initial configurations commute with a state map that sends the initial states correctly. -/
private theorem uk_init_mapState {m : ℕ} {P Q : Type}
    (A : MultiTapeTM m Bool P) (B : MultiTapeTM m Bool Q) (f : P → Q)
    (hq : B.q₀ = f A.q₀) (x : List Bool) : B.initCfg x = (A.initCfg x).mapState f := by
  refine Cfg.ext ?_ ?_ (funext fun j => funext fun a => ?_) (funext fun j => ?_) ?_
  all_goals
    simp only [MultiTapeTM.initCfg_eq, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
      Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes, Cfg.init_workTapePos,
      Cfg.init_output, Option.map_some, hq]

/-- The composed machine starts in the startup's initial configuration, with a left state. -/
private theorem uk_loop_init {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) (x : List Bool) :
    (uk_loopTM R exit L entry).initCfg x = (R.initCfg x).mapState Sum.inl := by
  exact uk_init_mapState R (uk_loopTM R exit L entry) Sum.inl rfl x

/-- A live startup endpoint makes the composed startup prefix live. -/
private theorem uk_loop_pre_live {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool} (T : ℕ)
    (hlive : (R.runFrom (R.initCfg x) T).state ≠ none)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (t : ℕ) (ht : t ≤ T) :
    ((uk_loopTM R exit L entry).runFrom ((uk_loopTM R exit L entry).initCfg x) t).state ≠
      none := by
  rw [uk_loop_init, uk_loopTM, MultiTapeTM.runFrom_with_q₀,
    seamCompTM_runFrom_left R exit _ entry hcut t ht, Cfg.mapState_state]
  intro hh
  exact MultiTapeTM.runFrom_state_ne_none_of_le R (R.initCfg x) T hlive t ht
    (Option.map_eq_none_iff.mp hh)

/-- At every time after the seam, the composed run is the embedded continuation run.
The continuation may be either the native forwarding loop or its suffix host. -/
private theorem uk_loop_run {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool}
    (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
    (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (hcfg : d.mapState (fun _ => entry) =
      embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] c) (t : ℕ) :
    (uk_loopTM R exit L entry).runFrom ((uk_loopTM R exit L entry).initCfg x)
        (T + 1 + t) =
      (embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] (L.runFrom c t)).mapState Sum.inr := by
  rw [uk_loop_init, uk_loopTM, MultiTapeTM.runFrom_with_q₀,
    seamCompTM_runFrom_right R exit _ entry hrun hexit hcut t, hcfg, embedEmitTM_runFrom]

/-- A halting source run gives a bounded loop run to its encoded final configuration.

**Proof sketch.** Choose the first source halt. The lockstep applies up to that
time, and each summand in its simulated time is bounded by the per-step bound.
Absorption identifies the first halted configuration with the given final one. -/
private theorem uk_loop_forward {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ) (D : ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hcost : ∀ c, c.state ≠ none → cost c ≤ D) (t : ℕ)
    (hhalt : (M.runFrom (M.initCfg x) t).state = none) :
    ∃ t₀ ≤ t, (∀ u < t₀, (M.runFrom (M.initCfg x) u).state ≠ none) ∧
      (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) ≤ D * t ∧
      L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x))
          (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) =
        StepBlock.forwardLoopCfg entry M (M.runFrom (M.initCfg x) t) := by
  classical
  let hex : ∃ u, (M.runFrom (M.initCfg x) u).state = none := ⟨t, hhalt⟩
  let t₀ := Nat.find hex
  have hle : t₀ ≤ t := Nat.find_min' hex hhalt
  have hfirst : ∀ u < t₀, (M.runFrom (M.initCfg x) u).state ≠ none :=
    fun u hu => Nat.find_min hex hu
  have hsame : M.runFrom (M.initCfg x) t₀ = M.runFrom (M.initCfg x) t := by
    symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ (Nat.find_spec hex)]
  refine ⟨t₀, hle, hfirst, ?_, ?_⟩
  · calc
      _ ≤ ∑ _u ∈ Finset.range t₀, D := Finset.sum_le_sum fun u hu =>
        hcost _ (hfirst u (Finset.mem_range.mp hu))
      _ = D * t₀ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
      _ ≤ D * t := Nat.mul_le_mul_left D hle
  · rw [hlock.runFrom (M.initCfg x) t₀ (by
      simpa only [Set.mem_singleton_iff] using hfirst), hsame]

/-- A source that remains live forever keeps its forwarding loop live forever.

**Proof sketch.** For a target time `v`, simulate `v + 1` source steps. Every
cost is positive, so their sum exceeds `v`; the lockstep cut gives liveness. -/
private theorem uk_loop_live {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hpos : ∀ c, c.state ≠ none → 0 < cost c)
    (hlive : ∀ u, (M.runFrom (M.initCfg x) u).state ≠ none) (v : ℕ) :
    (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).state ≠ none := by
  have hsum : v + 1 ≤ ∑ u ∈ Finset.range (v + 1), cost (M.runFrom (M.initCfg x) u) := by
    calc
      _ = ∑ _u ∈ Finset.range (v + 1), (1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
      _ ≤ _ := Finset.sum_le_sum fun u _ => hpos _ (hlive u)
  have hcut := hlock.cut (M.initCfg x) (v + 1)
    (fun u _ => by simpa only [Set.mem_singleton_iff] using hlive u) v (by omega)
  simpa only [Set.mem_singleton_iff] using hcut

/-- Every completed loop output is the source machine's completed output.

**Proof sketch.** If the source never halted, positivity and the lockstep cut
would keep the loop live at the given time. Choose a source halt and apply the
forward lemma. The loop is now halted at both times, so its output agrees at
their maximum; the encoding preserves the source's output. -/
private theorem uk_loop_converse {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ) (D : ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hcost : ∀ c, c.state ≠ none → 0 < cost c ∧ cost c ≤ D) (u : ℕ)
    (hhalt : (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) u).state = none) :
    ∃ t, (M.runFrom (M.initCfg x) t).state = none ∧
      (M.runFrom (M.initCfg x) t).output =
        (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) u).output := by
  classical
  have hex : ∃ t, (M.runFrom (M.initCfg x) t).state = none := by
    by_contra h
    have hsource : ∀ t, (M.runFrom (M.initCfg x) t).state ≠ none :=
      fun t ht => h ⟨t, ht⟩
    exact (uk_loop_live M L entry cost hlock (fun c hc => (hcost c hc).1) hsource u) hhalt
  obtain ⟨t, ht⟩ := hex
  obtain ⟨t₀, _, _, _, hr⟩ :=
    uk_loop_forward M L entry cost D hlock (fun c hc => (hcost c hc).2) t ht
  let v := ∑ i ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) i)
  have hv : (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).state = none := by
    rw [hr]
    exact (uk_encode_halt entry M _).1.mpr ht
  refine ⟨t, ht, ?_⟩
  calc
    _ = (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).output := by
      rw [hr, (uk_encode_halt entry M _).2]
    _ = (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) (max u v)).output :=
      (MultiTapeTM.runFrom_output_eq_of_halt L _ (Nat.le_max_right u v) hv).symm
    _ = _ := MultiTapeTM.runFrom_output_eq_of_halt L _ (Nat.le_max_left u v) hhalt

/-- The composed run uses the startup's space plus the embedded loop's per-tape bound.

**Proof sketch.** The seam's visited-set theorem bounds each tape by the union
of its startup and loop visits. A selected loop tape has the source loop's
visited set; an unselected tape visits just its initial cell. Count each union
and sum over the host's tapes, using the public space equations. -/
private theorem uk_loop_space {k K n : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) (T : ℕ)
    (hrun : R.runFrom (R.initCfg x) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
          else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
          else fun _ => none,
        fun _ => 0, []⟩)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (t B S : ℕ) (hB : R.spaceUsed (R.initCfg x) T ≤ B) (hS : 1 ≤ S)
    (hloop : ∀ i, L.spaceUsedByTape
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)) t i ≤ S) :
    (uk_loopTM R exit L entry).spaceUsed ((uk_loopTM R exit L entry).initCfg x)
        (T + 1 + t) ≤ B + (K + (k + 2)) * S := by
  classical
  let σ := Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2))
  let A := embedEmitTM σ L
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  let e := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] c
  let d : Cfg (K + (k + 2)) Bool P x :=
    ⟨some exit, 1,
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
        else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
        else fun _ => none,
      fun _ => 0, []⟩
  have he : d.mapState (fun _ => entry) = e := (uk_embed_init exit entry M x).symm
  have hA : ∀ j, A.spaceUsedByTape e t j ≤ S := by
    intro j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      rw [(embedEmitTM_visitedByTapeHead σ L _ _ [] c t i).2]
      exact hloop i
    · rw [(embedEmitTM_visitedByTapeHead_frame σ L _ _ [] c t j hj).2]
      exact hS
  have htape (j : Fin (K + (k + 2))) :
      (uk_loopTM R exit L entry).spaceUsedByTape
          ((uk_loopTM R exit L entry).initCfg x) (T + 1 + t) j ≤
        R.spaceUsedByTape (R.initCfg x) T j + S := by
    rw [MultiTapeTM.spaceUsedByTape_eq_card]
    have hsub := seamCompTM_visitedByTapeHead_ofCfg R exit A entry
      (c₁ := d) (T₂ := t) hrun rfl hcut j
    rw [he] at hsub
    have hown : (uk_loopTM R exit L entry).visitedByTapeHead
        ((uk_loopTM R exit L entry).initCfg x) (T + 1 + t) j ⊆
        (seamCompTM R exit A entry).visitedByTapeHead
          ((R.initCfg x).mapState Sum.inl) (T + 1 + t) j := by
      intro p hp
      rw [MultiTapeTM.mem_visitedByTapeHead_iff] at hp ⊢
      obtain ⟨u, hu, hp⟩ := hp
      refine ⟨u, hu, ?_⟩
      rw [uk_loop_init, uk_loopTM, MultiTapeTM.runFrom_with_q₀] at hp
      exact hp
    calc
      _ ≤ (R.visitedByTapeHead (R.initCfg x) T j ∪ A.visitedByTapeHead e t j).card :=
        Finset.card_le_card (hown.trans hsub)
      _ ≤ (R.visitedByTapeHead (R.initCfg x) T j).card +
          (A.visitedByTapeHead e t j).card := Finset.card_union_le _ _
      _ = R.spaceUsedByTape (R.initCfg x) T j + A.spaceUsedByTape e t j := by
        rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card]
      _ ≤ _ := Nat.add_le_add_left (hA j) _
  rw [MultiTapeTM.spaceUsed_eq_sum]
  calc
    _ ≤ ∑ j, (R.spaceUsedByTape (R.initCfg x) T j + S) :=
      Finset.sum_le_sum fun j _ => htape j
    _ = R.spaceUsed (R.initCfg x) T + (K + (k + 2)) * S := by
      rw [Finset.sum_add_distrib, ← MultiTapeTM.spaceUsed_eq_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_right hB _

/-- **U2-U, the self-application universal machine, with time and space ledgers and the
converse** [AB09, Theorem 1.9 and Exercise 4.1, at self-application]. For a `k`-tape scheme `E`
there is a binary machine `U` such that for every code `α` there is a constant `C > 0`
(depending on `α` only) with, for every `w`:
* whenever the machine coded by `α` halts on `pairEncode α w` with `output` within `t` steps,
  `U` halts on the same input with the same `output` within `C · (t + 1)` steps, having visited
  by then at most `C · (s + 1)` cells, `s` the coded machine's cells by time `t`;
* every completed output of `U` on `pairEncode α w` is a completed output of the coded machine
  there (so divergence is preserved).

`C` depends on the code string, as in `Turing.universal` (Argument E): it absorbs the canonizer's
arbitrary time and the table's length. B6's `Turing.exists_selfUniversal` is the case `k = 1`
(forward clause, space only).

**Proof sketch.** Startup, then H2-F. (i) U2-S reaches, after `T_α` steps and within `B_α`
cells, H2-F's encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg (pairEncode α w))` of
the coded machine `M := E.machine α`, on the block's tapes, the other tapes blank; seam it into
H2-F's machine `L` (R2, R1 on the first `k + 2` tapes). (ii) H2-F's lockstep
(`Turing.Lockstep.runFrom`) runs `M` from its initial configuration: after `M` halts at `t`,
`L` is at the encoding of the halted configuration, halted, with `M`'s output, after
`Σ_{u < t} cost ≤ (50 · (|tableBitsK| + 1) + C_L) · t` steps; so the time is at most
`T_α + (50 · (|tableBitsK| + 1) + C_L) · t ≤ C · (t + 1)`. (iii) Space: the mirrored heads visit
only `M`'s cells, at most `s`; the auxiliary heads stay in an interval of length
`2 (50 · (|tableBitsK| + 1) + C_L) + 1`; the startup `B_α`; in all `≤ C · (s + 1)`, and the
halted configuration is frozen afterwards. (iv) Converse: by the lockstep's cut
(`Turing.Lockstep.cut`) `L` is live while `M` is, and an encoded live configuration is live, so
`U` halts only at the encoding of a halted configuration of `M`, whose output is `M`'s. -/
theorem exists_selfUniversalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧ ∀ w : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (E.toFinTM α).ComputesInTime (pairEncode α w) output t →
        U.ComputesInTime (pairEncode α w) output (C * (t + 1)) ∧
        U.tm.spaceUsed (U.tm.initCfg (pairEncode α w)) (C * (t + 1)) ≤
          C * ((E.toFinTM α).tm.spaceUsed ((E.toFinTM α).tm.initCfg (pairEncode α w)) t + 1)) ∧
      ∀ output : List Bool, (∃ t', U.ComputesInTime (pairEncode α w) output t') →
        ∃ t, (E.toFinTM α).ComputesInTime (pairEncode α w) output t := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTMK k E
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  obtain ⟨Q, fQ, dQ, L, entry, C_L, hL⟩ := StepBlock.exists_forwardLoopTM k
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  let U : FinTM Bool :=
    { k := K + (k + 2), State := P ⊕ Q, tm := uk_loopTM R exit L entry }
  refine ⟨U, ?_⟩
  intro α
  obtain ⟨T, B, hRα⟩ := hR α
  let M := E.machine α
  let D := 50 * ((tableBitsK M.tr).length + 1) + C_L
  let N := K + (k + 2)
  let C := T + 1 + D + B + N * (2 * D + 1) + N
  have hTC : T + 1 ≤ C := by dsimp only [C]; omega
  have hDC : D ≤ C := by dsimp only [C]; omega
  have hNC : N ≤ C := by dsimp only [C]; omega
  have hBC : B + N * (2 * D + 1) ≤ C := by dsimp only [C]; omega
  refine ⟨C, by omega, ?_⟩
  intro w
  let z := pairEncode α w
  obtain ⟨hrun, hcut, _, hB⟩ := hRα w
  obtain ⟨cost, hlock, hcost, hledger⟩ := hL (x := z) M
  have hUrun := uk_loop_run R exit L entry
    (StepBlock.forwardLoopCfg entry M (M.initCfg z)) (R.runFrom (R.initCfg z) T) T rfl
    (by rw [hrun]) hcut (by rw [hrun]; exact (uk_embed_init exit entry M z).symm)
  constructor
  · intro output t hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff (E.toFinTM α) z output t).mp hcomp
    obtain ⟨t₀, ht₀, hfirst, hvbound, hr⟩ :=
      uk_loop_forward M L entry cost D hlock (fun c hc => (hcost c hc).2) t hhalt
    let v := ∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg z) u)
    have hUhalt : (U.tm.runFrom (U.tm.initCfg z) (T + 1 + v)).state = none := by
      rw [hUrun v, Cfg.mapState_state, embedEmitCfg_state, hr,
        StepBlock.forwardLoopCfg_state, hhalt, Option.map_none, Option.map_none]
    have hUout : (U.tm.runFrom (U.tm.initCfg z) (T + 1 + v)).output = output := by
      rw [hUrun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append, hr,
        StepBlock.forwardLoopCfg_output]
      exact hout
    have htime : T + 1 + v ≤ C * (t + 1) := by
      calc
        _ ≤ C + D * t := Nat.add_le_add hTC hvbound
        _ ≤ C + C * t := Nat.add_le_add_left (Nat.mul_le_mul_right t hDC) C
        _ = _ := by ring
    refine ⟨((FinTM.computesInTime_iff U z output (T + 1 + v)).mpr
      ⟨hUhalt, hUout⟩).mono htime, ?_⟩
    let s := M.spaceUsed (M.initCfg z) t
    have hloop : ∀ i, L.spaceUsedByTape
        (StepBlock.forwardLoopCfg entry M (M.initCfg z)) v i ≤ s + (2 * D + 1) := by
      intro i
      by_cases hi : i.val < k
      · let j : Fin k := ⟨i.val, hi⟩
        have hij : Fin.castAdd 2 j = i := Fin.ext rfl
        rw [← hij, MultiTapeTM.spaceUsedByTape_eq_card]
        calc
          _ ≤ (M.visitedByTapeHead (M.initCfg z) t₀ j).card :=
            Finset.card_le_card ((hledger (M.initCfg z) t₀ hfirst).1 j)
          _ ≤ (M.visitedByTapeHead (M.initCfg z) t j).card := Finset.card_le_card (by
            intro p hp
            rw [MultiTapeTM.mem_visitedByTapeHead_iff] at hp ⊢
            obtain ⟨u, hu, hp⟩ := hp
            exact ⟨u, hu.trans ht₀, hp⟩)
          _ = M.spaceUsedByTape (M.initCfg z) t j :=
            (MultiTapeTM.spaceUsedByTape_eq_card (tm := M) _ t j).symm
          _ ≤ s := MultiTapeTM.spaceUsedByTape_le_spaceUsed (tm := M) _ t j
          _ ≤ _ := by omega
      · rw [MultiTapeTM.spaceUsedByTape_eq_card]
        calc
          _ ≤ (Finset.Icc (-(D : ℤ)) (D : ℤ)).card :=
            Finset.card_le_card ((hledger (M.initCfg z) t₀ hfirst).2 i (by omega))
          _ = 2 * D + 1 := by rw [Int.card_Icc]; omega
          _ ≤ _ := by omega
    have hspace := uk_loop_space R exit L entry M z T hrun hcut v B
      (s + (2 * D + 1)) hB (by omega) hloop
    have hfreeze : U.tm.spaceUsed (U.tm.initCfg z) (C * (t + 1)) ≤
        U.tm.spaceUsed (U.tm.initCfg z) (T + 1 + v) := by
      rw [MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card]
      apply Finset.card_le_card
      intro p hp
      have splitVisits := MultiTapeTM.visitedByTapeHead_add_subset U.tm (U.tm.initCfg z)
        (T + 1 + v) (C * (t + 1) - (T + 1 + v)) j
      rw [Nat.add_sub_of_le htime] at splitVisits
      rcases Finset.mem_union.mp (splitVisits hp) with hpast | hfuture
      · exact hpast
      · rw [MultiTapeTM.mem_visitedByTapeHead_iff] at hfuture ⊢
        obtain ⟨u, _, he⟩ := hfuture
        rw [MultiTapeTM.runFrom_of_halt _ hUhalt] at he
        exact ⟨T + 1 + v, le_rfl, he⟩
    calc
      _ ≤ U.tm.spaceUsed (U.tm.initCfg z) (T + 1 + v) := hfreeze
      _ ≤ B + N * (s + (2 * D + 1)) := hspace
      _ = N * s + (B + N * (2 * D + 1)) := by ring
      _ ≤ C * s + C := Nat.add_le_add (Nat.mul_le_mul_right s hNC) hBC
      _ = _ := by dsimp only [s, M, EffectiveCodeK.toFinTM]; ring
  · intro output hcomp
    obtain ⟨u, hu⟩ := hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff U z output u).mp hu
    have hprefix := uk_loop_pre_live R exit L entry T
      (by rw [hrun]; exact Option.some_ne_none exit) hcut
    have hafter : T + 1 ≤ u := by
      by_contra h
      exact hprefix u (by omega) hhalt
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hafter
    rw [hUrun v, Cfg.mapState_state, embedEmitCfg_state, Option.map_eq_none_iff] at hhalt
    rw [hUrun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append] at hout
    obtain ⟨t, ht, ho⟩ := uk_loop_converse M L entry cost D hlock hcost v hhalt
    exact ⟨t, (FinTM.computesInTime_iff (E.toFinTM α) z output t).mpr
      ⟨ht, ho.trans hout⟩⟩

/-! ## U2-E: the code-first evaluator -/


/-- A header scan that writes one ruler mark per input cell. No public row writes a ruler
of the doubled header's length. States zero, one and two read aligned pairs; three returns. -/
private def uk_scanTM {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Fin 4) where
  q₀ := 0
  tr := fun q b _ =>
    if q = 3 then inputMoveAction 0 3
    else tapeAction i .pos (some (some true)) .pos
      (if q = 0 then if b = some false then 1 else 2
       else if q = 1 ∧ b = some true then 3 else 0)

/-- The scan presentation after writing a consecutive interval of ruler marks. -/
private def uk_scanCfg {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) : Cfg k Bool (Fin 4) z :=
  ⟨some q, ⟨d.inputPos.val + t, ht⟩,
    Function.update d.workTapes i
      (fun a => if d.workTapePos i ≤ a ∧ a < d.workTapePos i + t
        then some true else d.workTapes i a),
    Function.update d.workTapePos i (d.workTapePos i + t), d.output⟩

/-- Zero scan steps leave the initial live configuration unchanged. -/
private theorem uk_scan_zero {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (hd : d.state = some 0) :
    uk_scanCfg i d 0 0 (by have := d.inputPos.isLt; omega) = d := by
  apply Cfg.ext
  · exact hd.symm
  · apply Fin.ext; simp only [uk_scanCfg, Nat.add_zero]
  · funext j a
    simp only [uk_scanCfg, Nat.cast_zero, add_zero]
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
      rw [if_neg (by omega)]
    · rw [Function.update_of_ne hj]
  · simp only [uk_scanCfg, Nat.cast_zero, add_zero, Function.update_eq_self]
  · rfl

/-- One scan step writes and advances both heads, preserving every frame field.

**Proof sketch.** Read the transition with the public writing-action equation. Its
updated cell is exactly the new right endpoint of the already marked interval;
all other cells retain their previous value. -/
private theorem uk_scan_step {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 1) (hq : q ≠ 3) (b : Bool)
    (hb : (uk_scanCfg i d q t (by omega)).inputSymbol = some b) :
    (uk_scanTM i).step (uk_scanCfg i d q t (by omega)) =
      uk_scanCfg i d
        (if q = 0 then if b = false then 1 else 2
         else if q = 1 ∧ b = true then 3 else 0) (t + 1) (by omega) := by
  have ht' : (uk_scanTM i).tr q (uk_scanCfg i d q t (by omega)).inputSymbol
      (uk_scanCfg i d q t (by omega)).workTapeSymbols = tapeAction i .pos
        (some (some true)) .pos
        (if q = 0 then if b = false then 1 else 2
         else if q = 1 ∧ b = true then 3 else 0) := by
    simp only [uk_scanTM, if_neg hq, hb, Option.some.injEq]
  rw [step_of_tapeAction_write _ _ i .pos (some true) .pos rfl ht']
  apply Cfg.ext
  · rfl
  · rw [moveInputPos_pos_of_ne_right _ (by simp only [uk_scanCfg]; omega)]
    apply Fin.ext
    simp only [uk_scanCfg]
    omega
  · funext j a
    by_cases hj : j = i
    · subst j
      simp only [uk_scanCfg, Function.update_self, Nat.cast_add, Nat.cast_one]
      by_cases ha : a = d.workTapePos i + t
      · subst a
        rw [Function.update_self, if_pos (by omega)]
      · rw [Function.update_of_ne ha]
        by_cases ha' : d.workTapePos i ≤ a ∧ a < d.workTapePos i + t
        · rw [if_pos ha', if_pos (by omega)]
        · rw [if_neg ha', if_neg (by omega)]
    · simp only [uk_scanCfg, Function.update_of_ne hj]
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [uk_scanCfg, Function.update_self, Nat.cast_add, Nat.cast_one,
        SignType.pos_eq_one, SignType.coe_one, add_assoc]
    · simp only [uk_scanCfg, Function.update_of_ne hj]
  · rfl

/-- The scanner consumes one aligned pair, marking both input cells.

**Proof sketch.** The suffix equation gives the two input symbols through `getElem_drop`.
Apply the one-step result twice. The intermediate state stores the first bit,
and the second bit either returns on the separator or resumes the pair scan. -/
private theorem uk_scan_pair {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p t : ℕ) (hp : d.inputPos.val = 1 + p)
    (a b : Bool) (rest : List Bool) (hz : z.drop (p + t) = a :: b :: rest) :
    let hlen : d.inputPos.val + (t + 2) < z.length + 2 := by
      have h := congrArg List.length hz
      simp only [List.length_drop, List.length_cons] at h
      omega
    let c := uk_scanCfg i d 0 t (by omega)
    (uk_scanTM i).runFrom c 2 =
        uk_scanCfg i d (if a = false ∧ b = true then 3 else 0) (t + 2) hlen ∧
      (∀ v < 2, ((uk_scanTM i).runFrom c v).state ≠ some 3) := by
  have hlen : p + t + 2 ≤ z.length := by
    have h := congrArg List.length hz
    simp only [List.length_drop, List.length_cons] at h
    omega
  dsimp only
  have ha : z[p + t]'(by omega) = a := by
    have hh : (z.drop (p + t))[0]'(by rw [hz]; simp) = a := by
      simp only [hz, List.getElem_cons_zero]
    simpa only [List.getElem_drop, Nat.add_zero] using hh
  have hb : z[p + t + 1]'(by omega) = b := by
    have hh : (z.drop (p + t))[1]'(by rw [hz]; simp) = b := by
      simp only [hz, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa only [List.getElem_drop] using hh
  let q : Fin 4 := if a = false then 1 else 2
  have h1 : (uk_scanTM i).step (uk_scanCfg i d 0 t (by omega)) =
      uk_scanCfg i d q (t + 1) (by omega) := by
    have read : (uk_scanCfg i d 0 t (by omega)).inputSymbol = some a := by
      rw [inputSymbolInner (p + t) (by simp only [uk_scanCfg]; omega) (by omega), ha]
    simpa only [if_pos rfl] using uk_scan_step i d 0 t (by omega) (by decide) a read
  have h2 : (uk_scanTM i).step (uk_scanCfg i d q (t + 1) (by omega)) =
      uk_scanCfg i d (if a = false ∧ b = true then 3 else 0) (t + 2) (by omega) := by
    have read : (uk_scanCfg i d q (t + 1) (by omega)).inputSymbol = some b := by
      rw [inputSymbolInner (p + t + 1) (by simp only [uk_scanCfg]; omega) (by omega), hb]
    have step := uk_scan_step i d q (t + 1) (by omega)
      (by dsimp only [q]; split <;> decide) b read
    cases a <;> cases b <;> simpa only [q, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, and_self, and_false, false_and, true_and] using step
  have one (e : Cfg k Bool (Fin 4) z) :
      (uk_scanTM i).runFrom e 1 = (uk_scanTM i).step e := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  constructor
  · calc
      _ = (uk_scanTM i).runFrom
          ((uk_scanTM i).runFrom (uk_scanCfg i d 0 t (by omega)) 1) 1 :=
        MultiTapeTM.runFrom_add _ 1 1
      _ = _ := by rw [one, one, h1, h2]
  · intro v hv
    have casesv : v = 0 ∨ v = 1 := by omega
    rcases casesv with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
      change some (0 : Fin 4) ≠ some 3
      decide
    · rw [one, h1]
      change some q ≠ some 3
      cases a <;> decide

/-- The scanner consumes one doubled header from any native input offset.

**Proof sketch.** Induct on the header word. Every doubled bit takes two steps
and returns to the pair-reading state; the separator takes two steps and returns.
The suffix equation is advanced with `drop_drop`, while the exact-time cut is
split before and after each pair. -/
private theorem uk_scan_header {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (u v : List Bool) (t : ℕ) (hz : z.drop (p + t) = pairEncode u v) :
    let hlen : d.inputPos.val + (t + (2 * u.length + 2)) < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    (uk_scanTM i).runFrom (uk_scanCfg i d 0 t (by omega)) (2 * u.length + 2) =
        uk_scanCfg i d 3 (t + (2 * u.length + 2)) hlen ∧
      (∀ r < 2 * u.length + 2,
        ((uk_scanTM i).runFrom (uk_scanCfg i d 0 t (by omega)) r).state ≠ some 3) := by
  have length_bound : p + t + (2 * u.length + 2) ≤ z.length := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    omega
  dsimp only
  induction u generalizing t with
  | nil =>
    have hz' : z.drop (p + t) = false :: true :: v := by
      simpa only [pairEncode_eq, List.flatMap_nil, List.nil_append,
        List.cons_append] using hz
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, and_self, ↓reduceIte]
      using uk_scan_pair i d p t hp false true v hz'
  | cons b u ih =>
    have hz' : z.drop (p + t) = b :: b :: pairEncode u v := by
      simpa only [pairEncode_eq, List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc] using hz
    have pair := uk_scan_pair i d p t hp b b (pairEncode u v) hz'
    have hpair : (uk_scanTM i).runFrom (uk_scanCfg i d 0 t (by omega)) 2 =
        uk_scanCfg i d 0 (t + 2) (by omega) := by
      cases b <;> simpa only [Bool.false_eq_true, Bool.true_eq_false,
        false_and, and_false, ↓reduceIte] using pair.1
    have suffix : z.drop (p + (t + 2)) = pairEncode u v := by
      rw [show p + (t + 2) = (p + t) + 2 by omega, ← List.drop_drop, hz']
      rfl
    have tail := ih (t + 2) suffix (by simp only [List.length_cons] at length_bound; omega)
    have duration : 2 * (b :: u).length + 2 = 2 + (2 * u.length + 2) := by
      simp only [List.length_cons]
      omega
    constructor
    · calc
        _ = (uk_scanTM i).runFrom (uk_scanCfg i d 0 t (by omega))
            (2 + (2 * u.length + 2)) := congrArg _ duration
        _ = uk_scanCfg i d 3 (t + 2 + (2 * u.length + 2)) (by omega) := by
          rw [MultiTapeTM.runFrom_add, hpair, tail.1]
        _ = _ := by congr 1; omega
    · intro r hr
      by_cases hsmall : r < 2
      · exact pair.2 r hsmall
      · have hr' : r - 2 < 2 * u.length + 2 := by omega
        rw [show r = 2 + (r - 2) by omega, MultiTapeTM.runFrom_add, hpair]
        exact tail.2 (r - 2) hr'

/-- The framed, silent header-ruler scan, from any input offset and any ruler head.
The painted interval overwrites its old contents; all cells outside it are preserved,
so consecutive invocations can write a single ruler for consecutive headers.

**Proof sketch.** Instantiate the header induction at time zero. The endpoint has
the original output; output-prefix monotonicity in both directions gives silence
at every intermediate time. -/
private theorem uk_scan_run {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (hd : d.state = some 0) (u v : List Bool) (hz : z.drop p = pairEncode u v) :
    let hlen : d.inputPos.val + (2 * u.length + 2) < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    (uk_scanTM i).runFrom d (2 * u.length + 2) =
        uk_scanCfg i d 3 (2 * u.length + 2) hlen ∧
      (∀ t < 2 * u.length + 2, ((uk_scanTM i).runFrom d t).state ≠ some 3) ∧
      (∀ t ≤ 2 * u.length + 2, ((uk_scanTM i).runFrom d t).output = d.output) := by
  have hz' : z.drop (p + 0) = pairEncode u v := by simpa only [Nat.add_zero] using hz
  have h := uk_scan_header i d p hp u v 0 hz'
  simp only [Nat.zero_add, uk_scan_zero i d hd] at h
  refine ⟨h.1, h.2, ?_⟩
  intro t ht
  have hle := MultiTapeTM.output_prefix (uk_scanTM i) d ht
  have hge := MultiTapeTM.output_prefix (uk_scanTM i) d (Nat.zero_le t)
  rw [h.1] at hle
  rw [MultiTapeTM.runFrom_zero] at hge
  exact hle.eq_of_length_le hge.length_le

/-- On an initially blank ruler tape, the marked interval is the standard unary buffer.

**Proof sketch.** Read the buffer through its public equation. For a nonnegative
cell, a replicate lookup is present precisely before the interval's length;
negative cells and cells beyond the interval stay blank. -/
private theorem uk_scan_ruler {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) (hblank : ∀ a, d.workTapes i a = none) :
    ∀ a : ℤ, (uk_scanCfg i d q t ht).workTapes i (d.workTapePos i + a) =
      FinTM.bufferTape (List.replicate t true) a := by
  intro a
  simp only [uk_scanCfg, Function.update_self, hblank, FinTM.bufferTape_eq]
  by_cases ha : 0 ≤ a
  · rw [if_pos ha]
    by_cases hat : a < t
    · rw [if_pos (by omega), List.getElem?_replicate]
      simp only [show a.toNat < t by omega, ↓reduceIte]
    · rw [if_neg (by omega), List.getElem?_replicate]
      simp only [show ¬a.toNat < t by omega, ↓reduceIte]
  · rw [if_neg ha, if_neg (by omega)]

/-- The header scan followed by the public work-tape rewind. -/
private def uk_headerTM {k : ℕ} (i : Fin k) :
    MultiTapeTM k Bool (Fin 4 ⊕ RewindPhase) :=
  { seamCompTM (uk_scanTM i) 3 (rewindTM k i) .start with q₀ := Sum.inl 0 }

/-- Scanning and rewinding prepares a ruler without moving the other heads.

**Proof sketch.** The scan writes the unary buffer and ends immediately after it.
Its buffer equation supplies the framed rewind's hypothesis. The public seam
combines their exact runs and first-return cuts; its endpoint resets just the
ruler head, which restores the original vector of heads. -/
private theorem uk_header_run {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (hd : d.state = some 0) (u v : List Bool) (hz : z.drop p = pairEncode u v)
    (hblank : ∀ a, d.workTapes i a = none) :
    let ℓ := 2 * u.length + 2
    let hlen : d.inputPos.val + ℓ < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    let e : Cfg k Bool (Fin 4 ⊕ RewindPhase) z :=
      ⟨some (Sum.inr .done), ⟨d.inputPos.val + ℓ, hlen⟩,
        Function.update d.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - d.workTapePos i)),
        d.workTapePos, d.output⟩
    (uk_headerTM i).runFrom (d.mapState Sum.inl) (2 * ℓ + 3) = e ∧
      (∀ t < 2 * ℓ + 3,
        ((uk_headerTM i).runFrom (d.mapState Sum.inl) t).state ≠ some (Sum.inr .done)) := by
  dsimp only
  let ℓ := 2 * u.length + 2
  have hlen : d.inputPos.val + ℓ < z.length + 2 := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    dsimp only [ℓ]; omega
  let c := uk_scanCfg i d 3 ℓ hlen
  obtain ⟨hscan, hcut, _⟩ := uk_scan_run i d p hp hd u v hz
  have hrewind := rewindTM_run_ofCfg i (List.replicate ℓ true) ℓ
    (by rw [List.length_replicate]) (c.mapState fun _ => RewindPhase.start)
    (by rw [Cfg.mapState_state]; rfl) (by
      intro a _ _
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      have hh := uk_scan_ruler i d 3 ℓ hlen hblank a
      simpa only [c, uk_scanCfg, Function.update_self, add_sub_cancel_right] using hh)
  let r : Cfg k Bool RewindPhase z :=
    { c.mapState (fun _ => RewindPhase.start) with
      state := some .done
      workTapePos := Function.update (c.mapState (fun _ => RewindPhase.start)).workTapePos i
        ((c.mapState (fun _ => RewindPhase.start)).workTapePos i - ℓ) }
  have endpoint : r.mapState Sum.inr =
      (⟨some (Sum.inr RewindPhase.done), ⟨d.inputPos.val + ℓ, hlen⟩,
        Function.update d.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - d.workTapePos i)),
        d.workTapePos, d.output⟩ : Cfg k Bool (Fin 4 ⊕ RewindPhase) z) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]; rfl
    · funext j a
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      by_cases hj : j = i
      · subst j
        have hh := uk_scan_ruler i d 3 ℓ hlen hblank (a - d.workTapePos i)
        simpa only [add_sub_cancel, Function.update_self] using hh
      · simp only [c, uk_scanCfg, Function.update_of_ne hj]
    · funext j
      rw [Cfg.mapState_workTapePos]
      by_cases hj : j = i
      · subst j
        simp only [r, c, Cfg.mapState_workTapePos, uk_scanCfg,
          Function.update_self, add_sub_cancel_right]
      · simp only [r, c, Cfg.mapState_workTapePos, uk_scanCfg, Function.update_of_ne hj]
    · rw [Cfg.mapState_output, Cfg.mapState_output]; rfl
  have total : 2 * ℓ + 3 = ℓ + 1 + (ℓ + 2) := by omega
  constructor
  · rw [uk_headerTM, MultiTapeTM.runFrom_with_q₀, total]
    exact (seamCompTM_run_ofCfg (uk_scanTM i) 3 (rewindTM k i) .start
      hscan rfl hcut hrewind.1).trans endpoint
  · intro t ht
    rw [uk_headerTM, MultiTapeTM.runFrom_with_q₀]
    exact seamCompTM_firstReturn_ofCfg (uk_scanTM i) 3 (rewindTM k i) .start .done
      hscan rfl hcut hrewind.1 rfl hrewind.2.1 t (by omega)


/-- The startup embedded with one extra tape, followed by the header ruler preparation. -/
private noncomputable def uk_suffixStartupTM {k K : ℕ} {P : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P) :
    MultiTapeTM (K + (k + 3)) Bool (P ⊕ (Fin 4 ⊕ RewindPhase)) :=
  { seamCompTM
      ({ embedEmitTM (Fin.castLEEmb (by omega)) R with q₀ := R.q₀ }) exit
      (uk_headerTM ⟨k + 2, by omega⟩) (Sum.inl 0) with q₀ := Sum.inl R.q₀ }

/-- The initialized simulation bank and header ruler, ready for the suffix host. -/
private def uk_suffixCfg {k K n : ℕ} {P : Type} (q : P)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (z : List Bool) (ℓ : ℕ)
    (hℓ : ℓ + 1 < z.length + 2) : Cfg (K + (k + 3)) Bool P z :=
  ⟨some q, ⟨ℓ + 1, hℓ⟩,
    fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
      else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
      else if j.val = k + 2 then FinTM.bufferTape (List.replicate ℓ true)
      else fun _ => none,
    fun _ => 0, []⟩

/-- The original startup followed by the header scan and rewind reaches the suffix seam.

**Proof sketch.** Embed the startup in one more tape and reconstruct its initial
and final configurations with the public embedding theorem. At the endpoint,
the tape immediately after the simulation bank is blank. The framed header
contract prepares it, and the public seam composes the two runs and their cuts. -/
private theorem uk_suffixStartup_run {k K n : ℕ} {P : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (α x : List Bool) (T : ℕ)
    (hrun : R.runFrom (R.initCfg (pairEncode α x)) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
          else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
          else fun _ => none,
        fun _ => 0, []⟩)
    (hcut : ∀ t < T, (R.runFrom (R.initCfg (pairEncode α x)) t).state ≠ some exit) :
    let ℓ := 2 * α.length + 2
    let hlen : ℓ + 1 < (pairEncode α x).length + 2 := by rw [length_pairEncode]; omega
    (uk_suffixStartupTM R exit).runFrom ((uk_suffixStartupTM R exit).initCfg (pairEncode α x))
        (T + 1 + (2 * ℓ + 3)) = uk_suffixCfg (Sum.inr (Sum.inr .done)) M
          (pairEncode α x) ℓ hlen ∧
      (∀ t < T + 1 + (2 * ℓ + 3),
        ((uk_suffixStartupTM R exit).runFrom
          ((uk_suffixStartupTM R exit).initCfg (pairEncode α x)) t).state ≠
            some (Sum.inr (Sum.inr .done))) := by
  let z := pairEncode α x
  let ℓ := 2 * α.length + 2
  let σ := Fin.castLEEmb (by omega : K + (k + 2) ≤ K + (k + 3))
  let A := ({ embedEmitTM σ R with q₀ := R.q₀ } : MultiTapeTM (K + (k + 3)) Bool P)
  let i : Fin (K + (k + 3)) := ⟨k + 2, by omega⟩
  let B := uk_headerTM i
  let d : Cfg (K + (k + 3)) Bool P z :=
    ⟨some exit, 1,
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
        else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
        else fun _ => none,
      fun _ => 0, []⟩
  have initEmbed : embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (R.initCfg z) =
      A.initCfg z := by
    apply embedEmitCfg_eq
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_state]
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_inputPos]
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_output, List.nil_append]
    · intro j
      constructor
      · funext a
        simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes]
      · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos]
    · intro j _
      constructor
      · funext a
        simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes]
      · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos]
  have aRun : A.runFrom (A.initCfg z) T = d := by
    rw [← initEmbed]
    simp only [A, MultiTapeTM.runFrom_with_q₀, embedEmitTM_runFrom, z, hrun]
    apply embedEmitCfg_eq
    · rfl
    · rfl
    · rfl
    · intro j; exact ⟨rfl, rfl⟩
    · intro j hj
      have hge : K + (k + 2) ≤ j.val := by
        by_contra h
        apply hj
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        apply Fin.ext; rfl
      constructor
      · funext a
        simp only [d, if_neg (by omega : j.val ≠ k), if_neg (by omega : j.val ≠ k + 1)]
      · rfl
  have aCut : ∀ t < T, (A.runFrom (A.initCfg z) t).state ≠ some exit := by
    intro t ht
    rw [← initEmbed]
    simp only [A, MultiTapeTM.runFrom_with_q₀, embedEmitTM_runFrom, embedEmitCfg_state]
    exact hcut t ht
  let c := d.mapState (fun _ => (0 : Fin 4))
  have cstate : c.state = some 0 := by rw [Cfg.mapState_state]; rfl
  have cpos : c.inputPos.val = 1 + 0 := by rw [Cfg.mapState_inputPos]; rfl
  have cblank : ∀ a, c.workTapes i a = none := by
    intro a
    rw [Cfg.mapState_workTapes]
    simp only [d, i, if_neg (by omega : k + 2 ≠ k), if_neg (by omega : k + 2 ≠ k + 1)]
  obtain ⟨bRun, bCut⟩ := uk_header_run i c 0 cpos cstate α x
    (by rw [List.drop_zero]) cblank
  have cmap : c.mapState Sum.inl = d.mapState (fun _ => (Sum.inl 0 : Fin 4 ⊕ RewindPhase)) := by
    rw [Cfg.mapState_mapState]; rfl
  rw [cmap] at bRun bCut
  have clen : c.inputPos.val + ℓ < z.length + 2 := by
    rw [cpos]
    dsimp only [z, ℓ]
    rw [length_pairEncode]
    omega
  have plen : ℓ + 1 < z.length + 2 := by
    dsimp only [z, ℓ]
    rw [length_pairEncode]
    omega
  have final :
      (⟨some (Sum.inr RewindPhase.done),
        ⟨c.inputPos.val + ℓ, clen⟩,
        Function.update c.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - c.workTapePos i)),
        c.workTapePos, c.output⟩ : Cfg (K + (k + 3)) Bool (Fin 4 ⊕ RewindPhase) z).mapState
          Sum.inr =
        uk_suffixCfg (Sum.inr (Sum.inr .done) : P ⊕ (Fin 4 ⊕ RewindPhase)) M z ℓ plen := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos]
      apply Fin.ext
      change c.inputPos.val + ℓ = ℓ + 1
      rw [cpos]
      omega
    · funext j a
      rw [Cfg.mapState_workTapes]
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, c, Cfg.mapState_workTapePos, d, sub_zero,
          uk_suffixCfg, i, if_neg (by omega : k + 2 ≠ k),
          if_neg (by omega : k + 2 ≠ k + 1), ↓reduceIte]
      · have hjv : j.val ≠ k + 2 := by intro h; apply hj; exact Fin.ext h
        simp only [Function.update_of_ne hj, c, Cfg.mapState_workTapes, d,
          uk_suffixCfg, if_neg hjv]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      rfl
    · rw [Cfg.mapState_output, Cfg.mapState_output]; rfl
  have init : (uk_suffixStartupTM R exit).initCfg z = (A.initCfg z).mapState Sum.inl := by
    exact uk_init_mapState A (uk_suffixStartupTM R exit) Sum.inl rfl z
  constructor
  · rw [init, uk_suffixStartupTM, MultiTapeTM.runFrom_with_q₀]
    exact (seamCompTM_run_ofCfg A exit B (Sum.inl 0) aRun rfl aCut bRun).trans final
  · intro t ht
    rw [init, uk_suffixStartupTM, MultiTapeTM.runFrom_with_q₀]
    exact seamCompTM_firstReturn_ofCfg A exit B (Sum.inl 0) (Sum.inr .done)
      aRun rfl aCut bRun rfl bCut t ht

/-- The ruler host's presented configuration has its bank first and its ruler last. -/
private theorem uk_ruler_fields {m : ℕ} {S Q : Type} {y z : List Bool} (ℓ : ℕ)
    (hz : z.length = ℓ + y.length) (q : Option Q) (c : Cfg m Bool S y) (rt : ℤ → Option Bool)
    (rp : ℤ) :
    (rulerHostCfg ℓ hz q c rt rp).inputPos.val = ℓ + c.inputPos.val ∧
      (rulerHostCfg ℓ hz q c rt rp).workTapes (Fin.last m) = rt ∧
      (rulerHostCfg ℓ hz q c rt rp).workTapePos (Fin.last m) = rp ∧
      (∀ i : Fin m, (rulerHostCfg ℓ hz q c rt rp).workTapes i.castSucc = c.workTapes i) ∧
      (rulerHostCfg ℓ hz q c rt rp).output = c.output := by
  refine ⟨by rw [rulerHostCfg_inputPos], ?_, ?_, fun i => ?_, rulerHostCfg_output _ _ _ _ _ _⟩
  · funext a
    rw [rulerHostCfg_workTapes, Fin.lastCases_last]
  · rw [rulerHostCfg_workTapePos, Fin.lastCases_last]
  · funext a
    rw [rulerHostCfg_workTapes, Fin.lastCases_castSucc]

/-- The prepared suffix seam is the embedding of the initial ruler-host presentation.

**Proof sketch.** Reconstruct the embedding from its public field equations. Its
first bank is the initial forwarding-loop encoding, its last tape is the ruler,
and all unselected tapes are blank. The encoded input head is one, so the
physical head is exactly one cell after the header and its virtual-zero tag is false. -/
private theorem uk_embed_suffix {k K n : ℕ} {P Q H : Type} {x z : List Bool}
    (exit : P) (entry : Q) (inj : Q → Bool → H) (M : MultiTapeTM k Bool (Fin (n + 1)))
    (ℓ : ℕ) (hz : z.length = ℓ + x.length) (hlen : ℓ + 1 < z.length + 2) :
    let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
    embedEmitCfg (Fin.castLEEmb (by omega : k + 3 ≤ K + (k + 3)))
      (fun _ _ => none) (fun _ => 0) []
      (rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c
        (FinTM.bufferTape (List.replicate ℓ true)) 0) =
      (uk_suffixCfg (K := K) exit M z ℓ hlen).mapState (fun _ => inj entry false) := by
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  have fields := uk_encode_init_fields entry M x
  let rt := FinTM.bufferTape (List.replicate ℓ true)
  have host := uk_ruler_fields ℓ hz (c.state.map fun q => inj q false) c rt 0
  apply embedEmitCfg_eq
  · rw [rulerHostCfg_state, fields.1, Option.map_some, Cfg.mapState_state]
    rfl
  · apply Fin.ext
    rw [host.1, Cfg.mapState_inputPos]
    change ℓ + c.inputPos.val = ℓ + 1
    rw [fields.2.1]
  · rw [List.nil_append, rulerHostCfg_output, fields.2.2.2, Cfg.mapState_output]
    rfl
  · intro j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · constructor
      · funext b
        rw [rulerHostCfg_workTapes, Fin.lastCases_last, Cfg.mapState_workTapes]
        simp only [uk_suffixCfg, Fin.coe_castLEEmb, Fin.coe_castLE, Fin.val_last,
          if_neg (by omega : k + 2 ≠ k), if_neg (by omega : k + 2 ≠ k + 1), ↓reduceIte]
      · rw [rulerHostCfg_workTapePos, Fin.lastCases_last, Cfg.mapState_workTapePos]
        rfl
    · constructor
      · funext b
        rw [rulerHostCfg_workTapes, Fin.lastCases_castSucc, Cfg.mapState_workTapes,
          uk_encode_init_tapes]
        have ha : a.val ≠ k + 2 := by omega
        simp only [uk_suffixCfg, Fin.coe_castLEEmb, Fin.coe_castLE, Fin.coe_castSucc, if_neg ha]
      · rw [rulerHostCfg_workTapePos, Fin.lastCases_castSucc, Cfg.mapState_workTapePos,
          fields.2.2.1 a]
        rfl
  · intro j hj
    have hjge : k + 3 ≤ j.val := by
      by_contra h
      apply hj
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      apply Fin.ext; rfl
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      simp only [uk_suffixCfg, if_neg (by omega : j.val ≠ k),
        if_neg (by omega : j.val ≠ k + 1), if_neg (by omega : j.val ≠ k + 2)]
    · rw [Cfg.mapState_workTapePos]
      rfl

/-- **U2-E, the code-first evaluator** [AB09, Theorem 1.9, the evaluator `U(x, α) = M_α(x)`, in
the code-first layout of `Turing.universal`]. For a `k`-tape scheme `E` there is a binary
machine `U` such that for every code `α` there is a constant `C` (depending on `α` only) with,
for every input `x`:
* whenever the machine coded by `α` halts on `x` with `output` within `t` steps, `U` halts on
  `pairEncode α x` with the same `output` within `C · (t + 1)` steps (no term in `|x|`);
* every completed output of `U` on `pairEncode α x` is a completed output of the coded machine
  on `x`.

At `k = 1` and `E := c.toK` this is `Turing.universal c`'s statement (shown in the gate's
probe); re-deriving `Turing.universal` from it is the U-1 retrofit, deferred until this
statement is filled. At `k = 2` it is the core of Theorem 1.9 at `T log T` with the
Hennie–Stearns conversion (design note §4).

**Proof sketch.** (i) *Code-first startup:* scan the doubled code and its separator, writing
one ruler cell per header cell, so the ruler is `true^ℓ` with `ℓ = 2|α| + 2`, the header length
(`Turing.universal_pair_length`); extract and canonize `α` as U2-S does, installing H2-F's
encoding of `M := E.machine α`'s initial configuration on the virtual input `x` (virtual
position `1`, physical head at `ℓ + 1`). (ii) *Ruler host:* run H2-F's machine `L` through H5's
bounded-prefix ruler host (`Turing.exists_rulerHostTM`, `Turing.RulerAt`): a block simulation
of `L` on the suffix input `x`, with at most `C_R · (ℓ + 1)` host steps per step of `L`, the same
bank and output, and exit cut. Composing with H2-F's lockstep, each step of `M` costs at most
`C_R (ℓ + 1)(50 · (|tableBitsK| + 1) + C_L)`, a constant for fixed `α`; with the startup this is
`≤ C · (t + 1)`. (iii) *Converse:* the ruler host does not halt before `L`, nor `L` before `M`
(the two cuts), so every completed output of `U` is `M`'s on `x`. -/
theorem universalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ), (E.toFinTM α).ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      ∀ output : List Bool, (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (E.toFinTM α).ComputesInTime x output t := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTMK k E
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  obtain ⟨Q, fQ, dQ, L, entry, C_L, hL⟩ := StepBlock.exists_forwardLoopTM k
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  obtain ⟨V, fV, dV, H, inj, C_R, hCR, hH⟩ := exists_rulerHostTM L
  letI : Fintype V := fV
  letI : DecidableEq V := dV
  let A := uk_suffixStartupTM R exit
  let finish : P ⊕ (Fin 4 ⊕ RewindPhase) := Sum.inr (Sum.inr .done)
  let U : FinTM Bool :=
    { k := K + (k + 3), State := (P ⊕ (Fin 4 ⊕ RewindPhase)) ⊕ V,
      tm := uk_loopTM (k := k + 1) A finish H (inj entry false) }
  refine ⟨U, ?_⟩
  intro α
  obtain ⟨T, _, hRα⟩ := hR α
  let M := E.machine α
  let ℓ := 2 * α.length + 2
  let D := 50 * ((tableBitsK M.tr).length + 1) + C_L
  let T_A := T + 1 + (2 * ℓ + 3)
  let F := C_R * (ℓ + 1)
  let C := T_A + 1 + F * D
  have hAC : T_A + 1 ≤ C := by dsimp only [C]; omega
  have hDC : F * D ≤ C := by dsimp only [C]; omega
  refine ⟨C, ?_⟩
  intro x
  let z := pairEncode α x
  have hz : z.length = ℓ + x.length := length_pairEncode α x
  have hlen : ℓ + 1 < z.length + 2 := by omega
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; omega
  obtain ⟨hrun, hcut, _, _⟩ := hRα x
  obtain ⟨aRun, aCut⟩ := uk_suffixStartup_run R exit M α x T hrun hcut
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  let rt := FinTM.bufferTape (List.replicate ℓ true)
  let d := rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c rt 0
  have hb : false = true ↔ c.inputPos.val = 0 := by
    rw [(uk_encode_init_fields entry M x).2.1]
    decide
  have host := hH ℓ hz hℓ (pairEncode_drop α x) rt 0
    (by intro p _ _; rw [zero_add]) c false hb
  have uRun := uk_loop_run (k := k + 1) A finish H (inj entry false) d
    (uk_suffixCfg (K := K) finish M z ℓ hlen) T_A aRun rfl aCut
    (uk_embed_suffix finish entry inj M ℓ hz hlen).symm
  obtain ⟨cost, hlock, hcost, _⟩ := hL (x := x) M
  constructor
  · intro output t hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff (E.toFinTM α) x output t).mp hcomp
    obtain ⟨t₀, _, _, hvbound, hr⟩ :=
      uk_loop_forward M L entry cost D hlock (fun e he => (hcost e he).2) t hhalt
    let v := ∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)
    obtain ⟨w, _, hw, ⟨b, _, hhost⟩, _, _, _, _⟩ := host v
    have uHalt : (U.tm.runFrom (U.tm.initCfg z) (T_A + 1 + w)).state = none := by
      rw [uRun w, Cfg.mapState_state, embedEmitCfg_state, hhost, rulerHostCfg_state,
        hr, StepBlock.forwardLoopCfg_state, hhalt, Option.map_none, Option.map_none,
        Option.map_none]
    have uOut : (U.tm.runFrom (U.tm.initCfg z) (T_A + 1 + w)).output = output := by
      rw [uRun w, Cfg.mapState_output, embedEmitCfg_output, List.nil_append, hhost,
        rulerHostCfg_output, hr, StepBlock.forwardLoopCfg_output]
      exact hout
    have bound : T_A + 1 + w ≤ C * (t + 1) := by
      calc
        _ ≤ C + F * v := Nat.add_le_add hAC hw
        _ ≤ C + F * (D * t) := Nat.add_le_add_left (Nat.mul_le_mul_left F hvbound) C
        _ = C + (F * D) * t := by ring
        _ ≤ C + C * t := Nat.add_le_add_left (Nat.mul_le_mul_right t hDC) C
        _ = _ := by ring
    exact ((FinTM.computesInTime_iff U z output (T_A + 1 + w)).mpr ⟨uHalt, uOut⟩).mono bound
  · intro output hcomp
    obtain ⟨u, hu⟩ := hcomp
    obtain ⟨uhalt, uout⟩ := (FinTM.computesInTime_iff U z output u).mp hu
    have hprefix := uk_loop_pre_live (k := k + 1) A finish H (inj entry false) T_A
      (by rw [aRun]; exact Option.some_ne_none finish) aCut
    have after : T_A + 1 ≤ u := by
      by_contra h
      exact hprefix u (by omega) uhalt
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le after
    rw [uRun v, Cfg.mapState_state, embedEmitCfg_state, Option.map_eq_none_iff] at uhalt
    rw [uRun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append] at uout
    have loopHalts : ∃ r, (L.runFrom c r).state = none := by
      by_contra hn
      have forever : ∀ r, (L.runFrom c r).state ≠ none := by
        intro r hr
        exact hn ⟨r, hr⟩
      obtain ⟨w, hw, _, _, cut, _, _, _⟩ := host (v + 1)
      exact cut (fun r _ => forever r) v (by omega) uhalt
    obtain ⟨r, rHalt⟩ := loopHalts
    obtain ⟨w, _, _, ⟨b, _, endpoint⟩, _, _, _, _⟩ := host r
    have wHalt : (H.runFrom d w).state = none := by
      rw [endpoint, rulerHostCfg_state, rHalt, Option.map_none]
    have loopOutput : (L.runFrom c r).output = output := by
      calc
        _ = (H.runFrom d w).output := by rw [endpoint, rulerHostCfg_output]
        _ = (H.runFrom d (max v w)).output :=
          (MultiTapeTM.runFrom_output_eq_of_halt H d (Nat.le_max_right v w) wHalt).symm
        _ = (H.runFrom d v).output :=
          MultiTapeTM.runFrom_output_eq_of_halt H d (Nat.le_max_left v w) uhalt
        _ = _ := uout
    obtain ⟨t, ht, ho⟩ := uk_loop_converse M L entry cost D hlock hcost r rHalt
    exact ⟨t, (FinTM.computesInTime_iff (E.toFinTM α) x output t).mpr
      ⟨ht, ho.trans loopOutput⟩⟩

end Turing
