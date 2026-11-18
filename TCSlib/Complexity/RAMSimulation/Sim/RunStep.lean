/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunHost
import TCSlib.Complexity.RAMSimulation.Sim.RunSource

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Instruction steps inside the finite simulation host

The host follows one phase until its first redirect, then takes one stationary dispatch step.
The run lemmas here cite the standard phase host and the forwarding tape embedding.

## Main definitions

No additional machine is constructed in this file.

## Main results

* `WordRAM.Sim.RunSetup.host_phase_run`: an unredirected phase branch inside the host.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim.RunSetup

open Turing

variable {P : XProgram} {fn : Bool} {Mw : FinTM Bool} (A : RunSetup P fn Mw)

/-- A branch that encounters no redirect before its end is the corresponding tagged phase
branch, including a last phase that halts at its endpoint.

**Proof sketch.** At an unredirected state, each slice of the host takes the tagged phase
action, by `host_fixChoice` and the published transition equation of `phaseHostTM`.
`Turing.NDTM.runWith_mapState_of_agreeOn` transfers the branch along the phase-state tag. -/
theorem host_phase_run (i : Index (P := P)) {x : List Bool}
    (d : Turing.Cfg (8 + A.extraTapes) Bool (A.PhaseState i) x) (w : List Bool)
    (hguard : ∀ u < w.length, ∀ q, ((A.phase i).runWith (w.take u) d).state = some q →
      A.redirect i q = none) :
    A.host.runWith w (d.mapState (Sigma.mk i)) =
      ((A.phase i).runWith w d).mapState (Sigma.mk i) := by
  apply NDTM.runWith_mapState_of_agreeOn (A.phase i) A.host
    ⟨Sigma.mk i, sigma_mk_injective⟩ (fun q => A.redirect i q = none)
  · intro b q hq inp work
    change A.host.tr b ⟨i, q⟩ inp work =
      ((A.phase i).tr b q inp work).mapState (Sigma.mk i)
    rw [← NDTM.fixChoice_tr (tm := A.host) (b := b), host_fixChoice,
      phaseHostTM_tr_of_red_none _ _ _ i q hq, NDTM.fixChoice_tr]
  · exact hguard

/-- After an unredirected phase branch reaches a redirected live exit, either next choice
performs the stationary dispatch. All shorter prefixes are the tagged phase prefixes. -/
theorem host_phase_dispatch (i : Index (P := P)) {x : List Bool}
    (d d' : Turing.Cfg (8 + A.extraTapes) Bool (A.PhaseState i) x)
    (w : List Bool) (hrun : (A.phase i).runWith w d = d')
    (q : A.PhaseState i) (hs : d'.state = some q) (q' : A.State)
    (hred : A.redirect i q = some q')
    (hguard : ∀ u < w.length, ∀ q, ((A.phase i).runWith (w.take u) d).state = some q →
      A.redirect i q = none) (b : Bool) :
    (∀ u ≤ w.length, A.host.runWith (w.take u) (d.mapState (Sigma.mk i)) =
      ((A.phase i).runWith (w.take u) d).mapState (Sigma.mk i)) ∧
    A.host.runWith (w ++ [b]) (d.mapState (Sigma.mk i)) = d'.mapState (fun _ => q') := by
  simpa only [host_runWith] using
    NDTM.phaseHostND_run A.phase ⟨none, A.startEntry⟩ A.redirect i d d' w hrun q hs q'
      hred hguard b

/-- The redirect selected by an ordinary RAM step enters the phase of the successor program
position and flips parity. A continuing step is inside the program, so its clamped current
position equals its actual program counter. -/
theorem resumeTag_of_step {x ρ : List Bool} {W : ℕ} {c c' : XCfg W}
    (par jump : Bool) (hstep : xstep P x ρ c = .inl c')
    (hpc : c'.pc = if jump then jumpTarget
      (P.getD (runPosition P c.pc).val (.base .reject)) else c.pc + 1) :
    A.resumeTag (runPosition P c.pc) par jump =
      ⟨some (runPosition P c'.pc, !par), (A.phases (runPosition P c'.pc)).entry⟩ := by
  have hp : (runPosition P c.pc).val = c.pc := by
    rw [runPosition_val, min_eq_left (source_pc_lt hstep).le]
  have htarget : (if jump then jumpTarget (P.getD (runPosition P c.pc).val (.base .reject))
      else (runPosition P c.pc).val + 1) = c'.pc := by
    simpa only [hp] using hpc.symm
  rw [resumeTag_eq]
  dsimp only
  rw [htarget]

/-- An instruction's fixed slice has the same endpoint and head envelope after embedding
on the first eight tapes. Every unselected tape head remains at its ambient starting point.

**Proof sketch.** Select the entry bank with `runBank`, apply the chosen phase's correctness
field, and reconstruct the ambient start by `runBank_embed`. The forwarding embedding's run,
selected-head, state, output and frame equations transfer every clause. The resulting
encoding is `encodes_embed`, and the two live exit tags are mapped by `redirect_some`. -/
theorem phase_correct (p : Fin (P.length + 1)) (par b : Bool) {x : List Bool} {W : ℕ}
    (ρ : List Bool) (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
    (d : Turing.Cfg (8 + A.extraTapes) Bool (A.PhaseState (some (p, par))) x)
    (hfetch : P.getD c.pc (.base .reject) = P.getD p.val (.base .reject))
    (hcoin : isCoin (P.getD p.val (.base .reject)) = true → ρ.getD c.rd false = b)
    (hd : d.state = some (A.phases p).entry)
    (he : Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o d) :
    ∃ (t : ℕ) (d' : Turing.Cfg (8 + A.extraTapes) Bool (A.PhaseState (some (p, par))) x),
      t ≤ (A.phases p).cost * ((T.card + 1) * (W + 1) + W ^ 2 + x.length + 1) ∧
      (∀ u < t, ∀ q, (((A.phase (some (p, par))).fixChoice b).runFrom d u).state = some q →
        A.redirect (some (p, par)) q = none) ∧
      (∀ u ≤ t, ∀ j : Fin 8,
        |(((A.phase (some (p, par))).fixChoice b).runFrom d u).workTapePos
            ((Fin.castAddEmb A.extraTapes) j) - o j| ≤
          ((A.phases p).cost * ((T.card + 1) * (W + 1) + (Nat.bits x.length).length + 1) : ℕ)) ∧
      (∀ u ≤ t, ∀ j : Fin (8 + A.extraTapes), j ∉ Set.range (Fin.castAddEmb A.extraTapes) →
        (((A.phase (some (p, par))).fixChoice b).runFrom d u).workTapePos j = d.workTapePos j) ∧
      ((A.phase (some (p, par))).fixChoice b).runFrom d t = d' ∧
      match xstep P x ρ c with
      | .inl c' => Encodes A.width fn (T ∪ (P.getD p.val (.base .reject)).touches c.mem) c'
          (Fin.castAddEmb A.extraTapes) o d' ∧
          ∃ q jump, d'.state = some q ∧
            A.redirect (some (p, par)) q = some (A.resumeTag p par jump) ∧
            c'.pc = if jump then jumpTarget (P.getD p.val (.base .reject)) else c.pc + 1
      | .inr v => d'.state = none ∧ d'.output = (if fn then c.out else [v]) := by
  let σ : Fin 8 ↪ Fin (8 + A.extraTapes) := Fin.castAddEmb A.extraTapes
  let R := A.phases p
  let bank := runBank σ R.entry d
  have hbank : Encodes A.width fn T c (Function.Embedding.refl _) o bank :=
    (runBank_encodes A.width fn T c σ o R.entry d).mp he
  obtain ⟨t, e, ht, hguard, henv, hrun, hpost⟩ :=
    R.correct b P ρ T c o bank hfetch hcoin (runBank_state σ R.entry d) hbank
  have hstart : embedEmitCfg σ d.workTapes d.workTapePos [] bank = d :=
    runBank_embed σ R.entry d hd
  have hr : ∀ u, ((A.phase (some (p, par))).fixChoice b).runFrom d u =
      embedEmitCfg σ d.workTapes d.workTapePos [] ((R.machine.fixChoice b).runFrom bank u) := by
    intro u
    rw [phase_some, runEmbedND_fixChoice]
    have h := embedEmitTM_runFrom σ (R.machine.fixChoice b) d.workTapes d.workTapePos [] bank u
    rwa [hstart] at h
  refine ⟨t, embedEmitCfg σ d.workTapes d.workTapePos [] e, ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu q hq
    rw [hr u, embedEmitCfg_state] at hq
    rw [redirect_some, hguard u hu q hq, Option.map_none]
  · intro u hu j
    rw [hr u, embedEmitCfg_selected_pos]
    exact henv u hu j
  · intro u hu j hj
    rw [hr u]
    exact (embedEmitCfg_unselected σ _ _ _ _ j hj).2
  · rw [hr t, hrun]
  · cases hs : xstep P x ρ c with
    | inl c' =>
      rw [hs] at hpost
      obtain ⟨he', q, jump, hq, hred, hp⟩ := hpost
      refine ⟨(encodes_embed A.width fn _ c' σ o e d.workTapes d.workTapePos).mp he',
        q, jump, ?_, ?_, hp⟩
      · rw [embedEmitCfg_state]
        exact hq
      · rw [redirect_some, hred, Option.map_some]
    | inr v =>
      rw [hs] at hpost
      rw [embedEmitCfg_state, embedEmitCfg_output, List.nil_append]
      exact hpost

/-- An ambient instruction phase follows the fixed slice determined by its entry choice on
every prefix. Non-coin phases impose no condition on the branch's first bit.

**Proof sketch.** Reconstruct the ambient configuration from its selected entry bank. Transfer
the branch with `runEmbedND_runWith`, apply `RunPhase.branch_prefix_choice` on the eight source
tapes, and transfer the deterministic run back with `embedEmitTM_runFrom`. -/
theorem phase_branch_prefix (p : Fin (P.length + 1)) (par b : Bool) {x : List Bool}
    (d : Turing.Cfg (8 + A.extraTapes) Bool (A.PhaseState (some (p, par))) x)
    (hd : d.state = some (A.phases p).entry) (w : List Bool)
    (hb : isCoin (P.getD p.val (.base .reject)) = true → w ≠ [] → w.headD false = b)
    (u : ℕ) (hu : u ≤ w.length) :
    (A.phase (some (p, par))).runWith (w.take u) d =
      ((A.phase (some (p, par))).fixChoice b).runFrom d u := by
  let σ : Fin 8 ↪ Fin (8 + A.extraTapes) := Fin.castAddEmb A.extraTapes
  let R := A.phases p
  let bank := runBank σ R.entry d
  have hstart : embedEmitCfg σ d.workTapes d.workTapePos [] bank = d :=
    runBank_embed σ R.entry d hd
  have hleft := runEmbedND_runWith σ R.machine d.workTapes d.workTapePos [] (w.take u) bank
  have hright := embedEmitTM_runFrom σ (R.machine.fixChoice b) d.workTapes d.workTapePos [] bank u
  rw [hstart] at hleft hright
  rw [R.branch_prefix_choice b w bank hb u hu] at hleft
  rw [phase_some, runEmbedND_fixChoice]
  exact hleft.trans hright.symm

/-- If the fixed instruction slice reaches no redirect before the end of a choice word,
every host prefix is that slice with its state tagged by the instruction position/parity.

**Proof sketch.** At each prefix, `phase_branch_prefix` identifies the phase run with the
fixed slice. The slice's cut therefore supplies the guard for `host_phase_run`; nested takes
reduce to the original word's prefixes. This also works when the slice halts at its end. -/
theorem host_slice_prefix (p : Fin (P.length + 1)) (par b : Bool) {x : List Bool}
    (d : Turing.Cfg (8 + A.extraTapes) Bool (A.PhaseState (some (p, par))) x)
    (hd : d.state = some (A.phases p).entry) (w : List Bool)
    (hb : isCoin (P.getD p.val (.base .reject)) = true → w ≠ [] → w.headD false = b)
    (hcut : ∀ v < w.length, ∀ q,
      (((A.phase (some (p, par))).fixChoice b).runFrom d v).state = some q →
        A.redirect (some (p, par)) q = none) :
    ∀ u ≤ w.length, A.host.runWith (w.take u) (d.mapState (Sigma.mk (some (p, par)))) =
      (((A.phase (some (p, par))).fixChoice b).runFrom d u).mapState
        (Sigma.mk (some (p, par))) := by
  intro u hu
  have hguard : ∀ v < (w.take u).length, ∀ q,
      ((A.phase (some (p, par))).runWith ((w.take u).take v) d).state = some q →
        A.redirect (some (p, par)) q = none := by
    intro v hv q hq
    have hvu : v < u := by rw [List.length_take_of_le hu] at hv; exact hv
    rw [List.take_take, Nat.min_eq_left hvu.le,
      phase_branch_prefix A p par b d hd w hb v (hvu.le.trans hu)] at hq
    exact hcut v (hvu.trans_le hu) q hq
  rw [host_phase_run A (some (p, par)) d (w.take u) hguard,
    phase_branch_prefix A p par b d hd w hb u hu]

/-- **The local entry of a live host start.** A host configuration at the entry of the phase for
the instruction at `c.pc` is the local phase configuration at that entry, retagged; the local
configuration carries the same encoding. Shared by `host_ordinary` and `host_verdict`.

**Proof sketch.** Rename every state to the phase's entry: the state reader and `hd` give the
local entry, `encodes_mapState` transports the encoding, and `runEntry_reconstruct` retags it
back to `d`; renaming keeps the heads. -/
theorem host_local {x : List Bool} {W : ℕ} (par : Bool) (T : Finset ℤ) (c : XCfg W)
    (o : Fin 8 → ℤ) (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x)
    (hd : d.state = some ⟨some (runPosition P c.pc, par),
      (A.phases (runPosition P c.pc)).entry⟩)
    (he : Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o d) :
    ∃ locald : Turing.Cfg (8 + A.extraTapes) Bool (A.phases (runPosition P c.pc)).State x,
      locald.state = some (A.phases (runPosition P c.pc)).entry ∧
      Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o locald ∧
      locald.mapState (Sigma.mk (some (runPosition P c.pc, par))) = d ∧
      locald.workTapePos = d.workTapePos := by
  let R := A.phases (runPosition P c.pc)
  refine ⟨d.mapState (fun _ => R.entry), ?_, ?_, ?_, ?_⟩
  · rw [Cfg.mapState_state, hd]; rfl
  · exact (encodes_mapState A.width fn T c (Fin.castAddEmb A.extraTapes) o d
      (fun _ => R.entry)).mp he
  · exact runEntry_reconstruct R.entry
      (fun q : R.State => (⟨some (runPosition P c.pc, par), q⟩ : A.State)) d hd
  · funext j
    rw [Cfg.mapState_workTapePos]

/-- A word of each positive length headed by `b`: its nonempty values start with `b`. Shared
by `host_ordinary` and `host_verdict`. -/
theorem words_headD {b : Bool} (words : ℕ → List Bool) (hlen : ∀ n, (words n).length = n)
    (hhead : ∀ n, 0 < n → (words n).headD false = b) (t : ℕ) (hne : words t ≠ []) :
    (words t).headD false = b := by
  apply hhead t
  rw [← hlen t]
  exact List.length_pos_iff.mpr hne

/-- The ambient head envelope of a phase prefix started at the local entry: a selected tape stays
within the phase's envelope about its encoded origin, and an unselected tape is where the frame
clause leaves it. Shared by `host_ordinary` and `host_verdict`.

**Proof sketch.** Split on whether the tape is selected. A selected head of `d` sits at its
origin by the encoding, which the envelope bounds; an unselected one equals the local start,
whose heads are `d`'s. -/
theorem host_envelope {x : List Bool} {W : ℕ} {S : Type} (T : Finset ℤ) (c : XCfg W)
    (o : Fin 8 → ℤ) (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x)
    (he : Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o d)
    (locald e : Turing.Cfg (8 + A.extraTapes) Bool S x)
    (hpos : locald.workTapePos = d.workTapePos) (B : ℕ)
    (henv : ∀ r : Fin 8, |e.workTapePos (Fin.castAddEmb A.extraTapes r) - o r| ≤ (B : ℤ))
    (hframe : ∀ j : Fin (8 + A.extraTapes), j ∉ Set.range (Fin.castAddEmb A.extraTapes) →
      e.workTapePos j = locald.workTapePos j)
    (j : Fin (8 + A.extraTapes)) :
    |e.workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
  by_cases hj : j ∈ Set.range (Fin.castAddEmb A.extraTapes)
  · obtain ⟨r, rfl⟩ := hj
    rw [((encodes_iff A.width fn T c (Fin.castAddEmb A.extraTapes) o d).mp he).1 r]
    exact henv r
  · rw [hframe j hj, hpos, sub_self, abs_zero]
    exact Nat.cast_nonneg _

/-- A continuing RAM instruction is simulated by one phase word and one dispatch choice.
The endpoint encodes its successor at the opposite parity, every head is restored, and every
prefix stays within the instruction's envelope around its starting heads.

**Proof sketch.** Retag the live host start to the local entry and apply `phase_correct`.
`phase_branch_prefix` transfers the supplied word to that fixed slice. The standard host
dispatch lemma supplies the tagged prefixes and the stationary final dispatch; `resumeTag_of_step`
identifies its destination with the successor RAM counter. The endpoint encoding fixes each
selected head at its original origin, while the frame clause fixes every extra head. These
same two cases bound each prefix, including the dispatch endpoint. -/
theorem host_ordinary {x ρ : List Bool} {W : ℕ} (par b : Bool)
    (T : Finset ℤ) (c c' : XCfg W) (o : Fin 8 → ℤ)
    (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x)
    (hd : d.state = some ⟨some (runPosition P c.pc, par),
      (A.phases (runPosition P c.pc)).entry⟩)
    (he : Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o d)
    (hstep : xstep P x ρ c = .inl c')
    (hcoin : isCoin (P.getD c.pc (.base .reject)) = true → ρ.getD c.rd false = b)
    (words : ℕ → List Bool) (hlen : ∀ n, (words n).length = n)
    (hhead : ∀ n, 0 < n → (words n).headD false = b) (dispatch : ℕ → Bool) :
    ∃ (t : ℕ) (d' : Turing.Cfg (8 + A.extraTapes) Bool A.State x),
      t ≤ (A.phases (runPosition P c.pc)).cost *
        ((T.card + 1) * (W + 1) + W ^ 2 + x.length + 1) ∧
      A.host.runWith (words t ++ [dispatch t]) d = d' ∧
      d'.state = some ⟨some (runPosition P c'.pc, !par),
        (A.phases (runPosition P c'.pc)).entry⟩ ∧
      Encodes A.width fn (T ∪ (P.getD c.pc (.base .reject)).touches c.mem) c'
        (Fin.castAddEmb A.extraTapes) o d' ∧
      d'.workTapePos = d.workTapePos ∧
      ∀ u ≤ t + 1, ∀ j,
        |(A.host.runWith ((words t ++ [dispatch t]).take u) d).workTapePos j - d.workTapePos j| ≤
          ((A.phases (runPosition P c.pc)).cost *
            ((T.card + 1) * (W + 1) + (Nat.bits x.length).length + 1) : ℕ) := by
  let p := runPosition P c.pc
  let i : Index (P := P) := some (p, par)
  let σ : Fin 8 ↪ Fin (8 + A.extraTapes) := Fin.castAddEmb A.extraTapes
  let R := A.phases p
  have hfetch : P.getD p.val (.base .reject) = P.getD c.pc (.base .reject) :=
    runPosition_fetch P c.pc
  obtain ⟨locald, hd₀, he₀, hstart, hpos⟩ := A.host_local par T c o d hd he
  have hc : isCoin (P.getD p.val (.base .reject)) = true → ρ.getD c.rd false = b := by
    rw [hfetch]
    exact hcoin
  obtain ⟨t, e, ht, hcut, henv, hframe, hrun, hpost⟩ :=
    A.phase_correct p par b ρ T c o locald hfetch.symm hc hd₀ he₀
  rw [hstep] at hpost
  obtain ⟨he', q, jump, hq, hred, hpc⟩ := hpost
  let w := words t
  have hw : w.length = t := hlen t
  have hb : isCoin (P.getD p.val (.base .reject)) = true → w ≠ [] → w.headD false = b :=
    fun _ => words_headD words hlen hhead t
  have hrw := A.phase_branch_prefix p par b locald hd₀ w hb w.length le_rfl
  rw [List.take_length, hw, hrun] at hrw
  have hg : ∀ u < w.length, ∀ q,
      ((A.phase i).runWith (w.take u) locald).state = some q → A.redirect i q = none := by
    intro u hu q hqu
    rw [A.phase_branch_prefix p par b locald hd₀ w hb u hu.le] at hqu
    exact hcut u (by omega) q hqu
  obtain ⟨hpre, hfinal⟩ := A.host_phase_dispatch i locald e w hrw q hq
    (A.resumeTag p par jump) hred hg (dispatch t)
  rw [hstart] at hpre hfinal
  have hdest := A.resumeTag_of_step par jump hstep hpc
  let post := e.mapState (fun _ => A.resumeTag p par jump)
  have hheads : post.workTapePos = d.workTapePos := by
    funext j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨r, rfl⟩ := hj
      have heh := ((encodes_iff A.width fn _ c' σ o e).mp he').1 r
      have hdh := ((encodes_iff A.width fn T c σ o d).mp he).1 r
      rw [Cfg.mapState_workTapePos, heh, hdh]
    · have hf := hframe t le_rfl j hj
      rw [hrun] at hf
      rw [Cfg.mapState_workTapePos, hf, hpos]
  refine ⟨t, post, ht, hfinal, ?_, ?_, hheads, ?_⟩
  · rw [Cfg.mapState_state, hq, Option.map_some, hdest]
  · simpa only [hfetch] using
      (encodes_mapState A.width fn _ c' σ o e (fun _ => A.resumeTag p par jump)).mp he'
  · intro u hu j
    by_cases hut : u ≤ t
    · have huw : u ≤ w.length := by omega
      rw [List.take_append_of_le_length huw, hpre u huw,
        A.phase_branch_prefix p par b locald hd₀ w hb u huw, Cfg.mapState_workTapePos]
      exact A.host_envelope T c o d he locald _ hpos _ (henv u hut) (hframe u hut) j
    · have hue : u = t + 1 := by omega
      have hwle : (w ++ [dispatch t]).length ≤ u := by
        rw [List.length_append, hw, List.length_singleton, hue]
      rw [List.take_of_length_le hwle, hfinal, hheads, sub_self, abs_zero]
      exact Nat.cast_nonneg _

/-- A verdict instruction halts the host with the requested verdict/function output, with no
dispatch after it. Every prefix satisfies the same fixed-origin phase envelope.

**Proof sketch.** Apply `phase_correct` to the local entry after replacing the host tag.
A verdict is not a coin, so the entry-bit premise is vacuous. `host_slice_prefix` transfers
the entire word and all its prefixes; the final phase state is already halted. State and
output renaming equations preserve that endpoint, and the selected/frame cases give the
ambient head bound exactly as in the ordinary-step interface. -/
theorem host_verdict {x ρ : List Bool} {W : ℕ} (par b : Bool)
    (T : Finset ℤ) (c : XCfg W) (v : Bool) (o : Fin 8 → ℤ)
    (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x)
    (hd : d.state = some ⟨some (runPosition P c.pc, par),
      (A.phases (runPosition P c.pc)).entry⟩)
    (he : Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o d)
    (hstep : xstep P x ρ c = .inr v)
    (words : ℕ → List Bool) (hlen : ∀ n, (words n).length = n)
    (hhead : ∀ n, 0 < n → (words n).headD false = b) :
    ∃ (t : ℕ) (d' : Turing.Cfg (8 + A.extraTapes) Bool A.State x),
      t ≤ (A.phases (runPosition P c.pc)).cost *
        ((T.card + 1) * (W + 1) + W ^ 2 + x.length + 1) ∧
      A.host.runWith (words t) d = d' ∧ d'.state = none ∧
      d'.output = (if fn then c.out else [v]) ∧
      ∀ u ≤ t, ∀ j,
        |(A.host.runWith ((words t).take u) d).workTapePos j - d.workTapePos j| ≤
          ((A.phases (runPosition P c.pc)).cost *
            ((T.card + 1) * (W + 1) + (Nat.bits x.length).length + 1) : ℕ) := by
  let p := runPosition P c.pc
  let i : Index (P := P) := some (p, par)
  let σ : Fin 8 ↪ Fin (8 + A.extraTapes) := Fin.castAddEmb A.extraTapes
  let R := A.phases p
  have hfetch : P.getD p.val (.base .reject) = P.getD c.pc (.base .reject) :=
    runPosition_fetch P c.pc
  obtain ⟨locald, hd₀, he₀, hstart, hpos⟩ := A.host_local par T c o d hd he
  have hc : isCoin (P.getD p.val (.base .reject)) = true → ρ.getD c.rd false = b := by
    intro h
    rw [hfetch, source_verdict_not_coin hstep] at h
    cases h
  obtain ⟨t, e, ht, hcut, henv, hframe, hrun, hpost⟩ :=
    A.phase_correct p par b ρ T c o locald hfetch.symm hc hd₀ he₀
  rw [hstep] at hpost
  let w := words t
  have hw : w.length = t := hlen t
  have hb : isCoin (P.getD p.val (.base .reject)) = true → w ≠ [] → w.headD false = b :=
    fun _ => words_headD words hlen hhead t
  have hc' : ∀ u < w.length, ∀ q,
      (((A.phase (some (p, par))).fixChoice b).runFrom locald u).state = some q →
        A.redirect (some (p, par)) q = none := by
    intro u hu q hq
    exact hcut u (by omega) q hq
  have hpre := A.host_slice_prefix p par b locald hd₀ w hb hc'
  rw [hstart] at hpre
  have hfinal := hpre w.length le_rfl
  rw [List.take_length, hw, hrun] at hfinal
  refine ⟨t, e.mapState (Sigma.mk i), ht, hfinal, ?_, ?_, ?_⟩
  · rw [Cfg.mapState_state, hpost.1, Option.map_none]
  · rw [Cfg.mapState_output]
    exact hpost.2
  · intro u hu j
    have huw : u ≤ w.length := by omega
    rw [hpre u huw, Cfg.mapState_workTapePos]
    exact A.host_envelope T c o d he locald _ hpos _ (henv u hu) (hframe u hu) j

end WordRAM.Sim.RunSetup
