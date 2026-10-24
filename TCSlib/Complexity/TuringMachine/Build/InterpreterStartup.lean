/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.InputWindow
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.StepBlock

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The interpreter's startup kit

The pieces from which a universal machine's startup is composed, on a timed paired input
`⟨⟨bits t, α⟩, x⟩`: the two header projections and their silent capture, the window `x.take t`
of the suffix, the install call as a released phase, the redistribution of an installed
serialization into the step block's table and summary tapes, the seam step between two
verified phases, and the initial configuration of a fresh capture. The interpreter core of
`TCSlib.Complexity.TuringMachine.NDCodeSimulator` is assembled from them.

## Main results

* `Turing.seamCompTM_step` — one seam step between two verified phases.
* `Turing.prefixCanon_pairExtract_halt`, `Turing.headerCapture_run` — the header projections,
  and their capture with a first live return.
* `Turing.embedSilentRetTM_firstReturn`, `Turing.embedSilentCfg_initCfg` — a silent capture's
  first return, and a fresh capture's initial configuration.
* `Turing.exists_windowCall` — the suffix window.
* `Turing.installCall_releasePhase` — the install call as a released phase.
* `Turing.exists_layoutCall` — the layout of an installed serialization.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1: the universal machine.)
-/

namespace Turing

/-- **One seam step.** Composing a verified segment with a verified next phase through the seam
`Turing.seamCompTM`: the endpoint, its control state, and the inherited first return of the
phase's exit, in one step. [AB09, §1.4.1]

**Proof sketch.** The general-configuration seam run and its inherited first-return cut,
with the endpoint state projected through the state renaming. -/
theorem seamCompTM_step {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] {x : List Bool}
    (A : MultiTapeTM k Bool S₁) (exit₁ : S₁) (B : MultiTapeTM k Bool S₂)
    (entry₂ exit₂ : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₂ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : A.runFrom c₀ T₁ = c₁) (hx₁ : c₁.state = some exit₁)
    (hcut₁ : ∀ t < T₁, (A.runFrom c₀ t).state ≠ some exit₁)
    (h₂ : B.runFrom (c₁.mapState fun _ => entry₂) T₂ = c₂)
    (hx₂ : c₂.state = some exit₂)
    (hcut₂ : ∀ t < T₂,
      (B.runFrom (c₁.mapState fun _ => entry₂) t).state ≠ some exit₂) :
    (seamCompTM A exit₁ B entry₂).runFrom (c₀.mapState Sum.inl) (T₁ + 1 + T₂) =
        c₂.mapState (Sum.inr : S₂ → S₁ ⊕ S₂) ∧
      (c₂.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).state = some (Sum.inr exit₂) ∧
      ∀ t < T₁ + 1 + T₂,
        ((seamCompTM A exit₁ B entry₂).runFrom (c₀.mapState Sum.inl) t).state ≠
          some (Sum.inr exit₂) := by
  refine ⟨seamCompTM_run_ofCfg A exit₁ B entry₂ h₁ hx₁ hcut₁ h₂, ?_,
    seamCompTM_firstReturn_ofCfg A exit₁ B entry₂ exit₂ h₁ hx₁ hcut₁ h₂ hx₂
      hcut₂⟩
  rw [Cfg.mapState_state, hx₂, Option.map_some]

/-- **The header projections.** On a timed paired input `⟨⟨bits t, α⟩, x⟩`, either header
projection halts at the suffix with its selected component. The common time is
`16 |bits t| + 8 |α| + 25`; in particular it is independent of the suffix. [AB09, §1.4.1]

**Proof sketch.** Apply the published prefix contract to the first or second pair extractor.
Decode the inner pair with its round-trip lemma and expand only its published length formula. -/
theorem prefixCanon_pairExtract_halt (first : Bool) (α x : List Bool) (t : ℕ) :
    let F := if first then FinTM.pairExtractTM true false else FinTM.pairExtractTM false true
    let M := prefixCanonTM F
    let z := pairEncode (pairEncode (Nat.bits t) α) x
    let d := M.tm.runFrom (M.tm.initCfg z)
      (16 * (Nat.bits t).length + 8 * α.length + 25)
    d.state = none ∧ d.output = (if first then Nat.bits t else α) ∧
      d.inputPos.val = 4 * (Nat.bits t).length + 2 * α.length + 7 := by
  have duration : 3 * (pairEncode (Nat.bits t) α).length + 4 +
      5 * ((pairEncode (Nat.bits t) α).length + 1) =
      16 * (Nat.bits t).length + 8 * α.length + 25 := by
    rw [length_pairEncode]
    omega
  have position : 2 * (pairEncode (Nat.bits t) α).length + 3 =
      4 * (Nat.bits t).length + 2 * α.length + 7 := by
    rw [length_pairEncode]
    omega
  cases first
  · have h := prefixCanon_complete _ _ _ FinTM.pairExtractTM_snd
      (pairEncode (Nat.bits t) α) x
    simpa only [duration, position, pairDecode_pairEncode, Option.map_some,
      Option.getD_some, Bool.false_eq_true, ↓reduceIte] using h
  · have h := prefixCanon_complete _ _ _ FinTM.pairExtractTM_fst
      (pairEncode (Nat.bits t) α) x
    simpa only [duration, position, pairDecode_pairEncode, Option.map_some,
      Option.getD_some, ↓reduceIte] using h

/-- **A silent capture's first return.** A bounded native-input computation can be silently
captured with a first live return. The completed transport contains the source's final output,
even if it halted before the bound. [AB09, §1.4.1]

**Proof sketch.** Choose the first halt using the public first-halt lemma. The returning
embedding reaches its live anchor there, with exactly the configuration at the supplied bound. -/
theorem embedSilentRetTM_firstReturn {k : ℕ} (M : FinTM Bool) (x : List Bool)
    (ι : Fin M.k ↪ Fin k) (cap : Fin k) (hcap : cap ∉ Set.range ι)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (out : List Bool)
    (T : ℕ) (halt : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    ∃ u ≤ T,
      (embedSilentRetTM ι cap M.tm).runFrom
          ((embedSilentCfg ι cap tapes heads [] out (M.tm.initCfg x)).mapState Sum.inl) u =
        { embedSilentCfg ι cap tapes heads [] out (M.tm.runFrom (M.tm.initCfg x) T) with
          state := some (Sum.inr ()) } ∧
      ∀ v < u,
        ((embedSilentRetTM ι cap M.tm).runFrom
          ((embedSilentCfg ι cap tapes heads [] out (M.tm.initCfg x)).mapState Sum.inl)
          v).state ≠ some (Sum.inr ()) := by
  obtain ⟨u, hu, before, same⟩ := M.tm.exists_first_halt (M.tm.initCfg x) halt
  have live : (M.tm.initCfg x).state ≠ none := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  obtain ⟨_, result, cut⟩ := embedSilentRetTM_run ι cap hcap M.tm tapes heads [] out
    (M.tm.initCfg x) u live before (by rw [same]; exact halt)
  exact ⟨u, hu, by simpa only [same] using result, cut⟩

/-- **A fresh capture's start.** Silently capturing a fresh run starts from the initial
configuration of the capture host: blank host tapes and zero work heads. [AB09, §1.4.1]

**Proof sketch.** Partition host tapes into selected tapes, the capture tape, and the frame.
The selected tapes inherit the blank initial configuration; the empty captured output makes
its tape blank; the frame is blank by construction. Compare all configuration fields. -/
theorem embedSilentCfg_initCfg {m n : ℕ} {S : Type} (M : MultiTapeTM m Bool S)
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

/-- **The header capture.** A header projection has a silent first live return, with its
selected word on the capture tape and the native head at the suffix. Unselected tapes other than
the capture retain their contents and heads; no description of the projection's final scratch
bank is needed. [AB09, §1.4.1]

**Proof sketch.** Use the header's bounded halt and the returning capture lemma. Project the
capture, input-position, output and unselected-tape equations at that return. -/
theorem headerCapture_run (first : Bool) (K : ℕ) (α x : List Bool) (t : ℕ)
    (ι : Fin (prefixCanonTM
      (if first then FinTM.pairExtractTM true false else FinTM.pairExtractTM false true)).k ↪
        Fin K)
    (cap : Fin K) (hcap : cap ∉ Set.range ι)
    (tapes : Fin K → ℤ → Option Bool) (heads : Fin K → ℤ) (out : List Bool) :
    let M := prefixCanonTM
      (if first then FinTM.pairExtractTM true false else FinTM.pairExtractTM false true)
    let z := pairEncode (pairEncode (Nat.bits t) α) x
    let start := (embedSilentCfg ι cap tapes heads [] out (M.tm.initCfg z)).mapState Sum.inl
    ∃ T ≤ 16 * (Nat.bits t).length + 8 * α.length + 25,
      let e := (embedSilentRetTM ι cap M.tm).runFrom start T
      e.state = some (Sum.inr ()) ∧
      e.inputPos.val = 4 * (Nat.bits t).length + 2 * α.length + 7 ∧
      e.workTapes cap = FinTM.bufferTape (if first then Nat.bits t else α) ∧
      e.workTapePos cap = ((if first then Nat.bits t else α).length : ℤ) ∧
      e.output = out ∧
      (∀ j : Fin K, j ∉ Set.range ι → j ≠ cap →
        e.workTapes j = tapes j ∧ e.workTapePos j = heads j) ∧
      ∀ u < T, ((embedSilentRetTM ι cap M.tm).runFrom start u).state ≠ some (Sum.inr ()) := by
  dsimp only
  let M := prefixCanonTM
    (if first then FinTM.pairExtractTM true false else FinTM.pairExtractTM false true)
  let z := pairEncode (pairEncode (Nat.bits t) α) x
  obtain ⟨halt, word, pos⟩ := prefixCanon_pairExtract_halt first α x t
  obtain ⟨T, bound, run, cut⟩ := embedSilentRetTM_firstReturn M z ι cap hcap tapes heads out
    (16 * (Nat.bits t).length + 8 * α.length + 25) halt
  refine ⟨T, bound, ?_⟩
  rw [run]
  obtain ⟨hword, hhead⟩ := embedSilentCfg_cap ι cap hcap tapes heads [] out
    (M.tm.runFrom (M.tm.initCfg z) (16 * (Nat.bits t).length + 8 * α.length + 25))
  rw [List.nil_append, word] at hword hhead
  refine ⟨rfl, ?_, hword, hhead, ?_, ?_, cut⟩
  · simpa only [embedSilentCfg_inputPos] using pos
  · rw [embedSilentCfg_output]
  · intro j hj hjc
    exact embedSilentCfg_unselected ι cap tapes heads [] out _ j hj hjc

/-- Removing the doubled header and its separator from a paired input leaves its suffix.

**Proof sketch.** Express the pair as the empty-suffix header appended to the suffix. The
published length formula gives exactly the number of symbols to drop. -/
private theorem is_input_suffix (u x : List Bool) :
    (pairEncode u x).drop (2 * u.length + 2) = x := by
  have split : pairEncode u x = pairEncode u [] ++ x := by
    rw [pairEncode_eq, pairEncode_eq, List.append_nil]
  have width : (pairEncode u []).length = 2 * u.length + 2 := by
    rw [length_pairEncode, List.length_nil, Nat.add_zero]
  rw [split, ← width, List.drop_left]

/-- **The window call.** At the end of the header passes the copier produces exactly the
bounded suffix window `x.take t` on an initially blank tape. Tapes other than the window and
counter are framed, as are their heads, and the cost has no dependence on the uncopied suffix.
[AB09, §1.4.1]

**Proof sketch.** Identify the suffix by dropping the encoded header, and read the binary
counter through its published value equation. Project the copier's two tape updates; the
blank destination outside the copied interval agrees with the window buffer's blank cells. -/
theorem exists_windowCall (K : ℕ) (j dst : Fin K) (hjd : j ≠ dst) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (W : MultiTapeTM K Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ (α x : List Bool) (t : ℕ)
        (d : Cfg K Bool Q (pairEncode (pairEncode (Nat.bits t) α) x)),
        d.state = some entry →
        d.inputPos.val = 4 * (Nat.bits t).length + 2 * α.length + 7 →
        (∀ q : ℤ, -1 ≤ q → q ≤ ((Nat.bits t).length : ℤ) →
          d.workTapes j (d.workTapePos j + q) = FinTM.bufferTape (Nat.bits t) q) →
        d.workTapes dst = (fun _ => none) → d.workTapePos dst = 0 →
        ∃ T ≤ C * (min t x.length + 1) + 2 * (Nat.bits t).length,
          (W.runFrom d T).state = some done ∧
          (W.runFrom d T).inputPos.val =
            4 * (Nat.bits t).length + 2 * α.length + 7 + (x.take t).length ∧
          (W.runFrom d T).workTapes dst = FinTM.bufferTape (x.take t) ∧
          (W.runFrom d T).workTapePos dst = ((x.take t).length : ℤ) ∧
          (W.runFrom d T).workTapePos j = d.workTapePos j ∧
          (∀ i : Fin K, i ≠ j → i ≠ dst →
            (W.runFrom d T).workTapes i = d.workTapes i ∧
            (W.runFrom d T).workTapePos i = d.workTapePos i) ∧
          (W.runFrom d T).output = d.output ∧
          ∀ u < T, (W.runFrom d u).state ≠ some done := by
  obtain ⟨Q, hQ, hQ', W, entry, done, C, copy⟩ := exists_inputWindowCopyTM K j dst hjd
  refine ⟨Q, hQ, hQ', W, entry, done, C, ?_⟩
  intro α x t d hd hp hw hblank hzero
  have position : d.inputPos.val = 2 * (pairEncode (Nat.bits t) α).length + 2 + 1 := by
    rw [hp, length_pairEncode]
    omega
  have value : Nat.ofDigits 2 ((Nat.bits t).map Bool.toNat) = t :=
    (counterValue_eq _).symm.trans (counterValue_bits t)
  obtain ⟨T, bound, w', _, hstate, hin, htapes, hheads, hout, hcut⟩ :=
    copy d (2 * (pairEncode (Nat.bits t) α).length + 2) (Nat.bits t) hd position hw
  simp only [is_input_suffix, value] at bound hin htapes hheads
  refine ⟨T, by simpa only [List.length_take] using bound, hstate, ?_, ?_, ?_, ?_, ?_, hout,
    hcut⟩
  · rw [length_pairEncode (Nat.bits t) α] at hin
    omega
  · rw [htapes, Function.update_of_ne hjd.symm, Function.update_self]
    funext q
    simp only [hzero, hblank, zero_add, sub_zero]
    by_cases inside : 0 ≤ q ∧ q < ((x.take t).length : ℤ)
    · rw [if_pos inside]
    · rw [if_neg inside, FinTM.bufferTape_eq]
      by_cases nonneg : 0 ≤ q
      · rw [if_pos nonneg, List.getElem?_eq_none (by omega)]
      · rw [if_neg nonneg]
  · rw [hheads, Function.update_self, hzero, zero_add]
  · rw [hheads, Function.update_of_ne hjd]
  · intro i hij hid
    exact ⟨by rw [htapes, Function.update_of_ne hij, Function.update_of_ne hid],
      by rw [hheads, Function.update_of_ne hid]⟩

/-- **The install call as a released phase.** The install call, embedded silently on selected
host tapes and wrapped in the release adapter, so that its first re-arrival at the installed seam
is a positive event even when the call's entry and exit controls coincide. The embedded run
carries one clean seam to the other; unselected tapes hold their frame throughout.
[AB09, §1.4.1]

**Proof sketch.** The silent embedding transports the call's run between the transported
seams; the release adapter's positive lockstep makes the first arrival at the exit control
strictly positive, and the call's interior cut excludes it earlier. -/
theorem installCall_releasePhase {K : ℕ} (CI : FinTM Bool) (entryI doneI : CI.State)
    (ι : Fin CI.k ↪ Fin K) (cap : Fin K) (hcap : cap ∉ Set.range ι) {z : List Bool}
    (tapes : Fin K → ℤ → Option Bool) (heads : Fin K → ℤ) (α w' : List Bool) (T : ℕ)
    (hT : 0 < T)
    (hrun : CI.tm.runFrom (Cfg.ofWords (input := z) entryI (stateWord CI.k α)) T =
      Cfg.ofWords doneI (stateWord CI.k w'))
    (hcut : ∀ u, 0 < u → u < T →
      (CI.tm.runFrom (Cfg.ofWords (input := z) entryI (stateWord CI.k α)) u).state ≠
        some doneI) :
    (seamReleaseTM (embedSilentTM ι cap CI.tm) entryI).runFrom
        ((embedSilentCfg ι cap tapes heads [] []
          (Cfg.ofWords (input := z) entryI (stateWord CI.k α))).mapState
            (fun _ => Sum.inl ())) T =
      (embedSilentCfg ι cap tapes heads [] []
        (Cfg.ofWords (input := z) doneI (stateWord CI.k w'))).mapState
          (Sum.inr : CI.State → Unit ⊕ CI.State) ∧
    ∀ u < T,
      ((seamReleaseTM (embedSilentTM ι cap CI.tm) entryI).runFrom
        ((embedSilentCfg ι cap tapes heads [] []
          (Cfg.ofWords (input := z) entryI (stateWord CI.k α))).mapState
            (fun _ => Sum.inl ())) u).state ≠ some (Sum.inr doneI) := by
  have hstate : (embedSilentCfg ι cap tapes heads [] []
      (Cfg.ofWords (input := z) entryI (stateWord CI.k α))).state = some entryI := by
    rw [embedSilentCfg_state, Cfg.ofWords_state]
  have hlock := embedSilentTM_runFrom ι cap hcap CI.tm tapes heads [] []
    (Cfg.ofWords (input := z) entryI (stateWord CI.k α))
  constructor
  · rw [seamReleaseTM_runFrom_pos _ entryI _ hstate T hT, hlock T, hrun]
  · intro u hu
    cases u with
    | zero =>
      rw [MultiTapeTM.runFrom_zero, Cfg.mapState_state, hstate]
      simp
    | succ u =>
      rw [seamReleaseTM_runFrom_pos _ entryI _ hstate (u + 1) (by omega), hlock (u + 1),
        Cfg.mapState_state, embedSilentCfg_state]
      intro hbad
      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hbad
      exact hcut (u + 1) (by omega) hu (hq.trans (congrArg some (Sum.inr.inj heq)))

/-- **The layout call.** A serialization `pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)`
installed at cell zero can be redistributed into the step block's table and empty-output summary.
The return time depends on the serialized machine alone; all other tapes, the native input head,
and the physical output retain their frame. [AB09, §1.4.1]

**Proof sketch.** Specialize the shared layout contract to the state-count header and the
machine's unary initial state. Its shifted unary buffer is the empty-output summary, since
its cell at zero reads the blank cell at offset minus two. -/
theorem exists_layoutCall (K : ℕ) (src tbl sm : Fin K) (hst : src ≠ tbl)
    (hss : src ≠ sm) (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM K Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {k n : ℕ} (M : MultiTapeTM k Bool (Fin (n + 1))),
        ∃ T ≤ C * ((pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)).length + 1),
          ∀ {z : List Bool} (d : Cfg K Bool Q z),
            d.state = some entry →
            d.workTapes src =
              FinTM.bufferTape (pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)) →
            d.workTapePos src = 0 →
            d.workTapes tbl = (fun _ => none) → d.workTapePos tbl = 0 →
            d.workTapes sm = (fun _ => none) → d.workTapePos sm = 0 →
            (L.runFrom d T).state = some done ∧
            (L.runFrom d T).inputPos = d.inputPos ∧
            (L.runFrom d T).workTapes =
              Function.update (Function.update (Function.update d.workTapes src (fun _ => none))
                tbl (FinTM.bufferTape (tableBitsK M.tr)))
                sm (StepBlock.summaryCells none (unaryFin M.q₀)) ∧
            (L.runFrom d T).workTapePos =
              Function.update (Function.update (Function.update d.workTapePos src 0) tbl 0) sm 0 ∧
            (∀ u ≤ T, (L.runFrom d u).output = d.output) ∧
            ∀ u < T, (L.runFrom d u).state ≠ some done := by
  obtain ⟨Q, hQ, hQ', L, entry, done, C, layout⟩ :=
    exists_seamLayoutTM K src tbl sm hst hss hts
  refine ⟨Q, hQ, hQ', L, entry, done, C, ?_⟩
  intro k n M
  have word : pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr) =
      pairEncode n.bits ((List.replicate (M.q₀ : ℕ) true ++ [false]) ++ tableBitsK M.tr) := by
    rw [unaryFin_eq]
  have summary : (fun p =>
      FinTM.bufferTape (List.replicate (M.q₀ : ℕ) true ++ [false]) (p - 2)) =
      StepBlock.summaryCells none (unaryFin M.q₀) := by
    funext p
    rw [StepBlock.summaryCells_eq, unaryFin_eq]
    by_cases hp : p = 0
    · rw [if_pos hp, hp]
      exact FinTM.bufferTape_of_neg _ (by omega)
    · rw [if_neg hp]
  obtain ⟨T, bound, run⟩ := layout n.bits (tableBitsK M.tr) M.q₀ 0 (Nat.zero_le _)
  rw [← word] at bound run
  refine ⟨T, bound, ?_⟩
  intro z d hd hsrc hsrcp htbl htblp hsm hsmp
  obtain ⟨hstate, hin, htapes, hheads, hout, hcut⟩ :=
    run d hd hsrc hsrcp htbl htblp hsm hsmp
  exact ⟨hstate, hin, by rw [htapes, summary], hheads, hout, hcut⟩

end Turing
