/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.ChoiceWords

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the certificate shell (W2-V)

The plain verifier side of certificate enumeration ([AB09, Claim 2.4 and Theorem 2.6]): a
plain machine run on an input with a certificate preloaded on a work tape becomes a decider
of the concatenated language, and projecting along certificates of the prescribed length
recovers the outcome condition. Its customers are the `NP^EXPCOM ⊆ EXP` summit (with
`TCSlib.Complexity.TuringMachine.Build.OracleSim`) and, in the 12.2c window, the chapter-2
shell it generalizes (the private `cont_choiceVerifier_mem_P` of
`TCSlib.Complexity.ClassNP.Nondeterminism`).

**Status: proved** (the certificate shell and its projection identity are proved).

## Main results

* `Turing.FinTM.exists_certificateShell` — the shell (proved).
* `Turing.FinTM.certificateShell_proj` — its projection identity (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Claim 2.4, Theorem 2.6.)
-/

namespace Turing

/-- The two cells just left of the output head characterize the singleton `true` word.
**Proof sketch.** A blank second cell forces the word to have length at most one;
the first cell then distinguishes the singleton from the empty word. -/
private theorem cert_tail_test (w : List Bool) :
    (FinTM.bufferTape w ((w.length : ℤ) - 1) = some true ∧
      FinTM.bufferTape w ((w.length : ℤ) - 2) = none) ↔ w = [true] := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    have hlen : w.length ≤ 1 := by
      by_contra hn
      have hz : 0 ≤ (w.length : ℤ) - 2 := by omega
      have hi : ((w.length : ℤ) - 2).toNat < w.length := by omega
      simp only [FinTM.bufferTape, if_pos hz, List.getElem?_eq_none_iff] at hsecond
      omega
    cases w with
    | nil => simp at hfirst
    | cons b rest =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst rest
      simpa [FinTM.bufferTape] using hfirst
  · rintro rfl
    norm_num [FinTM.bufferTape]

/-- Verdict controller starting just past a captured output. There is no catalog row
for the exact singleton verdict: one left move, a `true` test, and a left-blank test.
It emits once and halts; the source's output never reaches the physical output. -/
private def certVerdictTM (k : ℕ) (cap : Fin k) : MultiTapeTM k Bool (Fin 3) where
  q₀ := 0
  tr := fun q _ w =>
    if q = 0 then
      ⟨0, fun i => (none, if i = cap then -1 else 0), none, some 1⟩
    else if q = 1 then
      if w cap = some true then
        ⟨0, fun i => (none, if i = cap then -1 else 0), none, some 2⟩
      else ⟨0, fun _ => (none, 0), some false, none⟩
    else ⟨0, fun _ => (none, 0), some (decide (w cap = none)), none⟩

/-- The captured-output verdict is complete after three steps, preserving the
physical prefix and appending precisely the singleton-equality bit.
**Proof sketch.** Expand the three finite transitions. The rejecting second step
is absorbed at step three. The accepting branch reads the two cells in `cert_tail_test`. -/
private theorem certVerdict_run {k : ℕ} {x : List Bool} (cap : Fin k)
    (d : Cfg k Bool (Fin 3) x) (w : List Bool)
    (hs : d.state = some 0) (hw : d.workTapes cap = FinTM.bufferTape w)
    (hp : d.workTapePos cap = (w.length : ℤ)) :
    ((certVerdictTM k cap).runFrom d 3).state = none ∧
      ((certVerdictTM k cap).runFrom d 3).output = d.output ++ [decide (w = [true])] := by
  have ht := cert_tail_test w
  simp only [sub_eq_add_neg] at ht
  by_cases hlast : FinTM.bufferTape w ((w.length : ℤ) + -1) = some true <;>
    simp_all [MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.step, certVerdictTM, Action.apply, Cfg.workTapeSymbols, add_assoc]

/-- The capture projection of the public silent configuration, for an unselected
capture tape. This missing projection is a promotion candidate in `Build/Embed`.
**Proof sketch.** No source index maps to the capture tape, so the finite lookup
returns `none` and the two capture clauses of the configuration apply. -/
private theorem cert_capture_fields {m k : ℕ} {S : Type} {x : List Bool}
    (ι : Fin m ↪ Fin k) (cap : Fin k) (hcap : cap ∉ Set.range ι)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (d : Cfg m Bool S x) :
    (embedSilentCfg ι cap tapes heads pre out₀ d).workTapes cap =
        FinTM.bufferTape (pre ++ d.output) ∧
      (embedSilentCfg ι cap tapes heads pre out₀ d).workTapePos cap =
        ((pre ++ d.output).length : ℤ) := by
  have hfind : (List.finRange m).find? (fun i => decide (ι i = cap)) = none := by
    apply List.find?_eq_none.mpr
    intro i _
    simpa only [decide_eq_true_eq] using (fun hi => hcap ⟨i, hi⟩ : ι i ≠ cap)
  change (match (List.finRange m).find? (fun i => decide (ι i = cap)) with
      | some i => d.workTapes i
      | none => if cap = cap then FinTM.bufferTape (pre ++ d.output) else tapes cap) = _ ∧
    (match (List.finRange m).find? (fun i => decide (ι i = cap)) with
      | some i => d.workTapePos i
      | none => if cap = cap then ((pre ++ d.output).length : ℤ) else heads cap) = _
  simp only [hfind, ↓reduceIte, and_self]

/-- The prepared certificate core: forwarding Z1 inside the returning R1 capture,
then one public R2 seam into the constant-time verdict controller. -/
private def certCoreTM {k : ℕ} (P : FinTM Bool)
    (ι : Fin (1 + P.k) ↪ Fin k) (cap : Fin k) : FinTM Bool :=
  ⟨k, ((P.State × Bool) ⊕ Unit) ⊕ Fin 3,
    seamCompTM (embedSilentRetTM ι cap (vhostEmitTM P.tm)) (.inr ())
      (certVerdictTM k cap) 0⟩

/-- The core reaches a halting verdict within four steps beyond the supplied
source deadline, on arbitrary physical input and ambient frame.
**Proof sketch.** Select the source's first halt. Z1 transfers liveness and that
halt, R1' captures the entire output including the last emission, and R2 runs the
three-step verdict scan. All three machine traces are cited from the public rows. -/
private theorem certCore_run {k : ℕ} (P : FinTM Bool)
    (ι : Fin (1 + P.k) ↪ Fin k) (cap : Fin k) (hcap : cap ∉ Set.range ι)
    {x y : List Bool} (d : Cfg P.k Bool P.State x) (hd : d.state ≠ none)
    (tag : Bool) (htag : FinTM.VirtualTag d.inputPos tag)
    (p : Fin (y.length + 2)) (tapes : Fin k → ℤ → Option Bool)
    (heads : Fin k → ℤ) (deadline : ℕ)
    (hhalt : (P.tm.runFrom d deadline).state = none) :
    ∃ t ≤ deadline + 4,
      let start := (embedSilentCfg ι cap tapes heads [] []
        (vhostCfg d tag p [])).mapState (fun q => Sum.inl (Sum.inl q))
      ((certCoreTM P ι cap).tm.runFrom start t).state = none ∧
        ((certCoreTM P ι cap).tm.runFrom start t).output =
          [decide ((P.tm.runFrom d deadline).output = [true])] := by
  obtain ⟨r, hr, hlive, heq⟩ := P.tm.exists_first_halt d hhalt
  let H := vhostEmitTM P.tm
  let v := vhostCfg d tag p []
  have hv : v.state ≠ none := by simpa [v, vhostCfg] using hd
  have hvlive : ∀ s < r, (H.runFrom v s).state ≠ none := by
    intro s hs
    obtain ⟨b, _, hrun⟩ := vhostEmitTM_runFrom P.tm d tag htag p [] s
    rw [hrun]
    simpa [vhostCfg, Cfg.Halted] using hlive s hs
  obtain ⟨b, _, hvr⟩ := vhostEmitTM_runFrom P.tm d tag htag p [] r
  have hvhalt : (H.runFrom v r).state = none := by
    rw [hvr, heq]
    simp [vhostCfg, hhalt]
  have hvout : (H.runFrom v r).output = (P.tm.runFrom d deadline).output := by
    rw [hvr, heq]
    rfl
  obtain ⟨_, hret, hcut⟩ := embedSilentRetTM_run ι cap hcap H tapes heads [] [] v r
    hv hvlive hvhalt
  let finish : Cfg k Bool ((P.State × Bool) ⊕ Unit) y :=
    { embedSilentCfg ι cap tapes heads [] [] (H.runFrom v r) with state := some (.inr ()) }
  let scan := finish.mapState (fun _ => (0 : Fin 3))
  have hc := cert_capture_fields ι cap hcap tapes heads [] [] (H.runFrom v r)
  have hs := certVerdict_run cap scan (P.tm.runFrom d deadline).output rfl
    (by simpa only [scan, finish, Cfg.mapState, List.nil_append, hvout] using hc.1)
    (by simpa only [scan, finish, Cfg.mapState, List.nil_append, hvout] using hc.2)
  have hseam := seamCompTM_run_ofCfg (embedSilentRetTM ι cap H) (.inr ())
    (certVerdictTM k cap) 0 hret rfl hcut
    (show (certVerdictTM k cap).runFrom scan 3 = _ from rfl)
  refine ⟨r + 1 + 3, by omega, ?_⟩
  change ((certCoreTM P ι cap).tm.runFrom _ _).state = none ∧
    ((certCoreTM P ι cap).tm.runFrom _ _).output = _
  rw [show (certCoreTM P ι cap).tm.runFrom
      ((embedSilentCfg ι cap tapes heads [] [] v).mapState
        (fun q => Sum.inl (Sum.inl q))) (r + 1 + 3) =
      ((certVerdictTM k cap).runFrom scan 3).mapState Sum.inr from by
        simpa only [Cfg.mapState, Option.map_map, Function.comp_def] using hseam]
  constructor
  · simpa only [Cfg.mapState, hs.1, Option.map_none]
  · simpa only [Cfg.mapState, scan, finish, embedSilentCfg, List.nil_append] using hs.2

/-- Strengthen a positive first-return word call to a cut including time zero.
**Proof sketch.** Distinct entry and exit already give the extra cut. If they
coincide, the public release adapter provides a fresh entry at the same cost. -/
private theorem cert_call_cut {A : Type} (k : ℕ) (S : Type)
    [Fintype S] [DecidableEq S] (M : MultiTapeTM k Bool S) (en ex : S)
    (input : A → List Bool) (before after : A → Fin k → List Bool) (budget : A → ℕ)
    (h : ∀ a, ∃ t ≤ budget a, 0 < t ∧
      (∀ u, 0 < u → u < t →
        (M.runFrom (Cfg.ofWords (input := input a) en (before a)) u).state ≠ some ex) ∧
      M.runFrom (Cfg.ofWords (input := input a) en (before a)) t =
        Cfg.ofWords ex (after a)) :
    ∃ (S' : Type) (_ : Fintype S') (_ : DecidableEq S')
      (N : MultiTapeTM k Bool S') (start finish : S'),
      ∀ a, ∃ t ≤ budget a,
        (∀ u < t, (N.runFrom (Cfg.ofWords (input := input a) start (before a)) u).state ≠
          some finish) ∧
        N.runFrom (Cfg.ofWords (input := input a) start (before a)) t =
          Cfg.ofWords finish (after a) := by
  by_cases he : en = ex
  · subst ex
    refine ⟨Unit ⊕ S, inferInstance, inferInstance, seamReleaseTM M en,
      Sum.inl (), Sum.inr en, ?_⟩
    intro a
    rcases h a with ⟨t, ht, hpos, hprefix, hdone⟩
    have release := seamReleaseTM_firstReturn M en rfl hpos hdone rfl hprefix
    refine ⟨t, ht, ?_, ?_⟩
    · simpa only [Cfg.mapState, Cfg.ofWords, Option.map_some] using release.2
    · simpa only [Cfg.mapState, Cfg.ofWords, Option.map_some] using release.1
  · refine ⟨S, inferInstance, inferInstance, M, en, ex, ?_⟩
    intro a
    rcases h a with ⟨t, ht, _, hprefix, hdone⟩
    refine ⟨t, ht, fun u hu => ?_, hdone⟩
    by_cases hu0 : u = 0
    · subst u
      simpa [Cfg.ofWords] using he
    · exact hprefix u (Nat.pos_of_ne_zero hu0) hu

/-- Forwarding a word configuration through a selected bank gives a specified
ambient word configuration whenever its selected words and frame agree.
**Proof sketch.** Selected components use the public selected-tape projections;
unselected components use the public frame theorem at time zero. -/
private theorem cert_embed_words {m k : ℕ} {S : Type} {y : List Bool}
    (M : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k) (q : S)
    (localWords : Fin m → List Bool) (frame target : Fin k → List Bool)
    (hin : ∀ i, target (ι i) = localWords i)
    (hout : ∀ i, i ∉ Set.range ι → target i = frame i) :
    embedEmitCfg ι (fun i => FinTM.bufferTape (frame i)) (fun _ => 0) []
      (Cfg.ofWords (input := y) q localWords) = Cfg.ofWords q target := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hi
      rw [embedEmitCfg_selected_tape]
      exact congrArg FinTM.bufferTape (hin j).symm
    · have hf := (embedEmitTM_frame ι M (fun i => FinTM.bufferTape (frame i))
        (fun _ => 0) [] (Cfg.ofWords (input := y) q localWords) 0).1 i hi
      simpa only [MultiTapeTM.runFrom_zero, Cfg.ofWords, hout i hi] using hf.1
  · funext i
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hi
      exact embedEmitCfg_selected_pos ι _ _ [] _ j
    · exact ((embedEmitTM_frame ι M (fun i => FinTM.bufferTape (frame i))
        (fun _ => 0) [] (Cfg.ofWords (input := y) q localWords) 0).1 i hi).2
  · rfl

/-- A clean word call may be placed in a selected bank while all other words
are retained. The cut is transported by the same public R1 equality. -/
private theorem cert_embed_call {m k : ℕ} {S : Type} {y : List Bool}
    (M : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k) (en ex : S)
    (localBefore localAfter : Fin m → List Bool) (before after : Fin k → List Bool)
    (hbefore : ∀ i, before (ι i) = localBefore i)
    (hafter : ∀ i, after (ι i) = localAfter i)
    (hframe : ∀ i, i ∉ Set.range ι → after i = before i) {t : ℕ}
    (hrun : M.runFrom (Cfg.ofWords (input := y) en localBefore) t =
      Cfg.ofWords ex localAfter)
    (hcut : ∀ u < t, (M.runFrom (Cfg.ofWords (input := y) en localBefore) u).state ≠ some ex) :
    (embedEmitTM ι M).runFrom (Cfg.ofWords (input := y) en before) t =
        Cfg.ofWords ex after ∧
      ∀ u < t, ((embedEmitTM ι M).runFrom (Cfg.ofWords (input := y) en before) u).state ≠
        some ex := by
  have hstart := cert_embed_words (y := y) M ι en localBefore before before hbefore
    (fun _ _ => rfl)
  have transport := fun u => embedEmitTM_runFrom ι M (fun i => FinTM.bufferTape (before i))
    (fun _ => 0) [] (Cfg.ofWords (input := y) en localBefore) u
  rw [hstart] at transport
  constructor
  · rw [transport t, hrun]
    exact cert_embed_words M ι ex localAfter before after hafter hframe
  · intro u hu
    rw [transport u]
    exact hcut u hu


/-- Package the two public R2 word-seam conclusions for repeated finite composition. -/
private theorem cert_seq {k : ℕ} {S U : Type} [DecidableEq S] {y : List Bool}
    (M : MultiTapeTM k Bool S) (N : MultiTapeTM k Bool U) (en ex : S) (start finish : U)
    (w₀ w₁ w₂ : Fin k → List Bool) {t₀ t₁ : ℕ}
    (h₀ : M.runFrom (Cfg.ofWords (input := y) en w₀) t₀ = Cfg.ofWords ex w₁)
    (cut₀ : ∀ t < t₀, (M.runFrom (Cfg.ofWords (input := y) en w₀) t).state ≠ some ex)
    (h₁ : N.runFrom (Cfg.ofWords (input := y) start w₁) t₁ = Cfg.ofWords finish w₂)
    (cut₁ : ∀ t < t₁, (N.runFrom (Cfg.ofWords (input := y) start w₁) t).state ≠ some finish) :
    (seamCompTM M ex N start).runFrom (Cfg.ofWords (input := y) (Sum.inl en) w₀)
        (t₀ + 1 + t₁) = Cfg.ofWords (Sum.inr finish) w₂ ∧
      ∀ t < t₀ + 1 + t₁,
        ((seamCompTM M ex N start).runFrom (Cfg.ofWords (input := y) (Sum.inl en) w₀) t).state ≠
          some (Sum.inr finish) :=
  ⟨seamCompTM_run M ex N start en finish w₀ w₁ w₂ t₀ t₁ h₀ cut₀ h₁,
    seamCompTM_firstReturn M ex N start en finish w₀ w₁ w₂ t₀ t₁ h₀ cut₀ h₁ cut₁⟩

/-- A selected blank bank becomes a standard argument bank after updating its
zero slot. This is an index equation, independent of any machine trace. -/
private theorem cert_bank_word {m k : ℕ} (hm : 0 < m) (ι : Fin m ↪ Fin k)
    (frame : Fin k → List Bool) (hframe : ∀ i, frame (ι i) = []) (w : List Bool) :
    ∀ i, Function.update frame (ι ⟨0, hm⟩) w (ι i) = stateWord m w i := by
  intro i
  by_cases hz : i = ⟨0, hm⟩
  · subst i
    simp [stateWord]
  · have hv : i.val ≠ 0 := fun hi => hz (Fin.ext hi)
    rw [Function.update_of_ne (fun h => hz (ι.injective h)), hframe]
    simp only [stateWord, if_neg hv]

/-- Canonical ambient words agree with a silent transport whose selected tapes
have those words and whose capture is empty. Only the control is relabeled.
**Proof sketch.** Selected tapes and heads use the public projections, the capture
uses `cert_capture_fields`, and the remainder uses R1's frame contract at time zero. -/
private theorem cert_silent_words {m k : ℕ} {S U : Type} {y : List Bool}
    (M : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (w : Fin k → List Bool) (d : Cfg m Bool S y)
    (q : S) (finish : U) (hs : d.state = some q) (hp : d.inputPos = 1)
    (htape : ∀ i, d.workTapes i = FinTM.bufferTape (w (ι i)))
    (hhead : ∀ i, d.workTapePos i = 0) (ho : d.output = []) (hc : w cap = []) :
    (embedSilentCfg ι cap (fun i => FinTM.bufferTape (w i)) (fun _ => 0) [] [] d).mapState
      (fun _ => finish) = Cfg.ofWords finish w := by
  have frame := (embedSilentTM_frame ι cap hcap M (fun i => FinTM.bufferTape (w i))
    (fun _ => 0) [] [] d 0).1
  have capture := cert_capture_fields ι cap hcap (fun i => FinTM.bufferTape (w i))
    (fun _ => 0) [] [] d
  apply Cfg.ext
  · simp only [Cfg.mapState, embedSilentCfg, hs, Option.map_some, Cfg.ofWords]
  · exact hp
  · funext i
    change (embedSilentCfg ι cap (fun i => FinTM.bufferTape (w i)) (fun _ => 0) [] [] d).workTapes i = FinTM.bufferTape (w i)
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨r, rfl⟩ := hi
      rw [embedSilentCfg_selected_tape]
      exact htape r
    · by_cases he : i = cap
      · subst i
        simpa only [ho, hc, List.nil_append] using capture.1
      · exact (frame i hi he).1
  · funext i
    change (embedSilentCfg ι cap (fun i => FinTM.bufferTape (w i)) (fun _ => 0) [] [] d).workTapePos i = 0
    by_cases hi : i ∈ Set.range ι
    · obtain ⟨r, rfl⟩ := hi
      rw [embedSilentCfg_selected_pos]
      exact hhead r
    · by_cases he : i = cap
      · subst i
        simpa only [ho, List.nil_append, List.length_nil, Nat.cast_zero] using capture.2
      · exact (frame i hi he).2
  · rfl

/-- The prescribed split emitter's output word, including its empty failure value. -/
private def certSplitWord (C c : ℕ) (y : List Bool) : List Bool :=
  match solveSplit C c y.length with
  | some i => pairEncode (y.take i) (y.drop i)
  | none => []

/-- The doubled-prefix encoding costs at most twice the original input length plus two. -/
private theorem certSplitWord_length (C c : ℕ) (y : List Bool) :
    (certSplitWord C c y).length ≤ 2 * y.length + 2 := by
  unfold certSplitWord
  split
  · rw [length_pairEncode, List.length_take, List.length_drop]
    omega
  · simp

/-- Successful bounded split search supplies a certificate of the exact requested length. -/
private theorem certSplit_valid (C c : ℕ) (y : List Bool) (i : ℕ)
    (h : solveSplit C c y.length = some i) :
    (y.drop i).length = C * ((y.take i).length + 1) ^ c := by
  have hmem := List.mem_of_find?_eq_some h
  have heq := List.find?_some h
  simp only [List.mem_range] at hmem
  simp only [beq_iff_eq] at heq
  rw [List.length_drop, List.length_take_of_le (by omega)]
  omega

/-- The split search and the certificate language give the same success condition.
**Proof sketch.** On failure, any certificate would supply an element accepted by
the bounded search. On success, use the public split-uniqueness theorem to identify
any proposed witness with the recovered prefix and suffix. -/
private theorem certSplit_language (C c : ℕ) (out : List Bool → List Bool → List Bool)
    (y : List Bool) :
    (∃ x u, y = x ++ u ∧ u.length = C * (x.length + 1) ^ c ∧ out x u = [true]) ↔
      match solveSplit C c y.length with
      | none => False
      | some i => out (y.take i) (y.drop i) = [true] := by
  cases hs : solveSplit C c y.length with
  | none =>
    constructor
    · rintro ⟨x, u, hy, hu, _⟩
      have hmissing := List.find?_eq_none.mp hs x.length
        (by simp only [List.mem_range]; rw [hy, List.length_append]; omega)
      apply hmissing
      simp only [beq_iff_eq]
      rw [hy, List.length_append, hu]
    · exact False.elim
  | some i =>
    have hc := certSplit_valid C c y i hs
    constructor
    · rintro ⟨x, u, hy, hu, ho⟩
      obtain ⟨hx, hv⟩ := append_split_unique (certificateLength_strictMono C c) hu hc
        (hy.symm.trans (List.take_append_drop i y).symm)
      simpa only [← hx, ← hv] using ho
    · intro ho
      exact ⟨y.take i, y.drop i, (List.take_append_drop i y).symm, hc, ho⟩

/-- Reject the split emitter's empty failure value before invoking any core.
No catalog row supplies this reject-or-return guard. A valid encoded pair is
nonempty even when both components are empty. -/
private def certGuardTM (k : ℕ) (slot : Fin k) : MultiTapeTM k Bool Bool where
  q₀ := false
  tr := fun _ _ work =>
    if work slot = none then ⟨0, fun _ => (none, 0), some false, none⟩
    else ⟨0, fun _ => (none, 0), none, some true⟩

/-- One guard transition either rejects the empty word or returns the unchanged word seam. -/
private theorem certGuard_run {k : ℕ} {y : List Bool} (slot : Fin k)
    (w : Fin k → List Bool) :
    (certGuardTM k slot).runFrom (Cfg.ofWords (input := y) false w) 1 =
      if w slot = [] then
        { Cfg.ofWords (input := y) true w with state := none, output := [false] }
      else Cfg.ofWords true w := by
  have he : FinTM.bufferTape (w slot) 0 = none ↔ w slot = [] := by
    cases w slot <;> simp [FinTM.bufferTape]
  simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, certGuardTM,
    Cfg.ofWords, Cfg.workTapeSymbols, Action.apply, he]
  split <;> simp

/-- The guard does not reach its success anchor before its one transition. -/
private theorem certGuard_cut {k : ℕ} {y : List Bool} (slot : Fin k)
    (w : Fin k → List Bool) :
    ∀ t < 1, ((certGuardTM k slot).runFrom (Cfg.ofWords (input := y) false w) t).state ≠
      some true := by
  intro t ht
  have : t = 0 := by omega
  subst t
  simp [Cfg.ofWords]

/-- The loader interface, parameterized by the core and the reserved
native-call bank. It is independent of the core's halting behavior.

**Proof sketch.** Allocate disjoint banks for the two install-mode extractors,
the reserved native-call machine, the virtual input and source tapes, and capture.
Duplicate the split word from the reserved bank into the first extractor; install
its first component and transfer it to the virtual-input buffer. Transfer the saved
pair into the second extractor, install its second component, and transfer it to
source tape `j`. Normalize both clean-call cuts with `cert_call_cut`; embed their
contracts with `cert_embed_call`. Chain the copy, two clean calls and three transfers
using the public R2 endpoint and first-return contracts. All work heads return to
zero, the capture is blank, and the sum of six linear costs is linear in `|x|+|u|+1`.
The canonical `copyTM_run`/`transferTM_run` rows already specialize the required
framed contracts, so their word-layout proofs must be cited, not repeated. -/
private theorem cert_prepare_exists (P : FinTM Bool) (j : Fin P.k) (m : ℕ) (hm : 0 < m) :
    ∃ (D : FinTM Bool) (exit : D.State) (ρ : Fin m ↪ Fin D.k)
      (ι : Fin (1 + P.k) ↪ Fin D.k) (cap : Fin D.k) (a : ℕ),
      cap ∉ Set.range ι ∧
      ∀ (y x u : List Bool),
        ∃ t ≤ a * (x.length + u.length + 1),
          ∃ (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
          (∀ s < t, (D.tm.runFrom
            (Cfg.ofWords (input := y) D.tm.q₀
              (Function.update (fun _ => []) (ρ ⟨0, hm⟩) (pairEncode x u))) s).state ≠
                some exit) ∧
          D.tm.runFrom
            (Cfg.ofWords (input := y) D.tm.q₀
              (Function.update (fun _ => []) (ρ ⟨0, hm⟩) (pairEncode x u))) t =
            (embedSilentCfg ι cap tapes heads [] []
              (vhostCfg (Cfg.ofWords (input := x) P.tm.q₀
                (Function.update (fun _ => []) j u)) true (1 : Fin (y.length + 2)) [])).mapState
                  (fun _ => exit) := by
  obtain ⟨F, f, hf⟩ := FinTM.computesFunInTime_pairFst
  obtain ⟨F₀, fen, fex, af, hkF, hF₀⟩ := FinTM.exists_installCallTM F _ _ hf
  obtain ⟨FS, ff, fd, FM, fe, fx, hF⟩ := cert_call_cut F₀.k F₀.State F₀.tm fen fex
    (fun z : List Bool × List Bool => z.1) (fun z => stateWord F₀.k z.2)
    (fun z => stateWord F₀.k (((pairDecode z.2).map Prod.fst).getD []))
    (fun z => af * (f * (z.2.length + 1) + z.2.length +
      (((pairDecode z.2).map Prod.fst).getD []).length + 1)) (fun z => hF₀ z.1 z.2)
  letI : Fintype FS := ff
  letI : DecidableEq FS := fd
  obtain ⟨S, s, hs⟩ := FinTM.computesFunInTime_pairSnd
  obtain ⟨S₀, sen, sex, as, hkS, hS₀⟩ := FinTM.exists_installCallTM S _ _ hs
  obtain ⟨SS, sf, sd, SM, se, sx, hS⟩ := cert_call_cut S₀.k S₀.State S₀.tm sen sex
    (fun z : List Bool × List Bool => z.1) (fun z => stateWord S₀.k z.2)
    (fun z => stateWord S₀.k (((pairDecode z.2).map Prod.snd).getD []))
    (fun z => as * (s * (z.2.length + 1) + z.2.length +
      (((pairDecode z.2).map Prod.snd).getD []).length + 1)) (fun z => hS₀ z.1 z.2)
  letI : Fintype SS := sf
  letI : DecidableEq SS := sd
  let K := m + (F₀.k + (S₀.k + ((1 + P.k) + 1)))
  let ρ : Fin m ↪ Fin K := Fin.castAddEmb _
  let σF : Fin F₀.k ↪ Fin K := (Fin.castAddEmb _).trans (Fin.natAddEmb m)
  let σS : Fin S₀.k ↪ Fin K :=
    ((Fin.castAddEmb _).trans (Fin.natAddEmb F₀.k)).trans (Fin.natAddEmb m)
  let ι : Fin (1 + P.k) ↪ Fin K :=
    (((Fin.castAddEmb 1).trans (Fin.natAddEmb S₀.k)).trans (Fin.natAddEmb F₀.k)).trans
      (Fin.natAddEmb m)
  let cap : Fin K := Fin.natAdd m (Fin.natAdd F₀.k (Fin.natAdd S₀.k (vhostCap P.k)))
  have hρ (i : Fin m) : (ρ i).val = i.val := rfl
  have hσF (i : Fin F₀.k) : (σF i).val = m + i.val := rfl
  have hσS (i : Fin S₀.k) : (σS i).val = m + (F₀.k + i.val) := rfl
  have hι (i : Fin (1 + P.k)) : (ι i).val = m + (F₀.k + (S₀.k + i.val)) := rfl
  have hcapval : cap.val = m + (F₀.k + (S₀.k + (1 + P.k))) := rfl
  let v := ρ ⟨0, hm⟩
  let vf := σF ⟨0, hkF⟩
  let vs := σS ⟨0, hkS⟩
  let vx := ι (vhostBuffer P.k)
  let vu := ι (vhostBank j)
  have hcap : cap ∉ Set.range ι := by
    rintro ⟨i, he⟩
    have hval := congrArg Fin.val he
    have hi := i.isLt
    simp only [hι, hcapval] at hval
    omega
  have hdistinct : v ≠ vf ∧ v ≠ vx ∧ v ≠ vs ∧ v ≠ vu ∧
      vf ≠ vx ∧ vf ≠ vs ∧ vf ≠ vu ∧ vx ≠ vs ∧ vx ≠ vu ∧ vs ≠ vu := by
    repeat' constructor
    all_goals
      apply Fin.ne_of_val_ne
      simp only [v, vf, vs, vx, vu, hρ, hσF, hσS, hι,
        vhostBuffer, vhostBank, Fin.coe_castAdd, Fin.coe_natAdd]
      omega
  rcases hdistinct with ⟨hvf, hvx, hvs, hvu, hfx, hfs, hfu, hxs, hxu, hsu⟩
  let CF := embedEmitTM σF FM
  let CS := embedEmitTM σS SM
  let M₀ := copyTM (Symbol := Bool) K v vf
  let M₁ := seamCompTM M₀ .done CF fe
  let M₂ := seamCompTM M₁ (.inr fx) (transferTM K vf vx) .sweep
  let M₃ := seamCompTM M₂ (.inr .done) (transferTM K v vs) .sweep
  let M₄ := seamCompTM M₃ (.inr .done) CS se
  let M₅ := seamCompTM M₄ (.inr sx) (transferTM K vs vu) .sweep
  let D : FinTM Bool := ⟨K, _, M₅⟩
  refine ⟨D, .inr .done, ρ, ι, cap, 30 + af * (3 * f + 4) + as * (3 * s + 4), hcap, ?_⟩
  intro y x u
  let pair := pairEncode x u
  let w₀ := Function.update (fun _ : Fin K => []) v pair
  let w₁ := Function.update w₀ vf pair
  let w₂ := Function.update w₀ vf x
  let w₃ := Function.update (Function.update w₂ vf []) vx x
  let w₄ := Function.update (Function.update w₃ v []) vs pair
  let w₅ := Function.update (Function.update w₃ v []) vs u
  let w₆ := Function.update (Function.update w₅ vs []) vu u
  have hfinal : w₆ = Function.update (Function.update (fun _ => []) vx x) vu u := by
    funext z
    by_cases hzv : z = v
    · subst z
      simp [w₆, w₅, w₃, w₂, w₀, hvx, hvs, hvu]
    by_cases hzf : z = vf
    · subst z
      simp [w₆, w₅, w₃, w₂, w₀, hfu, hfx, hfs, hvf.symm]
    by_cases hzs : z = vs
    · subst z
      simp [w₆, w₅, w₃, w₂, w₀, hsu, hxs.symm]
    simp [w₆, w₅, w₃, w₂, w₀, Function.update_apply, hzv, hzf, hzs]
  have hblankF (i : Fin F₀.k) : w₀ (σF i) = [] := by
    apply Function.update_of_ne
    intro he
    have he' := congrArg Fin.val he
    simp only [v, hρ, hσF] at he'
    omega
  have hblankS (i : Fin S₀.k) : Function.update w₃ v [] (σS i) = [] := by
    have hn : σS i ≠ v ∧ σS i ≠ vf ∧ σS i ≠ vx := by
      repeat' constructor
      all_goals
        apply Fin.ne_of_val_ne
        simp only [v, vf, vx, hρ, hσF, hσS, hι,
        vhostBuffer, Fin.coe_castAdd]
        have hi := i.isLt
        omega
    simp [w₃, w₂, w₀, hn.1, hn.2.1, hn.2.2]
  obtain ⟨t₀, ht₀, hc₀, hr₀⟩ := copyTM_run (x := y) K v vf hvf w₀
    (by simp [w₀, hvf.symm])
  have h0 : w₀ v = pair := Function.update_self _ _ _
  simp only [h0] at ht₀ hr₀
  obtain ⟨t₁, ht₁, hc₁, hr₁⟩ := hF (y, pair)
  simp only [pair, pairDecode_pairEncode, Option.map_some, Option.getD_some] at ht₁ hr₁ hc₁
  obtain ⟨hfRun, hfCut⟩ := cert_embed_call FM σF fe fx (stateWord F₀.k pair)
    (stateWord F₀.k x) w₁ w₂ (cert_bank_word hkF σF w₀ hblankF pair)
    (cert_bank_word hkF σF w₀ hblankF x)
    (by
      intro i hi
      have hn : i ≠ vf := fun he => hi ⟨⟨0, hkF⟩, he.symm⟩
      simp [w₁, w₂, hn]) hr₁ hc₁
  have h2 : w₂ vf = x := Function.update_self _ _ _
  obtain ⟨t₂, ht₂, hc₂, hr₂⟩ := transferTM_run (x := y) K vf vx hfx w₂
    (by simp [w₂, w₀, hfx.symm, hvx.symm])
  simp only [h2] at ht₂ hr₂
  have h3 : w₃ v = pair := by simp [w₃, w₂, w₀, hvx, hvf]
  obtain ⟨t₃, ht₃, hc₃, hr₃⟩ := transferTM_run (x := y) K v vs hvs w₃
    (by simp [w₃, w₂, w₀, hxs.symm, hfs.symm, hvs.symm])
  simp only [h3] at ht₃ hr₃
  obtain ⟨t₄, ht₄, hc₄, hr₄⟩ := hS (y, pair)
  simp only [pair, pairDecode_pairEncode, Option.map_some, Option.getD_some] at ht₄ hr₄ hc₄
  obtain ⟨hsRun, hsCut⟩ := cert_embed_call SM σS se sx (stateWord S₀.k pair)
    (stateWord S₀.k u) w₄ w₅ (cert_bank_word hkS σS _ hblankS pair)
    (cert_bank_word hkS σS _ hblankS u)
    (by
      intro i hi
      have hn : i ≠ vs := fun he => hi ⟨⟨0, hkS⟩, he.symm⟩
      simp [w₄, w₅, hn]) hr₄ hc₄
  have h5 : w₅ vs = u := Function.update_self _ _ _
  obtain ⟨t₅, ht₅, hc₅, hr₅⟩ := transferTM_run (x := y) K vs vu hsu w₅
    (by simp [w₅, w₃, w₂, w₀, hsu.symm, hvu.symm, hxu.symm, hfu.symm])
  simp only [h5] at ht₅ hr₅
  have h01 := cert_seq M₀ CF .sweep .done fe fx w₀ w₁ w₂ hr₀ hc₀ hfRun hfCut
  have h02 := cert_seq M₁ (transferTM K vf vx) (.inl .sweep) (.inr fx) .sweep .done
    w₀ w₂ w₃ h01.1 h01.2 hr₂ hc₂
  have h03 := cert_seq M₂ (transferTM K v vs) (.inl (.inl .sweep)) (.inr .done) .sweep .done
    w₀ w₃ w₄ h02.1 h02.2 hr₃ hc₃
  have h04 := cert_seq M₃ CS (.inl (.inl (.inl .sweep))) (.inr .done) se sx
    w₀ w₄ w₅ h03.1 h03.2 hsRun hsCut
  have h05 := cert_seq M₄ (transferTM K vs vu) (.inl (.inl (.inl (.inl .sweep))))
    (.inr sx) .sweep .done w₀ w₅ w₆ h04.1 h04.2 hr₅ hc₅
  refine ⟨(((((t₀ + 1 + t₁) + 1 + t₂) + 1 + t₃) + 1 + t₄) + 1 + t₅), ?_,
    (fun i => FinTM.bufferTape (w₆ i)), (fun _ => 0), h05.2, ?_⟩
  · simp only [pair, length_pairEncode] at ht₀ ht₁ ht₃ ht₄
    have hfbound : t₁ ≤ af * (3 * f + 4) * (x.length + u.length + 1) := by
      apply ht₁.trans
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      nlinarith
    have hsbound : t₄ ≤ as * (3 * s + 4) * (x.length + u.length + 1) := by
      apply ht₄.trans
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      nlinarith
    rw [Nat.add_mul, Nat.add_mul]
    omega
  · refine h05.1.trans ?_
    symm
    apply cert_silent_words (vhostEmitTM P.tm) ι cap hcap w₆ _ (P.tm.q₀, true)
      (Sum.inr SweepPhase.done) rfl rfl
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro z
        have hz : z = 0 := Subsingleton.elim _ _
        subst z
        change FinTM.bufferTape x = FinTM.bufferTape (w₆ vx)
        rw [hfinal]
        simp [hxu]
      · intro z
        simp only [vhostCfg, Fin.addCases_right, Cfg.ofWords]
        change FinTM.bufferTape (Function.update (fun _ => []) j u z) =
          FinTM.bufferTape (w₆ (ι (vhostBank z)))
        apply congrArg FinTM.bufferTape
        rw [hfinal]
        by_cases hz : z = j
        · subst z
          simp only [vu, Function.update_self]
        · have hn : ι (vhostBank z) ≠ vu ∧ ι (vhostBank z) ≠ vx := by
            constructor
            · intro he
              apply hz
              apply Fin.ext
              have he' := congrArg Fin.val he
              simp only [ vu, hι, vhostBank, Fin.coe_natAdd] at he'
              omega
            · apply Fin.ne_of_val_ne
              simp only [ vx, hι,
        vhostBuffer, vhostBank, Fin.coe_castAdd, Fin.coe_natAdd]
              omega
          simp [hz, hn.1, hn.2]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro z
        simp [vhostCfg, Cfg.ofWords]
      · intro z
        simp [vhostCfg, Cfg.ofWords]
    · rfl
    · rw [hfinal]
      have hcx : cap ≠ vx := fun he => hcap ⟨vhostBuffer P.k, he.symm⟩
      have hcu : cap ≠ vu := fun he => hcap ⟨vhostBank j, he.symm⟩
      simp [hcx, hcu]


/-- **The certificate shell** (row W2-V; [AB09, Claim 2.4 and Theorem 2.6], the verifier
side of the enumeration): let the plain machine `P`, started from `Cfg.ofWords` over the
input `x` with the certificate `u` on its tape `j` and every other tape empty, halt by
`T (|x| + |u|)` with output `out x u` whenever `|u| = C·(|x| + 1)^c`. Then some plain machine
decides the language of the strings `x ++ u` with `|u| = C·(|x| + 1)^c` and
`out x u = [true]` within `b·((m + 1)^e + T m)`. With `Complexity.exists_proj_decider`
this decides `{x | ∃ u, |u| = C·(|x| + 1)^c ∧ out x u = [true]}`
(`Turing.FinTM.certificateShell_proj`).

**Proof sketch.** Install the split `pairEncode x u` of the input `y` (the empty word on
failure, which rejects) on a work tape by the native-input clean call
`Turing.FinTM.exists_inputCallTM` (R8.5e, a §12.8 statement: this fill is sequenced after
the §12.8 fill) at `Turing.FinTM.computesFunInTime_splitSolve C c`; duplicate it
(`Turing.copyTM_run_ofCfg`), install `x` and `u` by the install-mode clean calls of
`Turing.FinTM.computesFunInTime_pairFst` and `computesFunInTime_pairSnd`, and move them to
the Z1 buffer and to bank tape `j` (`Turing.transferTM_run_ofCfg`); run `P` under Z1 from
`Turing.vhostCfg (Cfg.ofWords P.q₀ (Function.update (fun _ => []) j u)) true 1 []` (the
tag `true` is valid at position `1` for every `x`), inside the **returning** R1 capture
`Turing.embedSilentRetTM` over `Turing.vhostEmitTM P` (locksteps
`Turing.vhostEmitTM_runFrom` and `Turing.embedSilentRetTM_run`; the closed
`Turing.vhostSilentTM` would die with `P`), which lands in its return anchor at `P`'s first
halt with `P`'s output on the capture tape; a three-state scan of the capture (first cell
`true`, second blank) gives the verdict, which is emitted. Phases by R2 seams; time
`c·(m + 1)^(c + 2) + O(m) + T m + O(T m + 1)`. Template: the private 2B shell of
`TCSlib.Complexity.ClassNP.Nondeterminism` (`cont_choiceVerifier_mem_P`, the paired-input
loader and `choiceCore`), harvested with the core made a parameter.

**Fill appendix.** The empty split value is rejected by a one-step guard before any
source run. Positive clean-call cuts are strengthened to include time zero using
`seamReleaseTM_firstReturn` when entry and exit coincide. The loader uses disjoint
banks and cites `copyTM_run` and `transferTM_run`, the canonical-word corollaries of
the required `_run_ofCfg` rows, together with the two install calls and R2.
The returning capture already places its head just past the output. The three-state
verdict therefore scans left: one move, a last-cell `true` test, and a preceding-blank
test. On a finite captured word these two tests characterize exactly `[true]`, including
empty and longer-word rejection. No output-length rewind is needed; the captured
core and its verdict cost at most `T m + 4`. The assembled shell has exponent `c + 2`
and coefficient `b * (A + 3) + a + 8`, where `A` is the split-computation coefficient,
`b` is the native-call multiplier and `a` is the linear loader coefficient. All
simulation and seam traces are applications of the public contracts. -/
theorem FinTM.exists_certificateShell (P : FinTM Bool) (j : Fin P.k) (C c : ℕ)
    (out : List Bool → List Bool → List Bool) (T : ℕ → ℕ)
    (hP : ∀ x u : List Bool, u.length = C * (x.length + 1) ^ c →
      (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (Function.update (fun _ => []) j u))
          (T (x.length + u.length))).state = none ∧
        (P.tm.runFrom (Cfg.ofWords (input := x) P.tm.q₀ (Function.update (fun _ => []) j u))
          (T (x.length + u.length))).output = out x u) :
    ∃ (V : FinTM Bool) (b e : ℕ),
      V.DecidesInTime {y | ∃ x u, y = x ++ u ∧ u.length = C * (x.length + 1) ^ c ∧
          out x u = [true]}
        fun m => b * ((m + 1) ^ e + T m) := by
  classical
  obtain ⟨M, A, hM⟩ := FinTM.computesFunInTime_splitSolve C c
  obtain ⟨Q, entry, leave, b, hk, hQ⟩ := FinTM.exists_inputCallTM M (certSplitWord C c)
    (fun n => A * (n + 1) ^ (c + 2)) hM
  obtain ⟨AS, af, ad, R, en, ex, hR⟩ := cert_call_cut Q.k Q.State Q.tm entry leave
    (fun y : List Bool => y) (fun _ _ => []) (fun y => stateWord Q.k (certSplitWord C c y))
    (fun y => b * (A * (y.length + 1) ^ (c + 2) + y.length +
      (certSplitWord C c y).length + 1)) hQ
  letI : Fintype AS := af
  letI : DecidableEq AS := ad
  obtain ⟨D, done, ρ, ι, cap, a, hcap, hD⟩ := cert_prepare_exists P j Q.k hk
  let slot := ρ ⟨0, hk⟩
  let core := certCoreTM P ι cap
  let prepared := seamCompTM D.tm done core.tm core.tm.q₀
  let checked := seamCompTM (certGuardTM D.k slot) true prepared prepared.q₀
  let whole := seamCompTM (embedEmitTM ρ R) ex checked checked.q₀
  let V : FinTM Bool := ⟨D.k, AS ⊕ (Bool ⊕ (D.State ⊕ core.State)),
    { whole with q₀ := .inl en }⟩
  let L : Set (List Bool) := {y | ∃ x u, y = x ++ u ∧
    u.length = C * (x.length + 1) ^ c ∧ out x u = [true]}
  refine ⟨V, b * (A + 3) + a + 8, c + 2, ?_⟩
  intro y
  let w := Function.update (fun _ : Fin D.k => []) slot (certSplitWord C c y)
  obtain ⟨t₀, ht₀, hcut₀, hr₀⟩ := hR y
  have hwords : ∀ i, w (ρ i) = stateWord Q.k (certSplitWord C c y) i := by
    intro i
    by_cases hi : i = ⟨0, hk⟩
    · subst i
      simp [w, slot, stateWord]
    · have hne : ρ i ≠ slot := fun h => hi (ρ.injective h)
      have hz : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp [w, hne, stateWord, hz]
  have hframe : ∀ i, i ∉ Set.range ρ → w i = [] := by
    intro i hi
    have hne : i ≠ slot := fun h => hi ⟨⟨0, hk⟩, h.symm⟩
    simp [w, hne]
  obtain ⟨hfirst, hfirstCut⟩ := cert_embed_call R ρ en ex (fun _ => [])
    (stateWord Q.k (certSplitWord C c y)) (fun _ => []) w
    (fun _ => rfl) hwords hframe hr₀ hcut₀
  have htail : ∃ t ≤ a * (y.length + 1) + T y.length + 7,
      (checked.runFrom (Cfg.ofWords (input := y) checked.q₀ w) t).state = none ∧
      (checked.runFrom (Cfg.ofWords (input := y) checked.q₀ w) t).output =
        [MultiTapeTM.indicator L y] := by
    have hsem := certSplit_language C c out y
    cases hs : solveSplit C c y.length with
    | none =>
      have hno : y ∉ L := by simpa only [L, Set.mem_setOf_eq, hs, iff_false] using hsem
      have hg := certGuard_run (y := y) slot w
      have hempty : w slot = [] := by simp [w, certSplitWord, hs]
      rw [if_pos hempty] at hg
      have hleft := seamCompTM_runFrom_left (certGuardTM D.k slot) true prepared prepared.q₀
        (certGuard_cut (y := y) slot w) 1 le_rfl
      refine ⟨1, by omega, ?_, ?_⟩
      · change (checked.runFrom ((Cfg.ofWords (input := y) false w).mapState Sum.inl) 1).state = _
        rw [hleft, hg]
        rfl
      · change (checked.runFrom ((Cfg.ofWords (input := y) false w).mapState Sum.inl) 1).output = _
        rw [hleft, hg]
        simp only [Cfg.mapState, MultiTapeTM.indicator, if_neg hno]
    | some i =>
      have hu := certSplit_valid C c y i hs
      have hlen : (y.take i).length + (y.drop i).length = y.length := by
        simpa only [List.length_append] using congrArg List.length (List.take_append_drop i y)
      have hp := hP (y.take i) (y.drop i) hu
      obtain ⟨t₁, ht₁, tapes, heads, hcut₁, hr₁⟩ := hD y (y.take i) (y.drop i)
      have hword : w = Function.update (fun _ => []) slot
          (pairEncode (y.take i) (y.drop i)) := by simp only [w, certSplitWord, hs]
      rw [← hword] at hr₁ hcut₁
      let d := Cfg.ofWords (input := y.take i) P.tm.q₀
        (Function.update (fun _ => []) j (y.drop i))
      obtain ⟨t₂, ht₂, hc⟩ := certCore_run P ι cap hcap d
        (by simp [d, Cfg.ofWords]) true (by simp [d, Cfg.ofWords, FinTM.VirtualTag])
        (1 : Fin (y.length + 2)) tapes heads (T ((y.take i).length + (y.drop i).length)) hp.1
      let loaded := (embedSilentCfg ι cap tapes heads [] [] (vhostCfg d true
        (1 : Fin (y.length + 2)) [])).mapState (fun _ => done)
      let start : Cfg D.k Bool core.State y := (embedSilentCfg ι cap tapes heads [] [] (vhostCfg d true
        (1 : Fin (y.length + 2)) [])).mapState (fun q => Sum.inl (Sum.inl q))
      have hstart : loaded.mapState (fun _ => core.tm.q₀) = start := by
        simp [loaded, start, core, certCoreTM, seamCompTM, embedSilentRetTM,
          embedSilentCfg, vhostCfg, d, Cfg.ofWords, Cfg.mapState, vhostEmitTM]
      have hdc := seamCompTM_run_ofCfg D.tm done core.tm core.tm.q₀ hr₁
        (by simp [ Cfg.ofWords, Cfg.mapState, embedSilentCfg, vhostCfg]) hcut₁
        (show core.tm.runFrom (loaded.mapState (fun _ => core.tm.q₀)) t₂ =
          core.tm.runFrom start t₂ by rw [hstart])
      have hpair : w slot ≠ [] := by
        rw [hword, Function.update_self]
        intro he
        have hl := congrArg List.length he
        rw [length_pairEncode, List.length_nil] at hl
        omega
      have hg := certGuard_run (y := y) slot w
      rw [if_neg hpair] at hg
      have hchecked := seamCompTM_run_ofCfg (certGuardTM D.k slot) true prepared prepared.q₀
        hg rfl (certGuard_cut slot w) hdc
      refine ⟨1 + 1 + (t₁ + 1 + t₂), ?_, ?_, ?_⟩
      · rw [hlen] at ht₁ ht₂
        omega
      · rw [show checked.runFrom (Cfg.ofWords (input := y) checked.q₀ w)
            (1 + 1 + (t₁ + 1 + t₂)) =
            ((core.tm.runFrom start t₂).mapState Sum.inr).mapState Sum.inr from hchecked]
        simpa [Cfg.mapState] using hc.1
      · rw [show checked.runFrom (Cfg.ofWords (input := y) checked.q₀ w)
            (1 + 1 + (t₁ + 1 + t₂)) =
            ((core.tm.runFrom start t₂).mapState Sum.inr).mapState Sum.inr from hchecked]
        change (core.tm.runFrom start t₂).output = _
        rw [hc.2, hp.2]
        have hm : y ∈ L ↔ out (y.take i) (y.drop i) = [true] := by
          simpa only [L, Set.mem_setOf_eq, hs] using hsem
        simp only [MultiTapeTM.indicator, hm]
        split <;> simp_all
  obtain ⟨t, ht, hhalt, hout⟩ := htail
  have hwhole := seamCompTM_run_ofCfg (embedEmitTM ρ R) ex checked checked.q₀
    hfirst rfl hfirstCut
    (show checked.runFrom ((Cfg.ofWords (input := y) ex w).mapState (fun _ => checked.q₀)) t =
      checked.runFrom (Cfg.ofWords (input := y) checked.q₀ w) t from rfl)
  have hcomputed : V.ComputesInTime y [MultiTapeTM.indicator L y] (t₀ + 1 + t) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    have hinit : V.tm.initCfg y =
        (Cfg.ofWords (input := y) en (fun _ => [])).mapState Sum.inl := by
      simp [V, MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, Cfg.mapState]
    rw [hinit]
    change (whole.runFrom ((Cfg.ofWords (input := y) en (fun _ => [])).mapState Sum.inl)
      (t₀ + 1 + t)).state = none ∧
      (whole.runFrom ((Cfg.ofWords (input := y) en (fun _ => [])).mapState Sum.inl)
      (t₀ + 1 + t)).output = _
    rw [hwhole]
    simpa [Cfg.mapState] using And.intro hhalt hout
  apply hcomputed.mono
  have hlength := certSplitWord_length C c y
  have hpow : y.length + 1 ≤ (y.length + 1) ^ (c + 2) := by
    calc y.length + 1 = (y.length + 1) ^ 1 := (pow_one _).symm
         _ ≤ (y.length + 1) ^ (c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hzero : t₀ ≤ b * (A + 3) * (y.length + 1) ^ (c + 2) := by
    calc t₀ ≤ b * (A * (y.length + 1) ^ (c + 2) + y.length +
          (certSplitWord C c y).length + 1) := ht₀
         _ ≤ b * ((A + 3) * (y.length + 1) ^ (c + 2)) := by
           apply Nat.mul_le_mul_left
           rw [Nat.add_mul]
           omega
         _ = _ := by ring
  have ha := Nat.mul_le_mul_left a hpow
  have hone : 1 ≤ (y.length + 1) ^ (c + 2) := by omega
  have hT : T y.length ≤ (b * (A + 3) + a + 8) * T y.length := by
    calc T y.length = 1 * T y.length := (one_mul _).symm
         _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  calc t₀ + 1 + t ≤ (b * (A + 3) + a + 8) * (y.length + 1) ^ (c + 2) + T y.length := by
         rw [show (b * (A + 3) + a + 8) * (y.length + 1) ^ (c + 2) =
           b * (A + 3) * (y.length + 1) ^ (c + 2) + a * (y.length + 1) ^ (c + 2) +
             8 * (y.length + 1) ^ (c + 2) by ring]
         omega
       _ ≤ (b * (A + 3) + a + 8) * (y.length + 1) ^ (c + 2) +
           (b * (A + 3) + a + 8) * T y.length := Nat.add_le_add_left hT _
       _ = _ := (Nat.mul_add _ _ _).symm

/-- **The shell's projection identity**: projecting the shell's language along
certificates of the prescribed length recovers the outcome condition, the split of
`x ++ u` being unique because `n ↦ n + C·(n + 1)^c` is strictly increasing.

**Proof sketch.** Equal concatenations with prescribed certificate lengths have equal
parts: the shared split `Turing.append_split_unique` at
`Turing.certificateLength_strictMono`, the same lemma the plain Theorem 2.6 uses (wave-1
statement gate, round 1, finding 2). -/
theorem FinTM.certificateShell_proj (C c : ℕ) (out : List Bool → List Bool → List Bool) :
    {x : List Bool | ∃ u, u.length = C * (x.length + 1) ^ c ∧
        x ++ u ∈ {y : List Bool | ∃ x u, y = x ++ u ∧ u.length = C * (x.length + 1) ^ c ∧
          out x u = [true]}} =
      {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ out x u = [true]} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, x', u', he, hu', ho⟩
    obtain ⟨rfl, rfl⟩ := append_split_unique (f := fun n => C * (n + 1) ^ c)
      (certificateLength_strictMono C c) hu hu' he
    exact ⟨u, hu, ho⟩
  · rintro ⟨u, hu, ho⟩
    exact ⟨u, hu, x, u, rfl, hu, ho⟩

end Turing
