/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.CodeSimulator
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.InputWindow
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The interpreter core for nondeterministic codes

The code layer and the interpreter core that the universal NDTM and the diagonalizer of
`TCSlib.Complexity.Diagonalization.NTimeHierarchy` share ([AB09, Exercise 2.6]: a universal
NDTM; at linear overhead, decision CH34-Q8). Nondeterministic codes are interpreted through
their **replay machine** (user decision 3 of 2026-10-13): per code, the deterministic
three-work-tape serialization of the decoded machine's replay machine is computed, and the
deterministic step block (host H2) runs it at `k = 3`, unchanged, with the choice word on the
mirrored choice tape. No nondeterministic `Turing.MachineFormat`, no third parse layer, and no
change to `TCSlib.Complexity.TuringMachine.NDCodes`.

## Design

* **The bridge** `Turing.CodeNDTM.serialize_eq_tableBitsK` (proved) states the fixed ND
  serialization as its own header (the binary state count, the unary initial state) followed by
  the `false`-slice and `true`-slice tables in the generic `Turing.tableBitsK` layout. It is an
  identity of `Turing.CodeNDTM.serialize`, not of the serialization of any deterministic machine:
  no deterministic `k`-record serialization has two tables after one header.
* **The replay canonizer** `Turing.exists_replayCanonizer` keeps that header (the replay machine
  has the same states and initial state) and re-serializes the two tables into the replay
  machine's one table, at `3^4 = 81` records per state rather than `2·27 = 54`.
* **The interpreter core** `Turing.exists_ndInterpreterCore` is deterministic: the stream of
  choices is on a tape before it starts (guess first, user decision 1). Its prefix clause (time in
  the simulated branch's halting time) is kept with no consumer (user, 2026-10-17): the universal
  and the diagonalizer's mid-rung, at a guessed budget, use the total-time clause `C·(t + 1)`.

## Main definitions

No new definitions: the replay canonizer and the interpreter core are existential contracts.

## Main results

* `Turing.CodeNDTM.serialize_eq_tableBitsK` — the bridge (proved).
* `Turing.exists_replayCanonizer` — the per-code replay canonizer (sorried).
* `Turing.exists_ndInterpreterCore` — the interpreter core `R` (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, §1.4.1: machine codes and the universal machine;
  §2.1.2; Exercise 2.6: the universal NDTM.)
-/

namespace Turing

/-- **The ND serialization as two deterministic tables.** The fixed serialization of a coded
NDTM is the binary state count paired with the unary initial state followed by the `false`-slice
table and then the `true`-slice table, each in the generic `k`-record layout `Turing.tableBitsK`
at `k = 2`. This identity concerns `Turing.CodeNDTM.serialize` with its own header; it is not an
identity with `Turing.serializeK` of any deterministic machine. [AB09, §1.4]

**Proof sketch.** At two work tapes the generic table writer is `Turing.codeTable2Bits`
(`Turing.tableBitsK_two`); unfold the serialization over the choice bit. -/
theorem CodeNDTM.serialize_eq_tableBitsK (M : CodeNDTM) :
    M.serialize = pairEncode (Nat.bits M.numStates)
      (unaryFin M.tm.q₀ ++ (tableBitsK (M.tm.fixChoice false).tr ++
        tableBitsK (M.tm.fixChoice true).tr)) := by
  rw [tableBitsK_two, tableBitsK_two]
  simp [CodeNDTM.serialize, codeTable2Bits, NDTM.fixChoice, actionBits₂_eq_actionBitsK]

/-- **The per-code replay canonizer.** For every effective nondeterministic scheme `c` there is
a finite binary machine computing, from a code `α`, the fixed three-work-tape serialization
`Turing.serializeK` of the decoded machine's replay machine `Turing.NDTM.replayTM` (choice tape
last), within some time bound `T` of `|α|` alone. The bound is arbitrary: each code's universal
constant absorbs it. [AB09, §1.4: a code is mapped to its canonical description]

**Proof sketch.** The scheme's canonizer computes `α ↦ (c.decode α).serialize`
(`Turing.EffectiveNDMachineCode.canonizer_computes`). A primitive recursive list function `g`
maps it to `serializeK (c.decode α).tm.replayTM`: it copies the header, splits the two tables
into records by `Turing.codeSkipActionK`, and re-emits them in the order of
`Turing.workReadsK 3`, the choice read innermost (the blank and `false` reads both select the
`false` record). Each record is decoded and re-emitted in the three-tape field order of
`Turing.actionBitsK`: the input move, the first two work-tape fields, then the choice tape's
field `(none, +1)` as the third, then the output and the successor. Compile `g` by
`Turing.codePrim_machine` and compose (`Turing.FinTM.computesFunInTime_comp`; the canonizer's
output length is at most its time). -/
theorem exists_replayCanonizer (c : EffectiveNDMachineCode) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ),
      M.ComputesFunInTime (fun α => serializeK (c.decode α).tm.replayTM) T := by
  sorry

/-- Either header projection halts at the suffix with its selected component. The common
time is `16 |bits t| + 8 |α| + 25`; in particular it is independent of the suffix.

**Proof sketch.** Apply the published prefix contract to the first or second pair extractor.
Decode the inner pair with its round-trip lemma and expand only its published length formula. -/
private theorem ic_header_result (first : Bool) (α x : List Bool) (t : ℕ) :
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

/-- A bounded native-input computation can be silently captured with a first live return.
The completed transport contains the source's final output, even if it halted before the bound.

**Proof sketch.** Choose the first halt using the public first-halt lemma. The returning
embedding reaches its live anchor there, with exactly the configuration at the supplied bound. -/
private theorem ic_capture_return {k : ℕ} (M : FinTM Bool) (x : List Bool)
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

/-- Replaying any prefix of the stream on the bounded window gives the original branch's
control and output. The stream may be longer than the deadline.

**Proof sketch.** The replay theorem removes the extra choice tape. Input locality then
identifies the run on `x.take t` with the run on `x`, since the prefix has at most `t` bits. -/
private theorem ic_replay_window {k : ℕ} {S : Type} (N : NDTM k Bool S)
    (x s : List Bool) (t r : ℕ) (hs : t ≤ s.length) (hr : r ≤ t) :
    let d := N.replayTM.runFrom
      (NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0) r
    let e := N.runWith (s.take r) (N.initCfg x)
    d.state = e.state ∧ d.output = e.output := by
  obtain ⟨p, _, _, replay⟩ := N.replayTM_runFrom (N.initCfg (x.take t)) s r
    (hr.trans hs)
  have locality := N.runWith_initCfg_take x t (s.take r) (by
    rw [List.length_take]
    omega)
  dsimp only
  rw [replay, NDTM.withChoiceTape_state, NDTM.withChoiceTape_output]
  exact ⟨locality.1, locality.2.2.2.2⟩

/-- The replay canonizer can be called through the clean installation interface, with a
cost depending on the code alone. The installed word is the entire replay serialization.

**Proof sketch.** Take the canonizer from its gated statement and feed its computation contract
to the public install-call theorem. Both the argument and its result depend only on the code. -/
private theorem ic_table_call (c : EffectiveNDMachineCode) :
    ∃ (M : FinTM Bool) (entry done : M.State) (cost : List Bool → ℕ), 0 < M.k ∧
      ∀ x α : List Bool, ∃ T ≤ cost α, 0 < T ∧
        (∀ u, 0 < u → u < T →
          (M.tm.runFrom
            (Cfg.ofWords (input := x) entry (stateWord M.k α)) u).state ≠ some done) ∧
        M.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord M.k α)) T =
          Cfg.ofWords done (stateWord M.k (serializeK (c.decode α).tm.replayTM)) := by
  obtain ⟨F, τ, computes⟩ := exists_replayCanonizer c
  obtain ⟨M, entry, done, a, positive, installs⟩ :=
    FinTM.exists_installCallTM F _ τ computes
  exact ⟨M, entry, done,
    fun α => a * (τ α.length + α.length + (serializeK (c.decode α).tm.replayTM).length + 1),
    positive, installs⟩

/-- A header projection has a silent first live return, with its selected word on the capture
tape and the native head at the suffix. Unselected tapes other than the capture retain their
contents and heads; no description of the projection's final scratch bank is needed.

**Proof sketch.** Use the header's bounded halt and the returning capture lemma. Project the
capture, input-position, output and unselected-tape equations at that return. -/
private theorem ic_header_capture (first : Bool) (K : ℕ) (α x : List Bool) (t : ℕ)
    (ι : Fin (prefixCanonTM
      (if first then FinTM.pairExtractTM true false else FinTM.pairExtractTM false true)).k ↪ Fin K)
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
  obtain ⟨halt, word, pos⟩ := ic_header_result first α x t
  obtain ⟨T, bound, run, cut⟩ := ic_capture_return M z ι cap hcap tapes heads out
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

/-- A serialization installed at cell zero can be redistributed into the interpreter's table
and empty-output summary. The return time depends on the serialized machine alone; all other
tapes, the native input head, and the physical output retain their frame.

**Proof sketch.** Specialize the shared layout contract to the state-count header and the
machine's unary initial state. Its shifted unary buffer is the empty-output summary, since
its cell at zero reads the blank cell at offset minus two. -/
private theorem ic_layout_call (K : ℕ) (src tbl sm : Fin K) (hst : src ≠ tbl)
    (hss : src ≠ sm) (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM K Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {k n : ℕ} (M : MultiTapeTM k Bool (Fin (n + 1))),
        ∃ T ≤ C * ((serializeK M).length + 1),
          ∀ {z : List Bool} (d : Cfg K Bool Q z),
            d.state = some entry →
            d.workTapes src = FinTM.bufferTape (serializeK M) →
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
  have word : serializeK M =
      pairEncode n.bits ((List.replicate (M.q₀ : ℕ) true ++ [false]) ++ tableBitsK M.tr) := by
    rw [serializeK_eq, unaryFin_eq]
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

/-- The installed table and empty-output summary, together with the mirrored initial tapes,
represent the replay machine's start with its entire choice stream on the last mirrored tape.

**Proof sketch.** Assemble the six fields of the public representation equivalence. The replay
start has the nondeterministic machine's initial state and empty output; its work tapes are the
blank initial bank followed by the supplied stream. -/
private theorem ic_replay_rep {k n : ℕ} (N : NDTM k Bool (Fin (n + 1))) (x s : List Bool)
    (d : Cfg (k + 1 + 2) Bool (Σ key, StepBlock.Ph (k + 1) key) x)
    (hin : d.inputPos.val = 1)
    (hbank : ∀ i : Fin (k + 1),
      d.workTapes (Fin.castAdd 2 i) =
        Fin.lastCases (FinTM.bufferTape s) (fun _ _ => none) i ∧
      d.workTapePos (Fin.castAdd 2 i) = Fin.lastCases 0 (fun _ => 0) i)
    (htbl : d.workTapes (StepBlock.tableTape (k + 1)) =
      FinTM.bufferTape (tableBitsK N.replayTM.tr))
    (hsm : d.workTapes (StepBlock.summaryTape (k + 1)) =
      StepBlock.summaryCells none (unaryFin N.q₀))
    (htblp : d.workTapePos (StepBlock.tableTape (k + 1)) = 0)
    (hsmp : d.workTapePos (StepBlock.summaryTape (k + 1)) = 0) :
    StepBlock.Rep N.replayTM.tr
      (NDTM.withChoiceTape (N.initCfg x) (FinTM.bufferTape s) 0) d := by
  apply StepBlock.Rep_iff.mpr
  refine ⟨?_, ?_, htbl, ?_, htblp, hsmp⟩
  · rw [NDTM.withChoiceTape_inputPos, NDTM.initCfg_eq, Cfg.init_inputPos]
    exact Fin.ext hin
  · intro i
    have tapes : (N.initCfg x).workTapes = fun _ _ => none := by
      funext j a
      rw [NDTM.initCfg_eq, Cfg.init_workTapes]
    have heads : (N.initCfg x).workTapePos = fun _ => 0 := by
      funext j
      rw [NDTM.initCfg_eq, Cfg.init_workTapePos]
    obtain ⟨htape, hhead⟩ := hbank i
    refine ⟨?_, ?_⟩
    · funext a
      rw [htape, NDTM.withChoiceTape_workTapes, tapes]
    · rw [hhead, NDTM.withChoiceTape_workTapePos, heads]
  · simpa only [NDTM.withChoiceTape_output, NDTM.withChoiceTape_state, NDTM.initCfg_eq,
      Cfg.init_output, Cfg.init_state, Option.map_some, Option.getD_some,
      StepBlock.outputSummary_nil] using hsm

/-- Removing the doubled header and its separator from a paired input leaves its suffix.

**Proof sketch.** Express the pair as the empty-suffix header appended to the suffix. The
published length formula gives exactly the number of symbols to drop. -/
private theorem ic_input_suffix (u x : List Bool) :
    (pairEncode u x).drop (2 * u.length + 2) = x := by
  have split : pairEncode u x = pairEncode u [] ++ x := by
    rw [pairEncode_eq, pairEncode_eq, List.append_nil]
  have width : (pairEncode u []).length = 2 * u.length + 2 := by
    rw [length_pairEncode, List.length_nil, Nat.add_zero]
  rw [split, ← width, List.drop_left]

/-- At the end of the header passes the shared copier produces exactly the bounded suffix
window on an initially blank tape. Tapes other than the window and counter are framed, as are
their heads, and the cost has no dependence on the uncopied suffix.

**Proof sketch.** Identify the suffix by dropping the encoded header, and read the binary
counter through its published value equation. Project the copier's two tape updates; the
blank destination outside the copied interval agrees with the window buffer's blank cells. -/
private theorem ic_window_call (K : ℕ) (j dst : Fin K) (hjd : j ≠ dst) :
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
  simp only [ic_input_suffix, value] at bound hin htapes hheads
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

/-- From a represented replay start, the hosted loop has both time bounds measured against
the original nondeterministic branch. Its exit and summary cell give that branch's halting
status and output, and neither loop exit occurs earlier, for either boundary tag.

**Proof sketch.** Apply the existing hosted-loop contract with the untouched binary counter.
The initial boundary tag is valid even for an empty window. Replay and input locality transfer
both the endpoint semantics and every early-halting hypothesis to the original input. Finally
read the summary cell through the hosted-loop reading theorem. -/
private theorem ic_loop_replay {n : ℕ} (N : NDTM 2 Bool (Fin (n + 1)))
    (x s : List Bool) (t : ℕ) (hs : t ≤ s.length)
    (d : Cfg 5 Bool (Σ key, StepBlock.Ph 3 key) (x.take t))
    (entry : d.state = some (StepBlock.exit 3 true))
    (rel : StepBlock.Rep N.replayTM.tr
      (NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0) d)
    (z : List Bool) (p : Fin (z.length + 2)) :
    let start := vhostCfg
      (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape (Nat.bits t)) 0) true p []
    let branch := N.runWith (s.take t) (N.initCfg x)
    ∃ (T : ℕ) (e : Cfg 5 Bool (Σ key, StepBlock.Ph 3 key) (x.take t))
      (ct' : ℤ → Option Bool) (b' : Bool),
      T ≤ t * (50 * ((tableBitsK N.replayTM.tr).length + 1)) +
        4 * t + 2 * (Nat.bits t).length + 2 ∧
      (∀ r ≤ t, (N.runWith (s.take r) (N.initCfg x)).state = none →
        T ≤ r * (50 * ((tableBitsK N.replayTM.tr).length + 1)) +
          4 * r + 2 * (Nat.bits t).length) ∧
      e.output = d.output ∧
      (StepBlock.hostedLoopTM 3).runFrom start T =
        vhostCfg (counterLoopCfg
          (some (if branch.state.isSome then .done else .escape)) e ct' 0) b' p [] ∧
      ((StepBlock.hostedLoopTM 3).runFrom start T).workTapeSymbols
        (vhostBank (StepBlock.summaryTape 3).castSucc) = StepBlock.outputSummary branch.output ∧
      ∀ u < T, ∀ tag,
        ((StepBlock.hostedLoopTM 3).runFrom start u).state ≠ some (.done, tag) ∧
        ((StepBlock.hostedLoopTM 3).runFrom start u).state ≠ some (.escape, tag) := by
  dsimp only
  let c₀ := NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0
  have live : c₀.state ≠ none := by
    rw [NDTM.withChoiceTape_state, NDTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have tag : FinTM.VirtualTag c₀.inputPos true := by
    rw [FinTM.VirtualTag_iff, NDTM.withChoiceTape_inputPos, NDTM.initCfg_eq, Cfg.init_inputPos]
    constructor
    · intro h
      norm_num at h
    · intro _
      rfl
  have value : Nat.ofDigits 2 ((Nat.bits t).map Bool.toNat) = t :=
    (counterValue_eq _).symm.trans (counterValue_bits t)
  obtain ⟨T, e, ct', b', bound, early, represented, output, _, _, run, cut⟩ :=
    StepBlock.hostedLoopTM_run N.replayTM c₀ live d entry rel (Nat.bits t)
      (FinTM.bufferTape (Nat.bits t)) 0 (by intros; rw [zero_add]) t value true tag p []
  have semantic := ic_replay_window N x s t t hs le_rfl
  have reading := (StepBlock.hostedLoop_read N.replayTM.tr (N.replayTM.runFrom c₀ t)
    e represented
    (if (N.runWith (s.take t) (N.initCfg x)).state.isSome then .done else .escape)
    ct' 0 b' p []).2.2.2
  refine ⟨T, e, ct', b', bound, ?_, output, ?_, ?_, cut⟩
  · intro r hr halted
    apply early r hr
    exact (ic_replay_window N x s t r hs hr).1.trans halted
  · rw [semantic.1] at run
    exact run
  · rw [run, semantic.1]
    exact reading.trans (congrArg StepBlock.outputSummary semantic.2)

/-- The interpreter's final one-step read, with live verdict states. The entry bit records
whether the simulated machine halted; the accepting verdict additionally requires the summary
cell to contain `some true`. This consumer-specific leaf supplies the two live verdicts that
the hosted loop leaves to its caller; it is not another loop or dispatch host. -/
private def ic_verdictTM (K : ℕ) (summary : Fin K) : MultiTapeTM K Bool (Bool ⊕ Bool) where
  q₀ := Sum.inl false
  tr := fun q _ cells =>
    let verdict := match q with
      | Sum.inl halted => halted && decide (cells summary = some true)
      | Sum.inr result => result
    ⟨0, fun _ => (none, 0), none, some (Sum.inr verdict)⟩

/-- The verdict leaf reaches the correct live verdict in exactly one step, before which
neither verdict has been reached. The summary characterization recognizes precisely the
singleton accepting output.

**Proof sketch.** The only strict prefix of one step is the entry configuration, whose state
is in the other sum constructor. For the endpoint use the live-step and action-state equations
and the public characterization of an accepting summary. -/
private theorem ic_verdictTM_run {K : ℕ} (summary : Fin K) {z : List Bool}
    (d : Cfg K Bool (Bool ⊕ Bool) z) (halted : Bool) (out : List Bool)
    (hd : d.state = some (Sum.inl halted))
    (hsummary : d.workTapeSymbols summary = StepBlock.outputSummary out) :
    ((ic_verdictTM K summary).runFrom d 1).state =
      some (Sum.inr (decide (halted = true ∧ out = [true]))) ∧
      ∀ u < 1, ∀ verdict : Bool,
        ((ic_verdictTM K summary).runFrom d u).state ≠ some (Sum.inr verdict) := by
  constructor
  · rw [show 1 = 0 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, MultiTapeTM.step_of_some hd, Action.apply_state]
    simp only [ic_verdictTM, hsummary]
    congr 2
    cases halted <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
      false_and, decide_false, true_and, StepBlock.outputSummary_true]
  · intro u hu verdict
    have zero : u = 0 := by omega
    rw [zero, MultiTapeTM.runFrom_zero, hd]
    exact fun h => Sum.noConfusion (Option.some.inj h)

/-- The two phases of the interpreter's loop and final verdict read. -/
private def ic_loopPh : Bool → Type
  | false => CounterLoopState (Σ key, StepBlock.Ph 3 key) × Bool
  | true => Bool ⊕ Bool

/-- Each of the interpreter's two final phases has a finite control type. -/
private instance ic_loopPh_fintype (phase : Bool) : Fintype (ic_loopPh phase) := by
  cases phase <;> dsimp only [ic_loopPh] <;> infer_instance

/-- The existing hosted loop followed by the consumer's one-step verdict leaf. -/
private def ic_loopPiece (phase : Bool) : MultiTapeTM 7 Bool (ic_loopPh phase) :=
  match phase with
  | false => StepBlock.hostedLoopTM 3
  | true => ic_verdictTM 7 (vhostBank (StepBlock.summaryTape 3).castSucc)

/-- The loop's two exits dispatch to the corresponding verdict entry, independently of their
arrival tag. Verdict states stay live; all dispatch is performed by the shared phase host. -/
private def ic_loopRedirect : (phase : Bool) → ic_loopPh phase → Option (Σ i, ic_loopPh i)
  | false, (.done, _) => some ⟨true, Sum.inl false⟩
  | false, (.escape, _) => some ⟨true, Sum.inl true⟩
  | false, _ => none
  | true, Sum.inl _ => none
  | true, Sum.inr result => some ⟨true, Sum.inr result⟩

/-- The interpreter's loop and verdict stages assembled by the public phase host. -/
private def ic_loopHost : MultiTapeTM 7 Bool (Σ i, ic_loopPh i) :=
  phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect

/-- The loop-to-verdict assembly adds two steps and preserves the first-verdict guarantee.
Both boundary tags and both loop exits are handled by the same machine.

**Proof sketch.** The shared phase-host theorem transports the loop through its first exit,
then performs one silent dispatch to the verdict entry. Its theorem applied to the verdict
leaf transports the final read. Before dispatch all states carry the loop tag; at dispatch
the leaf is still at an entry, so neither live verdict has occurred. -/
private theorem ic_loopHost_run {z : List Bool}
    (d : Cfg 7 Bool (CounterLoopState (Σ key, StepBlock.Ph 3 key) × Bool) z)
    (T : ℕ) (halted tag : Bool) (out : List Bool)
    (exit : ((StepBlock.hostedLoopTM 3).runFrom d T).state =
      some ((if halted then .escape else .done), tag))
    (read : ((StepBlock.hostedLoopTM 3).runFrom d T).workTapeSymbols
      (vhostBank (StepBlock.summaryTape 3).castSucc) = StepBlock.outputSummary out)
    (cut : ∀ u < T, ∀ b,
      ((StepBlock.hostedLoopTM 3).runFrom d u).state ≠ some (.done, b) ∧
      ((StepBlock.hostedLoopTM 3).runFrom d u).state ≠ some (.escape, b)) :
    (ic_loopHost.runFrom (d.mapState (Sigma.mk false)) (T + 2)).state =
      some ⟨true, Sum.inr (decide (halted = true ∧ out = [true]))⟩ ∧
      ∀ u < T + 2, ∀ verdict : Bool,
        (ic_loopHost.runFrom (d.mapState (Sigma.mk false)) u).state ≠
          some ⟨true, Sum.inr verdict⟩ := by
  let e := (StepBlock.hostedLoopTM 3).runFrom d T
  have guard : ∀ u < T, ∀ q,
      ((ic_loopPiece false).runFrom d u).state = some q → ic_loopRedirect false q = none := by
    intro u hu q hq
    rcases q with ⟨q, b⟩
    cases q with
    | dec q => rfl
    | body q => rfl
    | done => exact False.elim ((cut u hu b).1 hq)
    | escape => exact False.elim ((cut u hu b).2 hq)
  have redirect : ic_loopRedirect false ((if halted then .escape else .done), tag) =
      some ⟨true, Sum.inl halted⟩ := by
    cases halted <;> rfl
  obtain ⟨hpre, dispatch⟩ := phaseHostTM_run ic_loopPiece
    ⟨false, (.dec .run, true)⟩ ic_loopRedirect false d e T rfl
    ((if halted then .escape else .done), tag) exit ⟨true, Sum.inl halted⟩ redirect guard
  let leaf : Cfg 7 Bool (Bool ⊕ Bool) z := e.mapState (fun _ => Sum.inl halted)
  have entry : leaf.state = some (Sum.inl halted) := by
    rw [Cfg.mapState_state, exit, Option.map_some]
  have cell : leaf.workTapeSymbols (vhostBank (StepBlock.summaryTape 3).castSucc) =
      StepBlock.outputSummary out := by
    rw [Cfg.workTapeSymbols_eq, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      ← Cfg.workTapeSymbols_eq]
    exact read
  obtain ⟨verdict, _⟩ := ic_verdictTM_run
    (vhostBank (StepBlock.summaryTape 3).castSucc) leaf halted out entry cell
  have leafGuard : ∀ u < 1, ∀ q,
      ((ic_loopPiece true).runFrom leaf u).state = some q → ic_loopRedirect true q = none := by
    intro u hu q hq
    have zero : u = 0 := by omega
    rw [zero, MultiTapeTM.runFrom_zero, entry] at hq
    cases Option.some.inj hq
    rfl
  have leafRun := (phaseHostTM_run ic_loopPiece ⟨false, (.dec .run, true)⟩
    ic_loopRedirect true leaf ((ic_loopPiece true).runFrom leaf 1) 1 rfl
    (Sum.inr (decide (halted = true ∧ out = [true]))) verdict
    ⟨true, Sum.inr (decide (halted = true ∧ out = [true]))⟩ rfl leafGuard).1 1 le_rfl
  have seam : e.mapState (fun _ => (⟨true, Sum.inl halted⟩ : Σ i, ic_loopPh i)) =
      leaf.mapState (Sigma.mk true) := by
    apply Cfg.ext <;> (try funext i) <;> (try funext p) <;>
      simp only [leaf, Cfg.mapState_state, Cfg.mapState_inputPos,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
        Option.map_map, Function.comp_def]
  constructor
  · change ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom
      (d.mapState (Sigma.mk false)) (T + 2)).state = _
    rw [show T + 2 = (T + 1) + 1 by omega, MultiTapeTM.runFrom_add, dispatch]
    have final : ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom
        (leaf.mapState (Sigma.mk true)) 1).state =
        some ⟨true, Sum.inr (decide (halted = true ∧ out = [true]))⟩ := by
      rw [leafRun, Cfg.mapState_state, verdict, Option.map_some]
    rw [← seam] at final
    exact final
  · intro u hu result
    by_cases before : u ≤ T
    · change ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom
        (d.mapState (Sigma.mk false)) u).state ≠ _
      rw [hpre u before, Cfg.mapState_state]
      cases hs : ((ic_loopPiece false).runFrom d u).state with
      | none => exact Option.noConfusion
      | some q =>
        intro bad
        have impossible := congrArg Sigma.fst (Option.some.inj bad)
        exact Bool.noConfusion impossible
    · have atDispatch : u = T + 1 := by omega
      change ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom
        (d.mapState (Sigma.mk false)) u).state ≠ _
      rw [atDispatch, dispatch, Cfg.mapState_state, exit, Option.map_some]
      intro bad
      have impossible := (Sigma.mk.inj (Option.some.inj bad)).2
      cases impossible

/-- Once startup has produced the represented replay start, one fixed finite-control machine
runs the branch and reaches its correct first verdict. The total and prefix costs include the
two final dispatch/read steps.

**Proof sketch.** Use the semantic hosted-loop contract, extract its exit state through the
configuration equations, and apply the loop-to-verdict assembly. Negated liveness is exactly
halting, so the resulting Boolean verdict is the target's acceptance predicate. -/
private theorem ic_replay_tail {n : ℕ} (N : NDTM 2 Bool (Fin (n + 1)))
    (x s : List Bool) (t : ℕ) (hs : t ≤ s.length)
    (d : Cfg 5 Bool (Σ key, StepBlock.Ph 3 key) (x.take t))
    (entry : d.state = some (StepBlock.exit 3 true))
    (rel : StepBlock.Rep N.replayTM.tr
      (NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0) d)
    (z : List Bool) (p : Fin (z.length + 2)) :
    let start := vhostCfg
      (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape (Nat.bits t)) 0) true p []
    let branch := N.runWith (s.take t) (N.initCfg x)
    ∃ T,
      T ≤ t * (50 * ((tableBitsK N.replayTM.tr).length + 1)) +
        4 * t + 2 * (Nat.bits t).length + 4 ∧
      (∀ r ≤ t, (N.runWith (s.take r) (N.initCfg x)).state = none →
        T ≤ r * (50 * ((tableBitsK N.replayTM.tr).length + 1)) +
          4 * r + 2 * (Nat.bits t).length + 2) ∧
      (ic_loopHost.runFrom (start.mapState (Sigma.mk false)) T).state =
        some ⟨true, Sum.inr (decide (branch.state = none ∧ branch.output = [true]))⟩ ∧
      ∀ u < T, ∀ verdict : Bool,
        (ic_loopHost.runFrom (start.mapState (Sigma.mk false)) u).state ≠
          some ⟨true, Sum.inr verdict⟩ := by
  dsimp only
  obtain ⟨T, e, ct', b', bound, early, _, run, summary, cut⟩ :=
    ic_loop_replay N x s t hs d entry rel z p
  let branch := N.runWith (s.take t) (N.initCfg x)
  have state := congrArg Cfg.state run
  rw [vhostCfg_state, counter_cfg_eq _ e, Option.map_some] at state
  have exit : ((StepBlock.hostedLoopTM 3).runFrom
      (vhostCfg (counterLoopCfg (some (.dec .run)) d
        (FinTM.bufferTape (Nat.bits t)) 0) true p []) T).state =
      some ((if !branch.state.isSome then .escape else .done), b') := by
    cases hb : branch.state.isSome <;>
      simpa only [branch, hb, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] using state
  obtain ⟨correct, first⟩ := ic_loopHost_run _ T (!branch.state.isSome) b' branch.output
    exit summary cut
  refine ⟨T + 2, by omega, ?_, ?_, first⟩
  · intro r hr halted
    have h := early r hr halted
    omega
  · simpa only [Option.not_isSome, Option.isNone_iff_eq_none] using correct

/-- A single per-code constant absorbs both the full-deadline ledger and the early-halting
ledger. Fixed dispatch costs and the serialization layout cost belong in the startup constant.

**Proof sketch.** For the full deadline, bound the binary width and window length by the
deadline. For early halting, bound the window by the input length and bound each coefficient
by the chosen constant. No comparison of the early halting time with the deadline is needed
for the second arithmetic inequality. -/
private theorem ic_time_ledger (a b w L t x r : ℕ) :
    let C := a + b + w + 50 * (L + 1) + 10
    (a + (b + 4) * (Nat.bits t).length + w * (min t x + 1) +
        (50 * (L + 1) + 4) * t + 2 ≤ C * (t + 1)) ∧
      (a + (b + 4) * (Nat.bits t).length + w * (min t x + 1) +
        (50 * (L + 1) + 4) * r ≤ C * (r + x + (Nat.bits t).length + 1)) := by
  dsimp only
  constructor
  · calc
      _ ≤ a + (b + 4) * t + w * (t + 1) + (50 * (L + 1) + 4) * t + 2 := by
        gcongr
        · exact length_bits_le_self t
        · exact min_le_left t x
      _ ≤ _ := by
        ring_nf
        omega
  · calc
      _ ≤ a + (b + 4) * (Nat.bits t).length + w * (x + 1) +
          (50 * (L + 1) + 4) * r := by
        gcongr
        exact min_le_right t x
      _ = a + w + (b + 4) * (Nat.bits t).length + w * x +
          (50 * (L + 1) + 4) * r := by ring
      _ ≤ (a + b + w + 50 * (L + 1) + 10) +
          (a + b + w + 50 * (L + 1) + 10) * (Nat.bits t).length +
          (a + b + w + 50 * (L + 1) + 10) * x +
          (a + b + w + 50 * (L + 1) + 10) * r := by
        gcongr ?_ + ?_ * _ + ?_ * _ + ?_ * _ <;> omega
      _ = _ := by ring

/-- Composing a verified segment with a verified next phase through the public seam: the
endpoint, its control state, and the inherited first return of the phase's exit, in one step.

**Proof sketch.** The general-configuration seam run and its inherited first-return cut,
with the endpoint state projected through the state renaming. -/
private theorem ic_seam_step {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] {x : List Bool}
    (A : MultiTapeTM k Bool S₁) (exit₁ : S₁) (B : MultiTapeTM k Bool S₂) (entry₂ exit₂ : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₂ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : A.runFrom c₀ T₁ = c₁) (hx₁ : c₁.state = some exit₁)
    (hcut₁ : ∀ t < T₁, (A.runFrom c₀ t).state ≠ some exit₁)
    (h₂ : B.runFrom (c₁.mapState fun _ => entry₂) T₂ = c₂)
    (hx₂ : c₂.state = some exit₂)
    (hcut₂ : ∀ t < T₂, (B.runFrom (c₁.mapState fun _ => entry₂) t).state ≠ some exit₂) :
    (seamCompTM A exit₁ B entry₂).runFrom (c₀.mapState Sum.inl) (T₁ + 1 + T₂) =
        c₂.mapState (Sum.inr : S₂ → S₁ ⊕ S₂) ∧
      (c₂.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).state = some (Sum.inr exit₂) ∧
      ∀ t < T₁ + 1 + T₂,
        ((seamCompTM A exit₁ B entry₂).runFrom (c₀.mapState Sum.inl) t).state ≠
          some (Sum.inr exit₂) := by
  refine ⟨seamCompTM_run_ofCfg A exit₁ B entry₂ h₁ hx₁ hcut₁ h₂, ?_,
    seamCompTM_firstReturn_ofCfg A exit₁ B entry₂ exit₂ h₁ hx₁ hcut₁ h₂ hx₂ hcut₂⟩
  rw [Cfg.mapState_state, hx₂, Option.map_some]

/-- The interpreter's native-input rewind leaf: one unconditional left move, a left scan to
the input's left blank, one right step, and a live parking state at which a seam can dispatch.
It is the two-`controlAction`-state input-rewind discipline with an explicit live exit; it
moves no work head and writes nothing. -/
private def ic_rewindLeafTM (k : ℕ) : MultiTapeTM k Bool (Fin 3) where
  q₀ := 0
  tr := fun q inp _ =>
    if q = 0 then FinTM.controlAction .neg (some 1)
    else if q = 1 then
      match inp with
      | some _ => FinTM.controlAction .neg (some 1)
      | none => FinTM.controlAction .pos (some 2)
    else FinTM.controlAction .zero (some 2)

/-- The leaf's scanning trajectory: from the scanning state at input position `j ≤ |x|`, the
parking state is reached at exactly `j + 1`, with only the control and the input head changed,
and the state stays the scanning one strictly before.

**Proof sketch.** Induct on the position. At zero the input symbol is the left blank, so one
right move parks. At a successor the symbol exists; one left move reduces the position. -/
private theorem ic_rewind_scan {k : ℕ} {x : List Bool} :
    ∀ (j : ℕ) (cfg : Cfg k Bool (Fin 3) x), cfg.state = some 1 →
      cfg.inputPos.val = j → j ≤ x.length →
      (ic_rewindLeafTM k).runFrom cfg (j + 1) =
          { cfg with state := some 2, inputPos := 1 } ∧
        ∀ u ≤ j, ((ic_rewindLeafTM k).runFrom cfg u).state = some 1 := by
  intro j
  induction j with
  | zero =>
    intro cfg hs hj _
    have hz : cfg.inputPos = 0 := Fin.ext hj
    have hstep : (ic_rewindLeafTM k).step cfg =
        { cfg with state := some 2, inputPos := moveInputPos cfg.inputPos .pos } := by
      rw [MultiTapeTM.step_of_some hs, Cfg.inputSymbol_of_zero hz]
      simp only [ic_rewindLeafTM, Fin.reduceEq, ↓reduceIte]
      exact FinTM.controlAction_apply cfg .pos (some 2)
    have hm : moveInputPos cfg.inputPos .pos = 1 := by
      apply Fin.ext
      rw [hz, moveInputPos_pos_of_ne_right _ (by simp)]
      simp
    refine ⟨?_, ?_⟩
    · show (ic_rewindLeafTM k).step cfg = _
      rw [hstep, hm]
    · intro u hu
      obtain rfl : u = 0 := by omega
      exact hs
  | succ j ih =>
    intro cfg hs hj hlen
    have hsym : cfg.inputSymbol = some (x[j]'(by omega)) :=
      inputSymbolInner j (by omega) (by omega)
    have hstep : (ic_rewindLeafTM k).step cfg =
        { cfg with state := some 1, inputPos := moveInputPos cfg.inputPos .neg } := by
      rw [MultiTapeTM.step_of_some hs, hsym]
      simp only [ic_rewindLeafTM, Fin.reduceEq, ↓reduceIte]
      exact FinTM.controlAction_apply cfg .neg (some 1)
    have hpos : (moveInputPos cfg.inputPos .neg).val = j := by
      rw [FinTM.moveInputPos_neg_val]
      omega
    obtain ⟨hrun, hstay⟩ := ih ((ic_rewindLeafTM k).step cfg)
      (by rw [hstep]) (by rw [hstep]; exact hpos) (by omega)
    refine ⟨?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step, hrun, hstep]
    · intro u hu
      cases u with
      | zero => exact hs
      | succ u =>
        rw [MultiTapeTM.runFrom_succ_eq_step]
        exact hstay u (by omega)

/-- The leaf's complete run: from its entry at any positive input position `p`, it parks at
exactly `p + 1` with the input head at `1`, every work tape, work head and the output
unchanged, and the parking state is not visited earlier.

**Proof sketch.** The unconditional first left move lands the scan at `p − 1 ≤ |x|`; the
scanning trajectory parks after `p` more steps. Strictly before, the state is the entry or the
scanning one. -/
private theorem ic_rewind_leaf_run {k : ℕ} {x : List Bool} (cfg : Cfg k Bool (Fin 3) x)
    (hs : cfg.state = some 0) (hp : 1 ≤ cfg.inputPos.val) :
    (ic_rewindLeafTM k).runFrom cfg (cfg.inputPos.val + 1) =
        { cfg with state := some 2, inputPos := 1 } ∧
      ∀ u < cfg.inputPos.val + 1,
        ((ic_rewindLeafTM k).runFrom cfg u).state ≠ some 2 := by
  have hstep : (ic_rewindLeafTM k).step cfg =
      { cfg with state := some 1, inputPos := moveInputPos cfg.inputPos .neg } := by
    rw [MultiTapeTM.step_of_some hs]
    simp only [ic_rewindLeafTM, ↓reduceIte]
    exact FinTM.controlAction_apply cfg .neg (some 1)
  have hval : (moveInputPos cfg.inputPos .neg).val = cfg.inputPos.val - 1 :=
    FinTM.moveInputPos_neg_val cfg.inputPos
  have hlen : cfg.inputPos.val - 1 ≤ x.length := by
    have := cfg.inputPos.isLt
    omega
  obtain ⟨hrun, hstay⟩ := ic_rewind_scan (cfg.inputPos.val - 1) ((ic_rewindLeafTM k).step cfg)
    (by rw [hstep]) (by rw [hstep]; exact hval) hlen
  have htime : cfg.inputPos.val + 1 = 1 + (cfg.inputPos.val - 1 + 1) := by omega
  refine ⟨?_, ?_⟩
  · rw [htime, MultiTapeTM.runFrom_add]
    show (ic_rewindLeafTM k).runFrom ((ic_rewindLeafTM k).step cfg) _ = _
    rw [hrun, hstep]
  · intro u hu
    cases u with
    | zero =>
      rw [MultiTapeTM.runFrom_zero, hs]
      simp
    | succ u =>
      rw [MultiTapeTM.runFrom_succ_eq_step, hstay u (by omega)]
      simp

/-- The install call, embedded silently on selected host tapes and wrapped in the release
adapter, so that its first re-arrival at the installed seam is a positive event even when the
call's entry and exit controls coincide. The embedded run carries one clean seam to the other;
unselected tapes hold their frame throughout.

**Proof sketch.** The silent embedding transports the call's run between the transported
seams; the release adapter's positive lockstep makes the first arrival at the exit control
strictly positive, and the call's interior cut excludes it earlier. -/
private theorem ic_install_phase {K : ℕ} (CI : FinTM Bool) (entryI doneI : CI.State)
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

/-- **The interpreter core for nondeterministic codes** `R` (deterministic; shared by the
universal NDTM and the diagonalizer's mid-rung). For every effective nondeterministic scheme
`c` there is one finite machine `R`, uniform over codes, with `K` work tapes, a designated stream
tape `j`, an entry state and two distinct verdict states `accept ≠ reject`, such that for every
code `α` there is a constant `C` with the following property. Start `R` at `entry` on the
native input `z = ⟨⟨bits t, α⟩, x⟩` (input head on its first symbol), with a stream `s` of
length at least `t` on tape `j` from cell `0`, every other tape blank, every head at `0`, and
empty output. Let `e` be the coded machine's branch on `x` along `s.take t`. Then `R` reaches
`accept` if `e` has halted with output exactly `[true]`, and `reject` otherwise, at a time `T`
with no verdict earlier, where:
* `T ≤ C·(t + 1)` in every case, with no `|x|` term;
* `T ≤ C·(t' + |x| + |bits t| + 1)` whenever the branch along `s.take t'` has already halted,
  for `t' ≤ t` (**the prefix clause**: the cost of a branch that halts early is linear in its
  own length, plus the window copy and the counter width).
[AB09, Exercise 2.6, §1.4.1: the universal machine, here for one fixed choice word]

**Proof sketch.** Per-code startup: parse the nested header, leaving `bits t` on a counter
tape; install the replay serialization of `Turing.exists_replayCanonizer` by
`Turing.FinTM.exists_installCallTM` with the unary initial state; copy the input window
`x.take t` onto a buffer by `Turing.exists_inputWindowCopyTM` (cost `O(min(t, |x|) + |bits t|)`)
and rewind it. Then the deterministic clocked interpreter loop at three work tapes, the stream
as the mirrored choice tape: the counter loop over H2's step block hosted by Z1 on the window,
from the replay machine's represented start with the stream installed, over the counter
`bits t` (`Turing.StepBlock.hostedLoopTM_run`, host H2-L in `Build/StepBlockLoop`; the
counter's value is `Turing.counterValue_bits`). Each round is one step of the replay machine and
costs at most a per-code constant (H2's `50·(|table| + 1)`), and the counter costs at most
`4r + 2|bits t|` over `r` rounds; when the simulated machine halts by `t'`, the loop escapes
within `t'·50·(|table| + 1) + 4t' + 2|bits t|` (the contract's early-escape bound), which gives
the prefix clause. The verdict reads H2's output summary at the live exits
(`Turing.StepBlock.hostedLoop_read`). The replay lemma `Turing.NDTM.replayTM_runFrom` identifies
the simulated run with the branch along `s.take t` on the window, and input locality
(`Turing.NDTM.runWith_initCfg_take`) with the branch on `x`. -/
theorem exists_ndInterpreterCore (c : EffectiveNDMachineCode) :
    ∃ (K : ℕ) (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (R : MultiTapeTM K Bool Q)
      (j : Fin K) (entry accept reject : Q), accept ≠ reject ∧
      ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ) (s : List Bool), t ≤ s.length →
        let z := pairEncode (pairEncode (Nat.bits t) α) x
        let N := (c.decode α).toFinNDTM
        let start : Cfg K Bool Q z :=
          ⟨some entry, 1, fun i => if i = j then FinTM.bufferTape s else fun _ => none,
            fun _ => 0, []⟩
        let e := N.tm.runWith (s.take t) (N.tm.initCfg x)
        ∃ T, (∀ t' ≤ t, (N.tm.runWith (s.take t') (N.tm.initCfg x)).state = none →
                T ≤ C * (t' + x.length + (Nat.bits t).length + 1)) ∧
          T ≤ C * (t + 1) ∧
          (R.runFrom start T).state =
            some (if e.state = none ∧ e.output = [true] then accept else reject) ∧
          ∀ u < T, (R.runFrom start u).state ≠ some accept ∧
            (R.runFrom start u).state ≠ some reject := by
  sorry

end Turing
