/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Build.Primitives
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic characterizations: Theorem 2.6, NEXP, and padding

[AB09, Theorem 2.6]: `NP = ⋃ c, NTIME (n^c)` — the certificate view and the
nondeterministic-machine view of `NP` coincide, with the accepting choice word as the
certificate and vice versa. This module states both directions as machine
compilations, the analogous `NTIME` characterization of the certificate-form
`Complexity.NEXP` ([AB09, §2.6.2] *defines* `NEXP` as `⋃ c, NTIME (2^(n^c))`; our
definition is [AB09, Exercise 2.27]'s verifier form, so the equality here is the
reconciliation of the two), and Theorem 2.22 (`EXP ≠ NEXP → P ≠ NP`, by padding).

## Design and deviations from [AB09]

* **The `NTIME` unions carry the same `+ 1` padding as `P`**: we write
  `⋃ c, NTIME (n^c + 1)` where [AB09] writes `⋃_{c ≥ 1} NTIME(n^c)`, for the reason
  recorded at `Complexity.P` — `n^c` vanishes at `n = 0` for `c ≥ 1` and no machine
  halts in zero steps, so the literal union is degenerate on the empty input; for
  `n ≥ 1` the two readings sandwich each other inside the constant slack. The
  exponential union `⋃ c, NTIME (2^(n^c))` needs no padding (`2^(n^c) ≥ 1`) and is
  [AB09]'s expression verbatim, matching `Complexity.EXP`.
* **Theorem 2.22 is proved through the certificate form** of `Complexity.NEXP` — the
  route of [AB09, Exercise 2.27], which needs no nondeterministic machines — rather
  than by padding an `NTIME` machine as in [AB09]'s proof of the theorem. With
  `Complexity.NEXP_eq_iUnion_NTIME` on the books the two renderings of the statement
  agree; the certificate route reuses the audited Exercise-2.1 interface instead of
  re-deriving NDTM compilations inside the padding argument.
* The choice-word/certificate correspondence is stated over the repaired explicit
  length formulas of `Complexity.NP`/`Complexity.NEXP` (phase-1 audit): each direction
  must land certificates of length **exactly** `C·(n+1)^c` (resp. `C·2^((n+1)^c)`),
  which the sketches arrange by padding choice words — harmless because halting is
  absorbing under every choice (`Turing.NDTM.runWith_of_halt`).

## Main results

* `Complexity.ntime_poly_subset_NP`, `Complexity.NP_subset_iUnion_NTIME`,
  `Complexity.NP_eq_iUnion_NTIME` — [AB09, Theorem 2.6], both directions and the
  equality.
* `Complexity.ntime_expPow_subset_NEXP`, `Complexity.NEXP_subset_iUnion_NTIME`,
  `Complexity.NEXP_eq_iUnion_NTIME` — the `NTIME` form of `NEXP` [AB09, §2.6.2,
  reconciled with Exercise 2.27].
* `Complexity.EXP_eq_NEXP_of_P_eq_NP`, `Complexity.P_ne_NP_of_EXP_ne_NEXP` —
  [AB09, Theorem 2.22], padding.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 2.6, pp. 41-42; §2.6.2, pp. 56-57;
  Theorem 2.22, p. 57; Exercises 2.1, 2.27.)

**Maintainer note (E5 dedup).** The epoch-2 checkpoint's superseded
standalone copying phase — `copyTapes` and the `choiceCopy*` family,
eight private declarations — was removed under the epoch-2 gate's
binding live/dead inventory (`audits/ch2-epoch2-resolutions.md`): the
continuation's forward compiler consumed `splitSolve` and the capture
layer directly, and the auditor's kernel walk confirmed the family
absent from the forward inclusion's closure. Unreferenced
continuation/B2-era lemmas that discharge binding contract obligations
(`cont_poly_guess_phase`, `b2_unary_mask`, `b2_tables_coincide`,
`certificateSplit_complete`) are deliberately retained as audited
evidence.
-/

namespace Complexity

open Turing
open Turing.FinTM

/-- The total length of an input and its prescribed certificate strictly increases
with the input length, including zero coefficient and degree. -/
private lemma certificate_split_strictMono (C c : ℕ) :
    StrictMono (fun n : ℕ => n + C * (n + 1) ^ c) := by
  intro n m hnm
  exact Nat.add_lt_add_of_lt_of_le hnm
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) c))

/-- Two concatenations satisfying the same exact certificate-length formula have
the same input and certificate whenever their concatenated words agree. -/
private lemma certificate_split_unique (C c : ℕ) {x u y v : List Bool}
    (hu : u.length = C * (x.length + 1) ^ c)
    (hv : v.length = C * (y.length + 1) ^ c) (h : x ++ u = y ++ v) :
    x = y ∧ u = v := by
  have hlen := congrArg List.length h
  simp only [List.length_append, hu, hv] at hlen
  have hx := (certificate_split_strictMono C c).injective hlen
  exact ⟨List.append_inj_left h hx, List.append_inj_right h hx⟩

/-- A finite, total specification of split recovery. Its implementation on native
tapes, including the time for polynomial evaluation, remains a startup obligation. -/
private def certificateSplit (C c m : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? (fun n => decide (n + C * (n + 1) ^ c = m))

/-- Every returned split is within the actual input and satisfies the exact
length formula. No validity assumption on the input is needed. -/
private lemma certificateSplit_spec (C c m n : ℕ)
    (h : certificateSplit C c m = some n) : n ≤ m ∧ n + C * (n + 1) ^ c = m := by
  have hn := List.mem_of_find?_eq_some h
  have he := List.find?_some h
  exact ⟨Nat.le_of_lt_succ (List.mem_range.mp hn), of_decide_eq_true he⟩

/-- Failed finite search means there is no solution at any natural split position,
so malformed lengths must be rejected rather than assigned a default split. -/
private lemma certificateSplit_none_iff (C c m : ℕ) :
    certificateSplit C c m = none ↔ ¬ ∃ n, n + C * (n + 1) ^ c = m := by
  rw [certificateSplit, List.find?_eq_none]
  constructor
  · intro h hex
    obtain ⟨n, hn⟩ := hex
    exact h n (List.mem_range.mpr (by omega)) (by simpa using hn)
  · intro h n _ hn
    exact h ⟨n, of_decide_eq_true hn⟩

/-- A valid split is returned by finite search; strict increase rules out a
different successful candidate before it. -/
private lemma certificateSplit_complete (C c m n : ℕ)
    (hn : n + C * (n + 1) ^ c = m) : certificateSplit C c m = some n := by
  cases hs : certificateSplit C c m with
  | none => exact False.elim ((certificateSplit_none_iff C c m).mp hs ⟨n, hn⟩)
  | some k =>
    have hk := (certificateSplit_spec C c m k hs).2
    have heq := (certificate_split_strictMono C c).injective (hk.trans hn.symm)
    exact congrArg some heq

/-- The verifier language described in the forward Theorem-2.6 sketch. This is a
language specification; polynomial-time decidability still requires a machine. -/
private def choiceVerifier (N : FinNDTM Bool) (C c : ℕ) : Language Bool :=
  {y | ∃ x u : List Bool, u.length = C * (x.length + 1) ^ c ∧ y = x ++ u ∧
    (N.tm.runWith u (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith u (N.tm.initCfg x)).output = [true]}

/-- On a correctly split word, verifier membership is exactly halted singleton-true
acceptance of the supplied choice word; a different split cannot create acceptance. -/
private lemma choiceVerifier_append (N : FinNDTM Bool) (C c : ℕ)
    (x u : List Bool) (hu : u.length = C * (x.length + 1) ^ c) :
    x ++ u ∈ choiceVerifier N C c ↔
      (N.tm.runWith u (N.tm.initCfg x)).state = none ∧
      (N.tm.runWith u (N.tm.initCfg x)).output = [true] := by
  constructor
  · rintro ⟨y, v, hv, heq, hhalt, hout⟩
    obtain ⟨rfl, rfl⟩ := certificate_split_unique C c hu hv heq
    exact ⟨hhalt, hout⟩
  · rintro ⟨hhalt, hout⟩
    exact ⟨x, u, hu, rfl, hhalt, hout⟩

/-- A word whose length has no valid split is outside the specified verifier
language. This is the rejecting branch of the total parser specification. -/
private lemma choiceVerifier_no_split (N : FinNDTM Bool) (C c : ℕ) (y : List Bool)
    (h : certificateSplit C c y.length = none) : y ∉ choiceVerifier N C c := by
  rintro ⟨x, u, hu, hy, _, _⟩
  have hlen := congrArg List.length hy
  simp only [List.length_append, hu] at hlen
  exact (certificateSplit_none_iff C c y.length).mp h ⟨x.length, hlen.symm⟩

/-- Once every branch has halted at `t`, extending the common budget changes
neither existential acceptance nor the accepting output. The reverse implication
uses the length-`t` prefix and all-branch halting, not just one halted branch. -/
private lemma acceptsWithin_iff_of_halts {N : FinNDTM Bool} {x : List Bool}
    {t t' : ℕ} (hhalt : N.tm.HaltsWithin x t) (hle : t ≤ t') :
    N.AcceptsWithin x t' ↔ N.AcceptsWithin x t := by
  constructor
  · rintro ⟨w, hw, _, hout⟩
    have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
    have hp := hhalt (w.take t) hlen
    have hr := N.tm.runWith_append (w.take t) (w.drop t) (N.tm.initCfg x)
    rw [List.take_append_drop, NDTM.runWith_of_halt _ hp] at hr
    exact ⟨w.take t, hlen, hp, hr ▸ hout⟩
  · intro h
    exact h.mono hle

/-- The exact certificate length with coefficient `2*a` covers the nondeterministic
time bound, uniformly at length zero and degree zero. -/
private lemma choice_budget_le (a c n : ℕ) :
    a * (n ^ c + 1) ≤ (2 * a) * (n + 1) ^ c := by
  have hp := Nat.pow_le_pow_left (Nat.le_succ n) c
  have h1 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow c _ (Nat.succ_pos n)
  calc
    a * (n ^ c + 1) ≤ a * ((n + 1) ^ c + (n + 1) ^ c) :=
      Nat.mul_le_mul_left a (Nat.add_le_add hp h1)
    _ = (2 * a) * (n + 1) ^ c := by ring

/-- Padding and truncation identify language membership with certificates for the
specified verifier. This proves the logical correspondence separately from the
timed construction needed to put the verifier in `P`. -/
private lemma choice_certificate_iff (N : FinNDTM Bool) (L : Language Bool)
    (a c : ℕ) (hN : N.DecidesInTime L (fun n => a * (n ^ c + 1)))
    (x : List Bool) :
    x ∈ L ↔ ∃ u : List Bool, u.length = (2 * a) * (x.length + 1) ^ c ∧
      x ++ u ∈ choiceVerifier N (2 * a) c := by
  rw [(hN x).2, ← acceptsWithin_iff_of_halts (hN x).1 (choice_budget_le a c x.length)]
  constructor
  · rintro ⟨u, hu, hhalt, hout⟩
    exact ⟨u, hu, (choiceVerifier_append N (2 * a) c x u hu).mpr ⟨hhalt, hout⟩⟩
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, hu, (choiceVerifier_append N (2 * a) c x u hu).mp hv⟩

/-- A finite summary of captured output: empty, the singleton true, or a rejecting
nonempty word. The complete word is retained separately on the capture tape. -/
private def capturedSummary : List Bool → Option Bool
  | [] => none
  | [b] => some b
  | _ => some false

/-- Update the output summary with one optional emission. -/
private def captureEmission (s : Option Bool) (e : Option Bool) : Option Bool :=
  match e with
  | none => s
  | some b => match s with
    | none => some b
    | some _ => some false

/-- The finite summary processes every emission, including one on the source's
halting transition; two or more emitted bits always give a rejecting summary. -/
private lemma captureEmission_correct (w : List Bool) (e : Option Bool) :
    captureEmission (capturedSummary w) e = capturedSummary (w ++ e.toList) := by
  cases e with
  | none => simp [captureEmission]
  | some b =>
    cases w with
    | nil => rfl
    | cons a w =>
      cases w with
      | nil => rfl
      | cons a' w => rfl

/-- The accepting summary recognizes exactly the singleton true, rather than a
word that merely contains true or starts with true. -/
private lemma capturedSummary_true (w : List Bool) :
    capturedSummary w = some true ↔ w = [true] := by
  cases w with
  | nil => simp [capturedSummary]
  | cons b w =>
    cases w with
    | nil => simp [capturedSummary]
    | cons b' w => simp [capturedSummary]

/-- Partition the work tapes into the original source tapes and three private
tapes, in order: virtual input, choices, captured output. -/
private def choiceTapes {α : Type} {k : ℕ} (source : Fin k → α)
    (input choices output : α) : Fin (k + 3) → α :=
  Fin.addCases source (fun i => if i = 0 then input else if i = 1 then choices else output)

/-- The deterministic simulation phase for a fixed NDTM. It starts only after its
three private tapes have been prepared. Each copied choice causes one source
step; a blank choice ends the clock and emits one verdict. Source halts remain
live simulator states until that clock ends. The physical input is never read.

The source state and the boundary tag are finite control. Every emission is
written to the capture tape, with a finite summary used only for the final exact
singleton test; physical output stays empty until that test. -/
private def choiceCore (N : FinNDTM Bool) : FinTM Bool where
  k := N.k + 3
  State := Option N.State × Bool × Option Bool
  tm :=
    { q₀ := (some N.tm.q₀, true, none)
      tr := fun ⟨q, tag, summary⟩ _ work =>
        match work (Fin.natAdd N.k 1) with
        | none =>
          ⟨0, fun _ => (none, 0), some (decide (q = none ∧ summary = some true)), none⟩
        | some bit =>
          match q with
          | none =>
            ⟨0, choiceTapes (fun _ => (none, 0)) (none, 0) (none, 1) (none, 0),
              none, some (none, tag, summary)⟩
          | some q =>
            let inp := work (Fin.natAdd N.k 0)
            let a := N.tm.tr bit q inp (fun i => work (Fin.castAdd 3 i))
            let m := virtualMove tag inp a.inputTape
            ⟨0, choiceTapes a.workTapes (none, m) (none, 1)
                (a.output.map some, if a.output.isSome then 1 else 0),
              none, some (a.state, virtualNextTag tag m, captureEmission summary a.output)⟩ }

/-- Embed a source configuration in the prepared simulator, preserving each
source tape and storing input, choices and captured output in disjoint blocks.
The native physical input position is arbitrary and remains fixed. -/
private def choiceCoreCfg (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (u : List Bool) (j : ℕ)
    (p : Fin (y.length + 2)) : Cfg (choiceCore N).k Bool (choiceCore N).State y where
  state := some (cfg.state, tag, capturedSummary cfg.output)
  inputPos := p
  workTapes := choiceTapes cfg.workTapes (bufferTape x) (bufferTape u) (bufferTape cfg.output)
  workTapePos := choiceTapes cfg.workTapePos ((cfg.inputPos.val : ℤ) - 1)
    (j : ℤ) (cfg.output.length : ℤ)
  output := []

/-- A prepared simulator consumes exactly the next copied choice in one physical
step. Its source tapes, virtual input and complete captured output agree with the
native source step. The physical output is still empty, even on a source halt.

**Proof sketch.** The copied-input read is the native guarded read. Apply the
existing virtual-movement invariant to preserve both clamping and the boundary
tag. Check the disjoint tape blocks separately; the output block uses the
append-at-the-right-blank identity. A halted source is absorbed while the choice
head still advances. -/
private lemma choiceCore_step (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (htag : VirtualTag cfg.inputPos tag)
    (u : List Bool) (j : ℕ) (hj : j < u.length) (p : Fin (y.length + 2)) :
    ∃ tag', VirtualTag (N.tm.stepWith u[j] cfg).inputPos tag' ∧
      (choiceCore N).tm.step (choiceCoreCfg N cfg tag u j p) =
        choiceCoreCfg N (N.tm.stepWith u[j] cfg) tag' u (j + 1) p := by
  have hu : (choiceCoreCfg N cfg tag u j p).workTapeSymbols (Fin.natAdd N.k 1) =
      some u[j] := by
    simp [choiceCoreCfg, choiceTapes, Cfg.workTapeSymbols, List.getElem?_eq_getElem hj]
  have hi : (choiceCoreCfg N cfg tag u j p).workTapeSymbols (Fin.natAdd N.k 0) =
      cfg.inputSymbol := by
    simp [choiceCoreCfg, choiceTapes, Cfg.workTapeSymbols, bufferTape_inputSymbol]
  have hw : (fun i => (choiceCoreCfg N cfg tag u j p).workTapeSymbols
      (Fin.castAdd 3 i)) = cfg.workTapeSymbols := by
    funext i
    simp [choiceCoreCfg, choiceTapes, Cfg.workTapeSymbols]
  have hs : (choiceCoreCfg N cfg tag u j p).state =
      some (cfg.state, tag, capturedSummary cfg.output) := rfl
  cases hq : cfg.state with
  | none =>
    have hc := NDTM.stepWith_of_halt (tm := N.tm) (b := u[j]) hq
    refine ⟨tag, ?_, ?_⟩
    · simpa only [hc] using htag
    · rw [hc]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [choiceCore]
      rw [hu, hq]
      refine Cfg.ext (by simp [choiceCoreCfg, hq]) (moveInputPos_zero _) ?_ ?_
        (by simp [choiceCoreCfg])
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [choiceCoreCfg, choiceTapes]
        · intro i; fin_cases i <;> simp [choiceCoreCfg, choiceTapes]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [choiceCoreCfg, choiceTapes]
        · intro i; fin_cases i <;> simp [choiceCoreCfg, choiceTapes, Nat.cast_add]
  | some q =>
    let a := N.tm.tr u[j] q cfg.inputSymbol cfg.workTapeSymbols
    let m := virtualMove tag cfg.inputSymbol a.inputTape
    have hm := virtualMove_correct cfg tag htag a.inputTape
    have hc : N.tm.stepWith u[j] cfg = a.apply cfg := by
      simp only [NDTM.stepWith, hq, a]
    refine ⟨virtualNextTag tag m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · rw [hc]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [choiceCore]
      rw [hu, hq, hi, hw]
      change (Action.mk 0 (choiceTapes a.workTapes (none, m) (none, 1)
          (a.output.map some, if a.output.isSome then 1 else 0)) none
          (some (a.state, virtualNextTag tag m,
            captureEmission (capturedSummary cfg.output) a.output))).apply
          (choiceCoreCfg N cfg tag u j p) =
        choiceCoreCfg N (a.apply cfg) (virtualNextTag tag m) u (j + 1) p
      refine Cfg.ext (by simp [choiceCoreCfg, captureEmission_correct])
        (moveInputPos_zero _) ?_ ?_ (by simp [choiceCoreCfg])
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [choiceCoreCfg, choiceTapes]
        · intro i
          fin_cases i <;> cases he : a.output <;>
            simp [choiceCoreCfg, choiceTapes, he, bufferTape_append]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [choiceCoreCfg, choiceTapes]
        · intro i
          fin_cases i
          · simpa [choiceCoreCfg, choiceTapes, m] using hm.1
          · simp [choiceCoreCfg, choiceTapes, Nat.cast_add]
          · cases he : a.output <;> simp [choiceCoreCfg, choiceTapes, he]

/-- After `t` physical simulation steps the represented source has consumed
exactly the first `t` copied choices. Administrative work before this phase is
not counted as source choices. The full configuration equality includes the
unchanged physical input, all source tapes, captured output, and empty real output.

**Proof sketch.** Induct on the physical step count, applying the one-step
invariant to the next indexed choice. The next prefix is the old prefix followed
by that bit, so the append law identifies the corresponding source run. -/
private lemma choiceCore_run (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (htag : VirtualTag cfg.inputPos tag)
    (u : List Bool) (t : ℕ) (ht : t ≤ u.length) (p : Fin (y.length + 2)) :
    ∃ tag', VirtualTag (N.tm.runWith (u.take t) cfg).inputPos tag' ∧
      (choiceCore N).tm.runFrom (choiceCoreCfg N cfg tag u 0 p) t =
        choiceCoreCfg N (N.tm.runWith (u.take t) cfg) tag' u t p := by
  induction t with
  | zero => exact ⟨tag, htag, rfl⟩
  | succ t ih =>
    obtain ⟨tag', htag', hr⟩ := ih (by omega)
    obtain ⟨tag'', htag'', hs⟩ :=
      choiceCore_step N (N.tm.runWith (u.take t) cfg) tag' htag' u t (by omega) p
    have hn : N.tm.runWith (u.take (t + 1)) cfg =
        N.tm.stepWith u[t] (N.tm.runWith (u.take t) cfg) := by
      rw [List.take_succ_eq_append_getElem (by omega), NDTM.runWith_append]
      rfl
    refine ⟨tag'', ?_, ?_⟩
    · simpa only [hn] using htag''
    · rw [MultiTapeTM.runFrom_succ_eq_step', hr, hs, hn]

/-- At the blank after the copied choice word, one final transition halts and
emits exactly one decision bit. A live source with output `[true]` rejects, as
does every halted source whose complete output differs from `[true]`. -/
private lemma choiceCore_finish (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (u : List Bool)
    (p : Fin (y.length + 2)) :
    ((choiceCore N).tm.step (choiceCoreCfg N cfg tag u u.length p)).state = none ∧
      ((choiceCore N).tm.step (choiceCoreCfg N cfg tag u u.length p)).output =
        [decide (cfg.state = none ∧ cfg.output = [true])] := by
  have hu : (choiceCoreCfg N cfg tag u u.length p).workTapeSymbols
      (Fin.natAdd N.k 1) = none := by
    simp [choiceCoreCfg, choiceTapes, Cfg.workTapeSymbols]
  have hs : (choiceCoreCfg N cfg tag u u.length p).state =
      some (cfg.state, tag, capturedSummary cfg.output) := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only [choiceCore]
  rw [hu]
  simp [choiceCoreCfg, capturedSummary_true]

/-- From a prepared configuration, the deterministic core halts after exactly the
declared `|u|+1` budget and reports whether the native source run under `u` accepts.
This is a timed `runFrom` contract, not a claim about blank-tape initialization. -/
private lemma choiceCore_timed (N : FinNDTM Bool) {x y : List Bool}
    (cfg : Cfg N.k Bool N.State x) (tag : Bool) (htag : VirtualTag cfg.inputPos tag)
    (u : List Bool) (p : Fin (y.length + 2)) :
    let result := (choiceCore N).tm.runFrom (choiceCoreCfg N cfg tag u 0 p) (u.length + 1)
    result.state = none ∧ result.output =
      [decide ((N.tm.runWith u cfg).state = none ∧
        (N.tm.runWith u cfg).output = [true])] := by
  obtain ⟨tag', _, hr⟩ := choiceCore_run N cfg tag htag u u.length (le_refl _) p
  simp only [List.take_length] at hr
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', hr]
  exact choiceCore_finish N (N.tm.runWith u cfg) tag' u p

/-- The native initial source configuration has the correct virtual boundary tag,
including the empty-input case, where position one is already the right blank. -/
private lemma choiceCore_initial_tag (N : FinNDTM Bool) (x : List Bool) :
    VirtualTag (N.tm.initCfg x).inputPos true := by
  simp [NDTM.initCfg, Cfg.init, VirtualTag]

/-- The library and this file solve the same length equation. The coefficient
is unchanged here: the `C+1` translation recorded for the marker-padding parser
in `NP.lean` does not apply to this file's choice-word parser. -/
private lemma cont_split_bridge (C c m : ℕ) :
    solveSplit C c m = certificateSplit C c m := by
  rfl

/-- Parse an aligned pair into the two buffers of the proved choice core.
States 0--2 parse doubled prefix bits, state 3 copies the suffix, and states
4--5 rewind the input and choice buffers. Both rewinds first move left from
the right blank, so empty words have the same startup contract. Every
administrative transition is physically silent except malformed rejection.
The core's transition table is embedded verbatim in the right summand. -/
private def contPairTM (N : FinNDTM Bool) : FinTM Bool where
  k := N.k + 3
  State := Fin 6 ⊕ (choiceCore N).State
  tm :=
    { q₀ := .inl 0
      tr := fun q inp work => match q with
        | .inr q => Action.mapState Sum.inr ((choiceCore N).tm.tr q inp work)
        | .inl 0 => match inp with
          | some b => ⟨1, fun _ => (none, 0), none, some (.inl (if b then 2 else 1))⟩
          | none => ⟨0, fun _ => (none, 0), some false, none⟩
        | .inl 1 => match inp with
          | some false => ⟨1, choiceTapes (fun _ => (none, 0))
              (some (some false), 1) (none, 0) (none, 0), none, some (.inl 0)⟩
          | some true => ⟨1, fun _ => (none, 0), none, some (.inl 3)⟩
          | none => ⟨0, fun _ => (none, 0), some false, none⟩
        | .inl 2 => match inp with
          | some true => ⟨1, choiceTapes (fun _ => (none, 0))
              (some (some true), 1) (none, 0) (none, 0), none, some (.inl 0)⟩
          | _ => ⟨0, fun _ => (none, 0), some false, none⟩
        | .inl 3 => match inp with
          | some b => ⟨1, choiceTapes (fun _ => (none, 0))
              (none, 0) (some (some b), 1) (none, 0), none, some (.inl 3)⟩
          | none => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, -1) (none, 0) (none, 0), none, some (.inl 4)⟩
        | .inl 4 => match work (Fin.natAdd N.k 0) with
          | some _ => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, -1) (none, 0) (none, 0), none, some (.inl 4)⟩
          | none => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, 1) (none, -1) (none, 0), none, some (.inl 5)⟩
        | .inl _ => match work (Fin.natAdd N.k 1) with
          | some _ => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, 0) (none, -1) (none, 0), none, some (.inl 5)⟩
          | none => ⟨0, choiceTapes (fun _ => (none, 0))
              (none, 0) (none, 1) (none, 0), none,
                some (.inr (some N.tm.q₀, true, none))⟩ }

/-- A silent loader configuration; the source work tapes and capture tape are
blank, and the two word buffers and their heads are explicit. -/
private def contLoadCfg (N : FinNDTM Bool) {y : List Bool} (q : Fin 6)
    (x u : List Bool) (p : Fin (y.length + 2)) (a b : ℤ) :
    Cfg (contPairTM N).k Bool (contPairTM N).State y :=
  ⟨some (.inl q), p, choiceTapes (fun _ _ => none) (bufferTape x)
    (bufferTape u) (fun _ => none), choiceTapes (fun _ => 0) a b 0, []⟩

/-- Once the loader dispatches, the proved core runs in exact lockstep in
its renamed control states, including its final physical verdict. -/
private lemma cont_core_run (N : FinNDTM Bool) {y : List Bool}
    (c : Cfg (choiceCore N).k Bool (choiceCore N).State y) (t : ℕ) :
    (contPairTM N).tm.runFrom (Cfg.mapState Sum.inr c) t =
      Cfg.mapState Sum.inr ((choiceCore N).tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
  intro d
  cases hs : d.state with
  | none => simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_none]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    change (Action.mapState Sum.inr ((choiceCore N).tm.tr q _ _)).apply _ = _
    rfl

/-- Rewinding the choice buffer costs exactly one step per remaining symbol
and one final dispatch, preserving the source input and every blank source tape.
**Proof sketch.** Induct on the number of cells to the left of the head. At
zero the head is at the left blank; otherwise its read is the corresponding
buffer bit and one left move reduces the induction parameter. -/
private lemma cont_rewind_choices (N : FinNDTM Bool) {y : List Bool}
    (x u : List Bool) (p : Fin (y.length + 2)) (j : ℕ) (hj : j ≤ u.length) :
    (contPairTM N).tm.runFrom (contLoadCfg (y := y) N 5 x u p 0 ((j : ℤ) - 1)) (j + 1) =
      Cfg.mapState Sum.inr (choiceCoreCfg N (N.tm.initCfg x) true u 0 p) := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero]
    have hw : (contLoadCfg (y := y) N 5 x u p 0 ((0 : ℤ) - 1)).workTapeSymbols
        (Fin.natAdd N.k 1) = none := by
      simp [contLoadCfg, Cfg.workTapeSymbols, choiceTapes]
    unfold MultiTapeTM.step
    change ((contPairTM N).tm.tr (.inl 5) _ _).apply _ = _
    dsimp only [contPairTM]
    rw [hw]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, Cfg.mapState, choiceCoreCfg, choiceTapes, NDTM.initCfg, Cfg.init]
      · intro i; fin_cases i <;>
          simp [contLoadCfg, Cfg.mapState, choiceCoreCfg, choiceTapes, NDTM.initCfg, Cfg.init]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, Cfg.mapState, choiceCoreCfg, choiceTapes, NDTM.initCfg, Cfg.init]
      · intro i; fin_cases i <;>
          simp [contLoadCfg, Cfg.mapState, choiceCoreCfg, choiceTapes, NDTM.initCfg, Cfg.init]
  | succ j ih =>
    have hw : (contLoadCfg (y := y) N 5 x u p 0 (((j + 1 : ℕ) : ℤ) - 1)).workTapeSymbols
        (Fin.natAdd N.k 1) = some u[j] := by
      simp [contLoadCfg, Cfg.workTapeSymbols, choiceTapes, List.getElem?_eq_getElem (by omega : j < u.length)]
    have hs : (contPairTM N).tm.step
        (contLoadCfg (y := y) N 5 x u p 0 (((j + 1 : ℕ) : ℤ) - 1)) =
          contLoadCfg (y := y) N 5 x u p 0 ((j : ℤ) - 1) := by
      unfold MultiTapeTM.step
      change ((contPairTM N).tm.tr (.inl 5) _ _).apply _ = _
      dsimp only [contPairTM]
      rw [hw]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
        · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
        · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Rewind the input buffer, then make the mandatory initial left move on
the choice buffer. The complete tape contents and physical input head survive.
**Proof sketch.** The same decreasing-head induction as the choice rewind;
the left-blank transition resets this head to zero and starts the next rewind. -/
private lemma cont_rewind_input (N : FinNDTM Bool) {y : List Bool}
    (x u : List Bool) (p : Fin (y.length + 2)) (j : ℕ) (hj : j ≤ x.length) :
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 4 x u p ((j : ℤ) - 1) u.length) (j + 1) =
        contLoadCfg (y := y) N 5 x u p 0 ((u.length : ℤ) - 1) := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero]
    have hw : (contLoadCfg (y := y) N 4 x u p ((0 : ℤ) - 1) u.length).workTapeSymbols
        (Fin.natAdd N.k 0) = none := by
      simp [contLoadCfg, Cfg.workTapeSymbols, choiceTapes]
    unfold MultiTapeTM.step
    change ((contPairTM N).tm.tr (.inl 4) _ _).apply _ = _
    dsimp only [contPairTM]
    rw [hw]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
      · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
      · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
  | succ j ih =>
    have hw : (contLoadCfg (y := y) N 4 x u p (((j + 1 : ℕ) : ℤ) - 1) u.length).workTapeSymbols
        (Fin.natAdd N.k 0) = some x[j] := by
      simp [contLoadCfg, Cfg.workTapeSymbols, choiceTapes, List.getElem?_eq_getElem (by omega : j < x.length)]
    have hs : (contPairTM N).tm.step
        (contLoadCfg (y := y) N 4 x u p (((j + 1 : ℕ) : ℤ) - 1) u.length) =
          contLoadCfg (y := y) N 4 x u p ((j : ℤ) - 1) u.length := by
      unfold MultiTapeTM.step
      change ((contPairTM N).tm.tr (.inl 4) _ _).apply _ = _
      dsimp only [contPairTM]
      rw [hw]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
        · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro i; simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
        · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Appending optional bits at the two right blanks realizes precisely the
corresponding list appends; all source and capture tapes remain blank. -/
private lemma cont_write_apply (N : FinNDTM Bool) {y : List Bool}
    (q q' : Fin 6) (x u : List Bool) (p : Fin (y.length + 2))
    (m : SignType) (bx bu : Option Bool) :
    (Action.mk m (choiceTapes (fun _ => (none, 0))
      (bx.map some, if bx.isSome then 1 else 0)
      (bu.map some, if bu.isSome then 1 else 0) (none, 0)) none
      (some (.inl q'))).apply (contLoadCfg (y := y) N q x u p x.length u.length) =
        contLoadCfg (y := y) N q' (x ++ bx.toList) (u ++ bu.toList) (moveInputPos p m)
          (x ++ bx.toList).length (u ++ bu.toList).length := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro i; simp [contLoadCfg, choiceTapes]
    · intro i
      fin_cases i <;> cases bx <;> cases bu <;>
        simp [contLoadCfg, choiceTapes, bufferTape_append]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro i; simp [contLoadCfg, choiceTapes]
    · intro i
      fin_cases i <;> cases bx <;> cases bu <;>
        simp [contLoadCfg, choiceTapes]

/-- Read the physical input at the loader's explicit position, including its
right boundary. The buffers have no effect on this read. -/
private lemma cont_load_read (N : FinNDTM Bool) {y : List Bool} (q : Fin 6)
    (x u : List Bool) (i : ℕ) (hi : i ≤ y.length) (a b : ℤ) :
    (contLoadCfg (y := y) N q x u ⟨i + 1, by omega⟩ a b).inputSymbol = y[i]? := by
  exact inputSymbol_at _ i hi rfl

/-- One right-going loader transition carries an exact physical step bound
and installs the appended buffers, provided its finite table has the displayed
write actions. -/
private lemma cont_load_right (N : FinNDTM Bool) {y : List Bool}
    (q q' : Fin 6) (x u : List Bool) (i : ℕ) (hi : i < y.length)
    (bx bu : Option Bool)
    (htr : (contPairTM N).tm.tr (.inl q) y[i]?
      (contLoadCfg (y := y) N q x u ⟨i + 1, by omega⟩ x.length u.length).workTapeSymbols =
        ⟨1, choiceTapes (fun _ => (none, 0))
          (bx.map some, if bx.isSome then 1 else 0)
          (bu.map some, if bu.isSome then 1 else 0) (none, 0), none, some (.inl q')⟩) :
    (contPairTM N).tm.step
      (contLoadCfg (y := y) N q x u ⟨i + 1, by omega⟩ x.length u.length) =
        contLoadCfg (y := y) N q' (x ++ bx.toList) (u ++ bu.toList) ⟨i + 2, by omega⟩
          (x ++ bx.toList).length (u ++ bu.toList).length := by
  unfold MultiTapeTM.step
  change ((contPairTM N).tm.tr (.inl q) _ _).apply _ = _
  rw [cont_load_read N q x u i (by omega), htr, cont_write_apply]
  congr 1
  apply Fin.ext
  rw [show (1 : SignType) = .pos from rfl,
    moveInputPos_pos_of_ne_right _ (by simp; omega)]

/-- The suffix copier appends each remaining physical input bit in exactly
one step. The prefix buffer is preserved and physical output stays empty.
**Proof sketch.** Induct on the remaining suffix, extending the physical
prefix and the copied suffix together in the inductive step. -/
private lemma cont_copy_run (N : FinNDTM Bool) (y rest : List Bool) :
    ∀ (pre x u : List Bool) (hy : y = pre ++ rest),
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 3 x u ⟨pre.length + 1, by simp [hy]; omega⟩
        x.length u.length) rest.length =
          contLoadCfg (y := y) N 3 x (u ++ rest) ⟨y.length + 1, by omega⟩
            x.length (u ++ rest).length := by
  induction rest with
  | nil => intro pre x u hy; subst y; simp [MultiTapeTM.runFrom_zero]
  | cons b rest ih =>
    intro pre x u hy
    have hs := cont_load_right (y := y) N 3 3 x u pre.length (by simp [hy]) none (some b) (by
      have hr : y[pre.length]? = some b := by simp [hy]
      rw [hr]
      rfl)
    simp only [Option.toList_none, Option.toList_some, List.append_nil] at hs
    simp only [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    rw [hs]
    have hh : y = (pre ++ [b]) ++ rest := by simp [hy, List.append_assoc]
    simpa only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] using ih (pre ++ [b]) x (u ++ [b]) hh

/-- After suffix copying, one left move plus the two exact rewinds enters the
proved simulator. No source choices are consumed during these administrative steps. -/
private lemma cont_start_core (N : FinNDTM Bool) (y x u : List Bool) :
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 3 x u ⟨y.length + 1, by omega⟩ x.length u.length)
      (1 + (x.length + 1) + (u.length + 1)) =
        Cfg.mapState Sum.inr (choiceCoreCfg N (N.tm.initCfg x) true u 0
          ⟨y.length + 1, by omega⟩) := by
  have hs : (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 3 x u ⟨y.length + 1, by omega⟩ x.length u.length) 1 =
        contLoadCfg (y := y) N 4 x u ⟨y.length + 1, by omega⟩
          ((x.length : ℤ) - 1) u.length := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((contPairTM N).tm.tr (.inl 3) _ _).apply _ = _
    rw [cont_load_read N 3 x u y.length (le_refl _)]
    simp only [List.getElem?_length]
    dsimp only [contPairTM]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, choiceTapes]
      · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [contLoadCfg, choiceTapes]
      · intro i; fin_cases i <;> simp [contLoadCfg, choiceTapes, sub_eq_add_neg]
  rw [MultiTapeTM.runFrom_add _ (1 + (x.length + 1)) (u.length + 1),
    MultiTapeTM.runFrom_add _ 1 (x.length + 1)]
  rw [hs, cont_rewind_input N x u _ x.length (le_refl _),
    cont_rewind_choices N x u _ u.length (le_refl _)]

/-- The suffix-copy, rewind, and native simulation phases compose with their
exact time bounds. A halted source's full output, including its final emission,
is tested only after the complete choice word has been consumed. -/
private lemma cont_suffix_run (N : FinNDTM Bool) (y pre x u : List Bool)
    (hy : y = pre ++ u) :
    let result := (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 3 x [] ⟨pre.length + 1, by simp [hy]; omega⟩ x.length 0)
      (u.length + (1 + (x.length + 1) + (u.length + 1)) + (u.length + 1))
    result.state = none ∧ result.output =
      [decide ((N.tm.runWith u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith u (N.tm.initCfg x)).output = [true])] := by
  have hc := cont_copy_run N y u pre x [] hy
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hc
  dsimp only
  rw [MultiTapeTM.runFrom_add _
      (u.length + (1 + (x.length + 1) + (u.length + 1))) (u.length + 1),
    MultiTapeTM.runFrom_add _ u.length (1 + (x.length + 1) + (u.length + 1)),
    hc, cont_start_core, cont_core_run]
  have h := choiceCore_timed (y := y) N (N.tm.initCfg x) true
    (choiceCore_initial_tag N x) u ⟨y.length + 1, by omega⟩
  exact ⟨by simpa only [Cfg.mapState, Option.map_eq_none_iff] using h.1, h.2⟩

/-- An aligned doubled bit is copied to the input buffer in exactly two
steps, without touching choices or emitting output. -/
private lemma cont_parse_double (N : FinNDTM Bool) (y pre rest x : List Bool)
    (b : Bool) (hy : y = pre ++ b :: b :: rest) :
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 0 x [] ⟨pre.length + 1, by simp [hy]; omega⟩ x.length 0) 2 =
        contLoadCfg (y := y) N 0 (x ++ [b]) [] ⟨pre.length + 3, by simp [hy]; omega⟩
          (x ++ [b]).length 0 := by
  have h1 := cont_load_right (y := y) N 0 (if b then 2 else 1) x [] pre.length
    (by simp [hy]) none none (by
      have hr : y[pre.length]? = some b := by simp [hy]
      rw [hr]
      have hz : choiceTapes (fun (_ : Fin N.k) => ((none : Option (Option Bool)), (0 : SignType)))
          (none, 0) (none, 0) (none, 0) = fun _ => (none, 0) := by
        funext i
        refine Fin.addCases (fun _ => by simp [choiceTapes]) (fun i => ?_) i
        fin_cases i <;> simp [choiceTapes]
      cases b <;> simp [contPairTM, hz])
  have h2 := cont_load_right (y := y) N (if b then 2 else 1) 0 x [] (pre.length + 1)
    (by simp [hy]) (some b) none (by
      have hr : y[pre.length + 1]? = some b := by simp [hy]
      rw [hr]
      cases b <;> rfl)
  simp only [Option.toList_none, Option.toList_some, List.append_nil,
    List.length_nil, Nat.cast_zero] at h1 h2
  simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  rw [h1]
  exact h2

/-- The aligned separator starts suffix copying after exactly two silent
transitions, leaving the already copied input word unchanged. -/
private lemma cont_parse_separator (N : FinNDTM Bool) (y pre u x : List Bool)
    (hy : y = pre ++ false :: true :: u) :
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 0 x [] ⟨pre.length + 1, by simp [hy]; omega⟩ x.length 0) 2 =
        contLoadCfg (y := y) N 3 x [] ⟨pre.length + 3, by simp [hy]; omega⟩ x.length 0 := by
  have hz : choiceTapes (fun (_ : Fin N.k) => ((none : Option (Option Bool)), (0 : SignType)))
      (none, 0) (none, 0) (none, 0) = fun _ => (none, 0) := by
    funext i
    refine Fin.addCases (fun _ => by simp [choiceTapes]) (fun i => ?_) i
    fin_cases i <;> simp [choiceTapes]
  have h1 := cont_load_right (y := y) N 0 1 x [] pre.length
    (by simp [hy]) none none (by
      have hr : y[pre.length]? = some false := by simp [hy]
      rw [hr]
      simp [contPairTM, hz])
  have h2 := cont_load_right (y := y) N 1 3 x [] (pre.length + 1)
    (by simp [hy]) none none (by
      have hr : y[pre.length + 1]? = some true := by simp [hy]
      rw [hr]
      simp [contPairTM, hz])
  simp only [Option.toList_none, List.append_nil, List.length_nil, Nat.cast_zero] at h1 h2
  simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  rw [h1]
  exact h2

/-- On a valid encoded pair, the doubled prefix and separator are parsed in
exactly `2*|x|+2` steps. The prefix buffer contains precisely the undoubled word.
**Proof sketch.** Induct on the first component. A data block invokes the
two-step copying lemma; the empty component invokes the separator lemma.
The generalized existing buffer and physical prefix make every seam explicit. -/
private lemma cont_parse_run (N : FinNDTM Bool) (y x u : List Bool) :
    ∀ (pre a : List Bool) (hy : y = pre ++ pairEncode x u),
    (contPairTM N).tm.runFrom
      (contLoadCfg (y := y) N 0 a [] ⟨pre.length + 1, by simp [hy]; omega⟩ a.length 0)
      (2 * x.length + 2) =
        contLoadCfg (y := y) N 3 (a ++ x) []
          ⟨pre.length + 2 * x.length + 3, by simp [hy, pairEncode]; omega⟩ (a ++ x).length 0 := by
  induction x with
  | nil =>
    intro pre a hy
    simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero, List.append_nil] using
      cont_parse_separator N y pre u a (by simpa [pairEncode] using hy)
  | cons b x ih =>
    intro pre a hy
    have hy' : y = pre ++ b :: b :: pairEncode x u := by
      simpa [pairEncode, List.append_assoc] using hy
    have hr := cont_parse_double N y pre (pairEncode x u) a b hy'
    have hh : y = (pre ++ [b, b]) ++ pairEncode x u := by
      simpa [List.append_assoc] using hy'
    conv_lhs =>
      arg 2
      simp only [List.length_cons]
      rw [show 2 * (x.length + 1) + 2 = 2 + (2 * x.length + 2) by omega]
    rw [MultiTapeTM.runFrom_add _ 2 (2 * x.length + 2), hr]
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using
        ih (pre ++ [b, b]) (a ++ [b]) hh

/-- Blank-tape initialization, parsing, copying, rewinds and simulation give
a genuine whole-machine contract on every valid pair, with a linear bound.
**Proof sketch.** The loader starts with two empty buffers and blank source
tapes. Sum the parser's `2|x|+2` steps, suffix copying's `|u|`, the
`|x|+|u|+3` rewind/dispatch steps, and the core's `|u|+1` steps. The sum
`3|x|+3|u|+6` fits `3(|pairEncode x u|+1)`. -/
private lemma cont_pair_computes (N : FinNDTM Bool) (x u : List Bool) :
    (contPairTM N).ComputesInTime (pairEncode x u)
      [decide ((N.tm.runWith u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith u (N.tm.initCfg x)).output = [true])]
      (3 * ((pairEncode x u).length + 1)) := by
  let y := pairEncode x u
  have hi : (contPairTM N).tm.initCfg y =
      contLoadCfg (y := y) N 0 [] [] ⟨1, by omega⟩ 0 0 := by
    refine Cfg.ext rfl (Fin.ext (by simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg])) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg, choiceTapes]
      · intro i; fin_cases i <;> simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg, choiceTapes]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro i; simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg, choiceTapes]
      · intro i; fin_cases i <;> simp [MultiTapeTM.initCfg, Cfg.init, contLoadCfg, choiceTapes]
  have hp := cont_parse_run N y x u [] [] rfl
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, Nat.zero_add] at hp
  have hf := cont_suffix_run N y (x.flatMap (fun b => [b, b]) ++ [false, true]) x u rfl
  have hlen : (x.flatMap (fun b => [b, b]) ++ [false, true]).length + 1 =
      2 * x.length + 3 := by simp; omega
  simp only [hlen] at hf
  have hbase : (contPairTM N).ComputesInTime y
      [decide ((N.tm.runWith u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith u (N.tm.initCfg x)).output = [true])]
      ((2 * x.length + 2) +
        (u.length + (1 + (x.length + 1) + (u.length + 1)) + (u.length + 1))) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hi, hp]
    exact hf
  apply hbase.mono
  simp [pairEncode]
  omega

/-- The split-search failure word is rejected in one transition, including
when the source NDTM would accept an empty input and empty choice word. -/
private lemma cont_pair_empty (N : FinNDTM Bool) :
    (contPairTM N).ComputesInTime [] [false] 1 := by
  apply (computesInTime_iff _ _ _ _).mpr
  simp [MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.step, MultiTapeTM.initCfg, Cfg.init, Cfg.inputSymbol, contPairTM]

/-- The library split emitter, retaining the exact encoded pair on success
and its distinguished empty failure word otherwise. -/
private def contSplitWord (C c : ℕ) (y : List Bool) : List Bool :=
  match solveSplit C c y.length with
  | some i => pairEncode (y.take i) (y.drop i)
  | none => []

/-- Split emission increases length by at most the doubled-prefix overhead.
This bound holds before any validity assumption. -/
private lemma cont_split_length (C c : ℕ) (y : List Bool) :
    (contSplitWord C c y).length ≤ 2 * y.length + 2 := by
  cases hs : solveSplit C c y.length with
  | none => simp [contSplitWord, hs]
  | some i =>
    have hi := (certificateSplit_spec C c y.length i (by
      simpa only [cont_split_bridge] using hs)).1
    simp [contSplitWord, hs, pairEncode]
    omega

/-- Every output of split search is handled in linear time, with exactly the
verifier's decision bit. Failure rejects; success uses the unique recovered
prefix and the exact certificate length.
**Proof sketch.** In the success case the split specification proves the
dropped suffix has the required length, so `choiceVerifier_append` identifies
the verdict. In the failure case `choiceVerifier_no_split` excludes membership.
The emitted pair's length is bounded on both branches before composition. -/
private lemma cont_split_answer (N : FinNDTM Bool) (C c : ℕ) (y : List Bool) :
    (contPairTM N).ComputesInTime (contSplitWord C c y)
      [MultiTapeTM.indicator (choiceVerifier N C c) y] (3 * (2 * y.length + 3)) := by
  classical
  cases hs : solveSplit C c y.length with
  | none =>
    have hn := choiceVerifier_no_split N C c y (by
      simpa only [cont_split_bridge] using hs)
    simpa only [contSplitWord, hs, MultiTapeTM.indicator, if_neg hn] using
      (cont_pair_empty N).mono (by omega : 1 ≤ 3 * (2 * y.length + 3))
  | some i =>
    obtain ⟨hi, he⟩ := certificateSplit_spec C c y.length i (by
      simpa only [cont_split_bridge] using hs)
    have hu : (y.drop i).length = C * ((y.take i).length + 1) ^ c := by
      rw [List.length_drop, List.length_take_of_le hi]
      omega
    have hv := choiceVerifier_append N C c (y.take i) (y.drop i) hu
    rw [List.take_append_drop] at hv
    have hout : MultiTapeTM.indicator (choiceVerifier N C c) y =
        decide ((N.tm.runWith (y.drop i) (N.tm.initCfg (y.take i))).state = none ∧
          (N.tm.runWith (y.drop i) (N.tm.initCfg (y.take i))).output = [true]) := by
      simp only [MultiTapeTM.indicator, hv]
      split <;> simp_all
    rw [contSplitWord, hs, hout]
    apply (cont_pair_computes N (y.take i) (y.drop i)).mono
    have hl := cont_split_length C c y
    simp only [contSplitWord, hs] at hl
    omega

/-- The complete choice-word verifier is polynomial-time on all inputs.
**Proof sketch.** The audited native split search costs `A(n+1)^(c+2)`.
Its output has length at most `2n+2`. Timed buffered composition takes at
most that cost plus the output length plus two steps to start the loader;
the loader/simulator then costs at most `3(2n+3)`. Thus the whole budget
is at most `(A+13)(n+1)^(c+2)`. The second phase is proved on every possible
split-search output; no untimed composition or unstated totality is used. -/
private lemma cont_choiceVerifier_mem_P (N : FinNDTM Bool) (C c : ℕ) :
    choiceVerifier N C c ∈ P := by
  obtain ⟨M, A, hM⟩ := computesFunInTime_splitSolve C c
  refine mem_P_iff.mpr ⟨A + 13, c + 2, bufferedCompTM M (contPairTM N), ?_⟩
  intro y
  have hfirst : M.ComputesInTime y (contSplitWord C c y)
      (A * (y.length + 1) ^ (c + 2)) := hM y
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start M (contPairTM N) y (contSplitWord C c y) _ hfirst
  obtain ⟨tag, _, hr⟩ := bufferedSecondCfg_run M (contPairTM N)
    ((contPairTM N).tm.initCfg (contSplitWord C c y)) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads
    (3 * (2 * y.length + 3))
  have hc := (computesInTime_iff _ _ _ _).mp (cont_split_answer N C c y)
  have hbase : (bufferedCompTM M (contPairTM N)).ComputesInTime y
      [MultiTapeTM.indicator (choiceVerifier N C c) y] (a + 3 * (2 * y.length + 3)) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  apply hbase.mono
  have hl := cont_split_length C c y
  have hp : y.length + 1 ≤ (y.length + 1) ^ (c + 2) := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos y.length) (by omega : 1 ≤ c + 2)
  calc
    a + 3 * (2 * y.length + 3) ≤
        A * (y.length + 1) ^ (c + 2) + 13 * (y.length + 1) := by omega
    _ ≤ A * (y.length + 1) ^ (c + 2) + 13 * (y.length + 1) ^ (c + 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 13 hp) _
    _ = (A + 13) * (y.length + 1) ^ (c + 2) := by ring

/-- **The choice word is a certificate** [AB09, Theorem 2.6, ⊆-direction of the
union]: every fixed-degree nondeterministic time class is contained in `NP`.

**Proof sketch.** Let `N` decide `L` within `T n = a·(n^c + 1)` (the `NTIME`
constant `a`). Certificate parameters: coefficient `2a`, degree `c`, so
`Q n = 2a·(n+1)^c ≥ T n` (as `n^c ≤ (n+1)^c` and `1 ≤ (n+1)^c`). The verifier
language is
`V = {x ++ u : |u| = Q |x| ∧ the run of N on x under choice word u is halted with output [true]}`
— a well-defined set, the split being unique since `n ↦ n + Q n` is strictly
increasing. Membership equivalence: forward, an accepting branch of length `T n` pads
with `false`-bits to length exactly `Q n`, still halted-with-`[true]` by
`Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`; backward, the length-
`T n` prefix of an accepting `u` is halted by the decider's `HaltsWithin`, absorption
gives it the same state and output, and `Turing.FinNDTM.AcceptsWithin` at `T n`
returns `x ∈ L`. `V ∈ P` by a deciding machine whose obligations are named for the
fill: (i) recover the unique split — search `n ≤ m` for `n + Q n = m`, **rejecting
explicitly when no solution exists** (the round-3 pattern of
`Complexity.mem_NP_iff_exists_length_le`), with a polynomial-evaluation machine for
the explicit formula `Q`; (ii) copy the choice suffix `u` to a dedicated work tape;
(iii) a clocked product simulation of the **fixed** machine `N`: `N`'s work tapes as
disjoint tape blocks (the `Simulation` lockstep gadgets are the precedent), `N`'s
state in finite control, and `N`'s input head as a binary position counter with the
**input-window guard** — `N` reads `x` only, so when the tracked position leaves the
window the simulator feeds the boundary blank instead of the symbol of `x ++ u` under
its own head, emulating the clamping of `Turing.moveInputPos` against the recovered
`n`; (iv) per simulated step, consume the next bit of the copied choice tape to select
between `N`'s two transition tables; (v) **output capture**: buffer `N`'s emissions on
a work tape and never write to the real output during simulation (the append-only
isolation obligation of the `Complexity.NP_subset_EXP` sketch;
`Turing.universalCaptureTM` is the in-repo precedent); (vi) the verdict — output
`[true]` iff the simulated run is halted with buffer exactly `[true]`, else `[false]`.
Budget: `Q n ≤ m` simulated steps at polynomial bookkeeping each, so polynomial in
`m`; conclude `V ∈ P` via `Complexity.mem_P_of_dtime_le` and `L ∈ NP` with
`(2a, c, V)`.

**Partial fill note (epoch 2B).** The certificate correspondence, finite split-search
specification, and two native phase contracts are proved below their private
definitions. `choiceCopy_timed` assumes a prepared unary split countdown and copies
the two words in `|x ++ u| + 1` steps. `choiceCore_timed` assumes prepared data tapes
and uses `|u| + 1` steps. In that core, the virtual input head is represented directly
by a head on the copied input buffer and a finite boundary tag, using
`virtualMove_correct`, rather than a binary position counter. This preserves the
specified guarded reads and clamping with constant overhead per source step. All
source emissions are captured on a separate tape; a finite summary recognizes
exactly `[true]` for the final verdict. These prepared-configuration contracts do
not supply a decider from blank tapes: the native arithmetic/split-search machine,
its rejecting branch, countdown preparation, rewinds, and timed phase composition
remain the single admitted verifier-membership obligation in this partial fill.

**Continuation completion (E2-cont-B).** The native library split emitter
`computesFunInTime_splitSolve C c` has exactly this file's coefficient `C`.
The new paired-input loader fills the input and choice buffers, rewinds them,
and enters the unchanged `choiceCore`; it needs no unary countdown. The
library emitter's empty failure word rejects. Timed buffered composition and
`cont_choiceVerifier_mem_P` now supply the whole blank-tape decider with bound
`(A+13)(m+1)^(c+2)`, where `A(m+1)^(c+2)` bounds split search. The predecessor's
copier and all other private phase proofs are retained unchanged. -/
theorem ntime_poly_subset_NP (c : ℕ) : NTIME (fun n => n ^ c + 1) ⊆ NP := by
  rintro L ⟨a, N, hN⟩
  refine ⟨2 * a, c, choiceVerifier N (2 * a) c, ?_,
    choice_certificate_iff N L a c hN⟩
  exact cont_choiceVerifier_mem_P N (2 * a) c

/-- Select the physical choice positions at which the deterministic scheduler
writes a guess. Administrative positions consume physical choices but contribute
no certificate bit. A short choice word contributes only its existing positions. -/
private def contSelect : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | emit :: mask, b :: w => (if emit then [b] else []) ++ contSelect mask w

/-- A fixed mask extracts precisely one certificate bit at each marked position,
independently of the values of the physical choices. -/
private lemma cont_select_length (mask w : List Bool) (hw : w.length = mask.length) :
    (contSelect mask w).length = (mask.filter id).length := by
  induction mask generalizing w with
  | nil => simp [contSelect]
  | cons emit mask ih =>
    cases w with
    | nil => simp at hw
    | cons b w =>
      have ht : w.length = mask.length := by simpa using hw
      cases emit <;> simp [contSelect, ih w ht]

/-- Every certificate of the scheduled length is realized at its actual physical
write positions. Unused choices may all be false; a zero-write schedule realizes
exactly the empty certificate.
**Proof sketch.** Induct on the mask. An unmarked position prepends an arbitrary
false choice. A marked position consumes and prepends the next certificate bit. -/
private lemma cont_select_surjective (mask u : List Bool)
    (hu : u.length = (mask.filter id).length) :
    ∃ w : List Bool, w.length = mask.length ∧ contSelect mask w = u := by
  induction mask generalizing u with
  | nil =>
    have he : u = [] := by simpa using hu
    subst u
    exact ⟨[], rfl, rfl⟩
  | cons emit mask ih =>
    cases emit with
    | false =>
      obtain ⟨w, hw, he⟩ := ih u (by simpa using hu)
      exact ⟨false :: w, by simp [hw], by simpa [contSelect] using he⟩
    | true =>
      cases u with
      | nil => simp at hu
      | cons b u =>
        obtain ⟨w, hw, he⟩ := ih u (by simpa using hu)
        exact ⟨b :: w, by simp [hw], by simp [contSelect, he]⟩

/-- The deterministic emission schedule, including the halting transition's
emission and excluding all subsequent absorbed steps. Evaluating it on the
unary word of length `n` gives a schedule depending on `n` alone. -/
private def contEmissionMask (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : ℕ → List Bool
  | 0 => []
  | t + 1 => (M.tm.outputSymbol c).isSome :: contEmissionMask M (M.tm.step c) t

/-- The schedule has one entry per physical scheduler transition. -/
private lemma cont_mask_length (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (contEmissionMask M c t).length = t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => simp [contEmissionMask, ih]

/-- Marked positions count every source emission exactly once, including an
emission on the halting transition.
**Proof sketch.** One step appends exactly `outputSymbol.toList`; its length
is zero or one according to the schedule's first entry. Induct on elapsed time. -/
private lemma cont_mask_count (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ) :
    c.output.length + ((contEmissionMask M c t).filter id).length =
      (M.tm.runFrom c t).output.length := by
  induction t generalizing c with
  | zero => simp [contEmissionMask]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have h := ih (M.tm.step c)
    rw [MultiTapeTM.step_output] at h
    cases he : M.tm.outputSymbol c <;>
      simpa [contEmissionMask, he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- A native nondeterministic guessing phase driven by a deterministic
scheduler. At every scheduler emission, capture the current physical choice
bit on the extra tape; all other transitions ignore it. Source reads never
consult that extra tape. A completed scheduler stays at the live return
state `none`; a surrounding controller must perform the later dispatch. -/
private def contGuessTM (M : FinTM Bool) : FinNDTM Bool where
  k := M.k + 1
  State := Option M.State
  tm :=
    { q₀ := some M.tm.q₀
      tr := fun bit q inp work => match q with
        | none => controlAction 0 (some none)
        | some q =>
          let a := M.tm.tr q inp (fun i => work i.castSucc)
          captureAction some none {a with output := a.output.map (fun _ => bit)} }

/-- The guessing-phase invariant: the deterministic scheduler's state, input
head and work tapes are exact; the guessed word is held separately at its
right blank, and physical output is empty. -/
private def contGuessCfg (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (u : List Bool) :
    Cfg (contGuessTM M).k Bool (contGuessTM M).State x :=
  ⟨some c.state, c.inputPos,
    (fun i => if h : i.val < M.k then c.workTapes ⟨i, h⟩ else bufferTape u),
    (fun i => if h : i.val < M.k then c.workTapePos ⟨i, h⟩ else u.length), []⟩

/-- One native guessing transition selects its physical choice exactly when
the scheduler emits. It preserves the complete source configuration, apart
from storing chosen rather than emitted data on the separate capture tape.
**Proof sketch.** For a live source, instantiate the capture-action transformer
with the emission replaced by the current choice. Check source and capture
tapes separately. A halted source and the phase's return state both stutter. -/
private lemma cont_guess_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (u : List Bool) (bit : Bool) :
    (contGuessTM M).tm.stepWith bit (contGuessCfg M c u) =
      contGuessCfg M (M.tm.step c)
        (u ++ if (M.tm.outputSymbol c).isSome then [bit] else []) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    simp only [MultiTapeTM.outputSymbol, hs, Option.isSome_none, Bool.false_eq_true,
      if_false, List.append_nil]
    unfold NDTM.stepWith
    simp only [contGuessCfg, hs]
    change (controlAction 0 (some none)).apply _ = _
    rw [controlAction_apply, moveInputPos_zero]
  | some q =>
    let a := M.tm.tr q c.inputSymbol c.workTapeSymbols
    have hi : (contGuessCfg M c u).inputSymbol = c.inputSymbol := rfl
    have hw : (fun i => (contGuessCfg M c u).workTapeSymbols i.castSucc) =
        c.workTapeSymbols := by
      funext i
      simp [contGuessCfg, Cfg.workTapeSymbols, i.isLt]
    have hstate : (contGuessCfg M c u).state = some (some q) := by simp [contGuessCfg, hs]
    unfold NDTM.stepWith
    rw [hstate]
    dsimp only [contGuessTM]
    rw [hi, hw]
    change (captureAction some none {a with output := a.output.map (fun _ => bit)}).apply
      (contGuessCfg M c u) = contGuessCfg M (M.tm.step c)
        (u ++ if (M.tm.outputSymbol c).isSome then [bit] else [])
    have hc : M.tm.step c = a.apply c := by simp [MultiTapeTM.step, hs, a]
    have he : M.tm.outputSymbol c = a.output := by simp [MultiTapeTM.outputSymbol, hs, a]
    rw [hc, he]
    refine Cfg.ext ?_ rfl ?_ ?_ rfl
    · cases ha : a.state <;> simp [captureAction, contGuessCfg, ha]
    · funext i
      by_cases h : i.val < M.k
      · simp [captureAction, contGuessCfg, h]
      · cases ho : a.output <;>
          simp [captureAction, contGuessCfg, h, ho, bufferTape_append]
    · funext i
      by_cases h : i.val < M.k
      · simp [captureAction, contGuessCfg, h]
      · cases ho : a.output <;> simp [captureAction, contGuessCfg, h, ho]

/-- The native phase realizes the emission-position mask exactly, with one
physical transition per choice and no changes to the source simulation.
**Proof sketch.** Induct on the physical choice word. The one-step lemma
appends its bit precisely at the first marked position; the remaining source
schedule is the schedule from the stepped configuration. -/
private lemma cont_guess_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (u w : List Bool) :
    (contGuessTM M).tm.runWith w (contGuessCfg M c u) =
      contGuessCfg M (M.tm.runFrom c w.length)
        (u ++ contSelect (contEmissionMask M c w.length) w) := by
  induction w generalizing c u with
  | nil => simp [contSelect, contEmissionMask]
  | cons bit w ih =>
    rw [NDTM.runWith_cons, cont_guess_step, ih]
    simp only [List.length_cons, contEmissionMask, contSelect,
      MultiTapeTM.runFrom_succ_eq_step, List.append_assoc]

/-- The guessing phase's genuine initial configuration has the scheduler's
blank source bank and an empty capture tape. -/
private lemma cont_guess_initial (M : FinTM Bool) (x : List Bool) :
    (contGuessTM M).tm.initCfg x = contGuessCfg M (M.tm.initCfg x) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : i.val < M.k <;>
      simp [NDTM.initCfg, MultiTapeTM.initCfg, Cfg.init, contGuessCfg]
  · funext i
    by_cases h : i.val < M.k <;>
      simp [NDTM.initCfg, MultiTapeTM.initCfg, Cfg.init, contGuessCfg]

/-- The native guessing phase has both witness extraction and witness coverage
at the scheduler's physical step budget. It captures exactly as many bits as
the completed scheduler emitted, and all words of that length occur.
**Proof sketch.** The emission-count invariant fixes the mask's number of
marked positions. Exact-length selection gives extraction; mask surjectivity
gives coverage. The native run invariant then supplies the whole configuration,
not merely the captured tape. The host's return state is still live here. -/
private lemma cont_guess_coverage (M : FinTM Bool) (x v : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x v T) :
    (∀ w : List Bool, w.length = T → ∃ u : List Bool, u.length = v.length ∧
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) u) ∧
    (∀ u : List Bool, u.length = v.length → ∃ w : List Bool, w.length = T ∧
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) u) := by
  let mask := contEmissionMask M (M.tm.initCfg x) T
  have hlen : mask.length = T := cont_mask_length M _ T
  have hcount : (mask.filter id).length = v.length := by
    have h := cont_mask_count M (M.tm.initCfg x) T
    have ho := ((computesInTime_iff _ _ _ _).mp hM).2
    rw [ho] at h
    simpa only [MultiTapeTM.initCfg, Cfg.init, List.length_nil, Nat.zero_add] using h
  have hrun (w : List Bool) (hw : w.length = T) :
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) (contSelect mask w) := by
    rw [cont_guess_initial, cont_guess_run, hw, List.nil_append]
  constructor
  · intro w hw
    exact ⟨contSelect mask w, (cont_select_length mask w (hw.trans hlen.symm)).trans hcount,
      hrun w hw⟩
  · intro u hu
    obtain ⟨w, hw, he⟩ := cont_select_surjective mask u (hu.trans hcount.symm)
    exact ⟨w, hw.trans hlen, by rw [hrun w (hw.trans hlen), he]⟩

/-- The reverse compiler's complete polynomial envelope has the exact padded
`NTIME` form demanded by the audited statement, including zero certificate
coefficient, zero degree, and empty inputs.
**Proof sketch.** Bound `n+1` and `(n+1)^c` by `(n+1)^max(1,c)`, add their
coefficients, raise to `r`, then apply the proved `succ_pow_le`. -/
private lemma cont_guess_time_bound (C c K r n : ℕ) :
    K * (n + C * (n + 1) ^ c + 1) ^ r ≤
      (K * (C + 1) ^ r * 2 ^ (r * max 1 c)) * (n ^ (r * max 1 c) + 1) := by
  have hp : 0 < n + 1 := Nat.succ_pos n
  have h1 : n + 1 ≤ (n + 1) ^ max 1 c := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right hp (Nat.le_max_left 1 c)
  have hc : (n + 1) ^ c ≤ (n + 1) ^ max 1 c :=
    Nat.pow_le_pow_right hp (Nat.le_max_right 1 c)
  have hsum : n + C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ max 1 c := by
    have hm := Nat.mul_le_mul_left C hc
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    K * (n + C * (n + 1) ^ c + 1) ^ r ≤
        K * ((C + 1) * (n + 1) ^ max 1 c) ^ r :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_left hsum r)
    _ = (K * (C + 1) ^ r) * (n + 1) ^ (r * max 1 c) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (max 1 c) r, Nat.mul_assoc]
    _ ≤ (K * (C + 1) ^ r) * (2 ^ (r * max 1 c) * (n ^ (r * max 1 c) + 1)) :=
      Nat.mul_le_mul_left _ (succ_pow_le n (r * max 1 c))
    _ = _ := by ring

/-- An all-branch compiler with the stated complete polynomial envelope lands
in one fixed-degree `NTIME` component. Acceptance at the enlarged budget is
proved by all-branch truncation as well as accepting-branch padding. -/
private lemma cont_guess_normalize (L : Language Bool) (C c : ℕ)
    (h : ∃ (K r : ℕ) (N : FinNDTM Bool),
      N.DecidesInTime L (fun n => K * (n + C * (n + 1) ^ c + 1) ^ r)) :
    L ∈ ⋃ e : ℕ, NTIME fun n => n ^ e + 1 := by
  obtain ⟨K, r, N, hN⟩ := h
  refine Set.mem_iUnion.mpr ⟨r * max 1 c, K * (C + 1) ^ r * 2 ^ (r * max 1 c), N, ?_⟩
  intro x
  have ht := cont_guess_time_bound C c K r x.length
  refine ⟨(hN x).1.mono ht, ?_⟩
  exact (hN x).2.trans (acceptsWithin_iff_of_halts (hN x).1 ht).symm

/-- The proved unary polynomial generator supplies a concrete native guessing
phase for every exact certificate length. Its physical schedule is evaluated
on the unary input of length `n`, so it depends only on `n`, including when
`C=0`. This contract does not yet preserve an arbitrary original input or
run its verifier; those are obligations of the surrounding reverse compiler. -/
private lemma cont_poly_guess_phase (C c : ℕ) :
    ∃ (M : FinTM Bool) (A : ℕ), ∀ n : ℕ,
    let x := List.replicate n true
    let T := A * (n + 1) ^ (c + 1)
    (∀ w : List Bool, w.length = T → ∃ u : List Bool,
      u.length = C * (n + 1) ^ c ∧
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) u) ∧
    (∀ u : List Bool, u.length = C * (n + 1) ^ c → ∃ w : List Bool,
      w.length = T ∧
      (contGuessTM M).tm.runWith w ((contGuessTM M).tm.initCfg x) =
        contGuessCfg M (M.tm.runFrom (M.tm.initCfg x) T) u) := by
  obtain ⟨M, A, hM⟩ := computesFunInTime_polyUnary C c
  refine ⟨M, A, fun n => ?_⟩
  have h := cont_guess_coverage M (List.replicate n true)
    (List.replicate (C * (n + 1) ^ c) true) (A * (n + 1) ^ (c + 1)) (by
      simpa only [List.length_replicate] using hM (List.replicate n true))
  simpa only [List.length_replicate] using h

/-- Normalize each nonblank physical input read to `true`. The physical input
and its head are retained; source work symbols are not normalized. -/
private def b2UnaryTM (M : FinTM Bool) : FinTM Bool where
  k := M.k
  State := M.State
  tm := ⟨M.tm.q₀, fun q inp work => M.tm.tr q (inp.map fun _ => true) work⟩

/-- View an arbitrary-input configuration over the unary word of the same
length, leaving its state, work tapes, heads, and output unchanged. -/
private def b2UnaryCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg k Bool S (List.replicate x.length true) :=
  ⟨c.state, ⟨c.inputPos.val, by simp⟩,
    c.workTapes, c.workTapePos, c.output⟩

/-- Normalization preserves both input blanks and maps every interior symbol
to the corresponding unary symbol, including at empty input. -/
private lemma b2_unary_read {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) :
    (b2UnaryCfg c).inputSymbol = c.inputSymbol.map (fun _ => true) := by
  by_cases h0 : c.inputPos.val = 0 <;>
    by_cases h1 : c.inputPos.val = x.length + 1 <;>
    simp [Cfg.inputSymbol, b2UnaryCfg, Fin.ext_iff, h0, h1]

/-- Applying an action commutes with changing to an equal-length unary input:
native clamping uses only the length, and no work symbol is changed. -/
private lemma b2_unary_apply {k : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    b2UnaryCfg (a.apply c) = a.apply (b2UnaryCfg c) := by
  refine Cfg.ext rfl ?_ rfl rfl rfl
  apply Fin.ext
  simp only [b2UnaryCfg, Action.apply, moveInputPos, List.length_replicate]
  split <;> rfl

/-- One step of the input-normalized scheduler is exactly a native step on
the unary word, including the absorbing halted case. -/
private lemma b2_unary_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    b2UnaryCfg ((b2UnaryTM M).tm.step c) = M.tm.step (b2UnaryCfg c) := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, b2UnaryTM, b2UnaryCfg, hs]
  | some q =>
    simp only [MultiTapeTM.step, hs, b2UnaryTM]
    change b2UnaryCfg ((M.tm.tr q (c.inputSymbol.map fun _ => true)
      c.workTapeSymbols).apply c) = _
    rw [b2_unary_apply]
    have hs' : (b2UnaryCfg c).state = some q := hs
    simp only [hs', b2_unary_read]
    rfl

/-- Every elapsed time, not just a declared upper bound, has exactly the
unary scheduler configuration. Thus first halts and emission times can be
selected from the input length alone. -/
private lemma b2_unary_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ) :
    b2UnaryCfg ((b2UnaryTM M).tm.runFrom c t) =
      M.tm.runFrom (b2UnaryCfg c) t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, ih, b2_unary_step,
      MultiTapeTM.runFrom_succ_eq_step]

/-- The normalized scheduler's genuine startup corresponds to the genuine
unary startup, with blank work tapes and initial input head one. -/
private lemma b2_unary_initial (M : FinTM Bool) (x : List Bool) :
    b2UnaryCfg ((b2UnaryTM M).tm.initCfg x) =
      M.tm.initCfg (List.replicate x.length true) := by
  refine Cfg.ext rfl ?_ rfl rfl rfl
  apply Fin.ext
  simp [b2UnaryCfg, b2UnaryTM, MultiTapeTM.initCfg, Cfg.init]

/-- Normalizing input reads also preserves every emission position; no
assumption of value-independent timing is extracted from a function contract. -/
private lemma b2_unary_mask (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ) :
    contEmissionMask (b2UnaryTM M) c t = contEmissionMask M (b2UnaryCfg c) t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [contEmissionMask, contEmissionMask, ih, b2_unary_step]
    congr 1
    have hs' : (b2UnaryCfg c).state = c.state := rfl
    cases hs : c.state <;>
      simp only [MultiTapeTM.outputSymbol, b2UnaryTM, hs', hs, b2_unary_read]
    rfl

/-- A unary timed computation transfers to every original word of that
length, at exactly the same time and with exactly the same completed output. -/
private lemma b2_unary_computes (M : FinTM Bool) (x v : List Bool) (t : ℕ)
    (hM : M.ComputesInTime (List.replicate x.length true) v t) :
    (b2UnaryTM M).ComputesInTime x v t := by
  have hr := b2_unary_run M ((b2UnaryTM M).tm.initCfg x) t
  rw [b2_unary_initial] at hr
  have hc := (computesInTime_iff _ _ _ _).mp hM
  apply (computesInTime_iff _ _ _ _).mpr
  exact ⟨(congrArg Cfg.state hr).trans hc.1, (congrArg Cfg.output hr).trans hc.2⟩

/-- A total unary scheduler has a first halt depending only on input length.
The bound is used to prove existence, never as a native phase-dispatch clock.
**Proof sketch.** Choose the least halting time on each unary input. Absorption
identifies its output with the output at the given bound. Exact normalized
lockstep transfers the first halt and all earlier live states to every word
of that length. -/
private lemma b2_unary_first (M : FinTM Bool) (f : ℕ → List Bool) (T : ℕ → ℕ)
    (hM : ∀ n, M.ComputesInTime (List.replicate n true) (f n) (T n)) :
    ∃ τ : ℕ → ℕ, ∀ x : List Bool,
      τ x.length ≤ T x.length ∧
      (b2UnaryTM M).ComputesInTime x (f x.length) (τ x.length) ∧
      ∀ s < τ x.length, ((b2UnaryTM M).tm.runFrom
        ((b2UnaryTM M).tm.initCfg x) s).state ≠ none := by
  classical
  have hex (n : ℕ) : ∃ t, (M.tm.runFrom
      (M.tm.initCfg (List.replicate n true)) t).state = none :=
    ⟨T n, ((computesInTime_iff _ _ _ _).mp (hM n)).1⟩
  refine ⟨fun n => Nat.find (hex n), fun x => ?_⟩
  have hh := Nat.find_spec (hex x.length)
  have ht := Nat.find_min' (hex x.length)
    ((computesInTime_iff _ _ _ _).mp (hM x.length)).1
  have ho := M.tm.runFrom_output_eq_of_halt
    (M.tm.initCfg (List.replicate x.length true)) ht hh
  have hc : M.ComputesInTime (List.replicate x.length true) (f x.length)
      (Nat.find (hex x.length)) := (computesInTime_iff _ _ _ _).mpr
    ⟨hh, ho.symm.trans ((computesInTime_iff _ _ _ _).mp (hM x.length)).2⟩
  refine ⟨ht, b2_unary_computes M x _ _ hc, fun s hs hh' => ?_⟩
  have hr := congrArg Cfg.state (b2_unary_run M ((b2UnaryTM M).tm.initCfg x) s)
  rw [b2_unary_initial] at hr
  exact Nat.find_min (hex x.length) hs (hr.symm.trans hh')

/-- The host's four disjoint tape banks: scheduler, assembled input, verifier,
and verifier output. Each machine bank has a private final buffer slot. -/
private def b2Slots {α : Type} (S V : FinTM Bool) (s : Fin S.k → α)
    (input : α) (v : Fin V.k → α) (output : α) :
    Fin ((S.k + 1) + (V.k + 1)) → α :=
  Fin.addCases
    (fun i => if h : i.val < S.k then s ⟨i, h⟩ else input)
    (fun i => if h : i.val < V.k then v ⟨i, h⟩ else output)

/-- Native reverse host. Administrative states copy the input, rewind its
physical head, and rewind the assembled buffer. The scheduler reads the
normalized physical input; its emissions append choices to the copied input.
The verifier uses only its own bank and the guarded virtual assembly input.
Both tables are definitionally identical outside live guessing states. -/
private def b2Host (S V : FinTM Bool) : FinNDTM Bool where
  k := (S.k + 1) + (V.k + 1)
  State := Fin 3 ⊕ (Option S.State ⊕ (Option V.State × Bool × Option Bool))
  tm :=
    { q₀ := .inl 0
      tr := fun bit q inp work => match q with
        | .inl q =>
          if q = 0 then
            match inp with
            | some b =>
              ⟨1, b2Slots S V (fun _ => (none, 0)) (some (some b), 1)
                (fun _ => (none, 0)) (none, 0), none, some (.inl 0)⟩
            | none => controlAction (-1) (some (.inl 1))
          else if q = 1 then
            match inp with
            | some _ => controlAction (-1) (some (.inl 1))
            | none => controlAction 1 (some (.inr (.inl (some S.tm.q₀))))
          else
            let inp := work (Fin.castAdd (V.k + 1) (Fin.last S.k))
            ⟨0, b2Slots S V (fun _ => (none, 0))
              (none, if inp.isSome then -1 else 1)
              (fun _ => (none, 0)) (none, 0), none,
              some (if inp.isSome then .inl 2
                else .inr (.inr (some V.tm.q₀, true, none)))⟩
        | .inr (.inl q) => match q with
          | none =>
            ⟨0, b2Slots S V (fun _ => (none, 0)) (none, -1)
              (fun _ => (none, 0)) (none, 0), none, some (.inl 2)⟩
          | some q =>
            leftAction (V.k + 1) (fun q => .inr (.inl q))
              ((contGuessTM (b2UnaryTM S)).tm.tr bit (some q) inp
                (fun i => work (Fin.castAdd (V.k + 1) i)))
        | .inr (.inr (q, tag, summary)) => match q with
          | none =>
            ⟨0, fun _ => (none, 0), some (decide (summary = some true)), none⟩
          | some q =>
            let inp := work (Fin.castAdd (V.k + 1) (Fin.last S.k))
            let a := V.tm.tr q inp
              (fun i => work (Fin.natAdd (S.k + 1) i.castSucc))
            let m := virtualMove tag inp a.inputTape
            ⟨0, b2Slots S V (fun _ => (none, 0)) (none, m) a.workTapes
              (a.output.map some, if a.output.isSome then 1 else 0), none,
              some (.inr (.inr (a.state, virtualNextTag tag m,
                captureEmission summary a.output)))⟩ }

/-- Embed the guessing phase with the original word already on its buffer.
The verifier bank and its output capture remain blank throughout this phase. -/
private def b2GuessCfg (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (u : List Bool) :
    Cfg (b2Host S V).k Bool (b2Host S V).State x :=
  leftCfg (fun q => .inr (.inl q)) (contGuessCfg (b2UnaryTM S) c (x ++ u))
    (fun _ _ => none) (fun _ => 0)

/-- Outside a live guessing state, the two native transition tables coincide
by the definition of the host, for every possible tuple of symbols. -/
private lemma b2_tables_coincide (S V : FinTM Bool) (q : (b2Host S V).State)
    (hq : ∀ s, q ≠ .inr (.inl (some s))) (inp : Option Bool)
    (work : Fin (b2Host S V).k → Option Bool) :
    (b2Host S V).tm.tr false q inp work = (b2Host S V).tm.tr true q inp work := by
  rcases q with q | (q | q)
  · rfl
  · cases q with
    | none => rfl
    | some q => exact False.elim (hq q rfl)
  · rfl

/-- A live host guessing step is the banked native guessing transition with
an inactive verifier bank. In particular a halting emission is appended before
the host enters its scheduler-return state.
**Proof sketch.** The left-bank projection has precisely the standalone
phase's reads. The library's disjoint-bank action identity embeds its step;
the predecessor's guessing-step invariant supplies the exact appended bit. -/
private lemma b2_guess_step (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (hc : c.state ≠ none) (u : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2GuessCfg S V c u) =
      b2GuessCfg S V ((b2UnaryTM S).tm.step c)
        (u ++ if ((b2UnaryTM S).tm.outputSymbol c).isSome then [bit] else []) := by
  cases hs : c.state with
  | none => exact False.elim (hc hs)
  | some q =>
    let g := contGuessCfg (b2UnaryTM S) c (x ++ u)
    have hstate : (b2GuessCfg S V c u).state = some (.inr (.inl (some q))) := by
      simp [b2GuessCfg, leftCfg, contGuessCfg, hs]
    have hi : (b2GuessCfg S V c u).inputSymbol = g.inputSymbol := rfl
    have hw : (fun i : Fin (S.k + 1) => (b2GuessCfg S V c u).workTapeSymbols
        (Fin.castAdd (V.k + 1) i)) = g.workTapeSymbols := by
      funext i
      simp [b2GuessCfg, leftCfg, Cfg.workTapeSymbols, g]
    unfold NDTM.stepWith
    rw [hstate]
    dsimp only [b2Host]
    simp only [hi]
    simp only [b2GuessCfg, leftCfg, Cfg.workTapeSymbols, Fin.addCases_left]
    change (leftAction (V.k + 1) (fun q : Option S.State => (Sum.inr (Sum.inl q) : (b2Host S V).State))
      ((contGuessTM (b2UnaryTM S)).tm.tr bit (some q) g.inputSymbol g.workTapeSymbols)).apply
        (leftCfg (fun q : Option S.State => (Sum.inr (Sum.inl q) : (b2Host S V).State)) g (fun _ _ => none) (fun _ => 0)) = _
    rw [leftCfg_apply]
    have hg : ((contGuessTM (b2UnaryTM S)).tm.tr bit (some q)
        g.inputSymbol g.workTapeSymbols).apply g =
        (contGuessTM (b2UnaryTM S)).tm.stepWith bit g := by
      simp [NDTM.stepWith, g, contGuessCfg, hs]
    rw [hg]
    dsimp only [g]
    rw [cont_guess_step]
    simp only [List.append_assoc]
    rfl

/-- The host follows the standalone emission mask until the actual first
scheduler halt. The preserved original input is a prefix of the assembly
buffer, and every other bank remains isolated.
**Proof sketch.** Induct on the physical choice word. The strict liveness
guard permits one guessing step, including the final source-halting step;
shift the guard by one for the remaining choices. -/
private lemma b2_guess_run (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (u w : List Bool)
    (hlive : ∀ s < w.length, ((b2UnaryTM S).tm.runFrom c s).state ≠ none) :
    (b2Host S V).tm.runWith w (b2GuessCfg S V c u) =
      b2GuessCfg S V ((b2UnaryTM S).tm.runFrom c w.length)
        (u ++ contSelect (contEmissionMask (b2UnaryTM S) c w.length) w) := by
  induction w generalizing c u with
  | nil => simp [contEmissionMask, contSelect]
  | cons bit w ih =>
    have hc : c.state ≠ none := hlive 0 (by simp)
    have ht : ∀ s < w.length,
        ((b2UnaryTM S).tm.runFrom ((b2UnaryTM S).tm.step c) s).state ≠ none := by
      intro s hs
      rw [← MultiTapeTM.runFrom_succ_eq_step]
      exact hlive (s + 1) (by simpa using hs)
    rw [NDTM.runWith_cons, b2_guess_step S V c hc, ih _ _ ht]
    simp only [List.length_cons, contEmissionMask, contSelect,
      MultiTapeTM.runFrom_succ_eq_step, List.append_assoc]

/-- Loader configuration: all machine tapes are blank and only the assembly
buffer is populated. The physical input is retained verbatim. -/
private def b2LoadCfg (S V : FinTM Bool) {x : List Bool} (q : Fin 3)
    (p : Fin (x.length + 2)) (pre : List Bool) (j : ℤ) :
    Cfg (b2Host S V).k Bool (b2Host S V).State x :=
  ⟨some (.inl q), p,
    b2Slots S V (fun _ _ => none) (bufferTape pre) (fun _ _ => none) (fun _ => none),
    b2Slots S V (fun _ => 0) j (fun _ => 0) 0, []⟩

/-- One copy transition appends exactly the next original input bit; its
physical choice is ignored and every scheduler/verifier tape stays blank. -/
private lemma b2_copy_step (S V : FinTM Bool) (x : List Bool) (i : ℕ)
    (hi : i < x.length) (bit : Bool) :
    (b2Host S V).tm.stepWith bit
      (b2LoadCfg S V (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i) =
        b2LoadCfg S V (x := x) 0 ⟨i + 2, by omega⟩ (x.take (i + 1)) (i + 1) := by
  have hr : (b2LoadCfg S V (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i).inputSymbol =
      some x[i] := inputSymbolInner i (by simp [b2LoadCfg]; omega) hi
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 0) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_pos rfl, hr]
  dsimp only
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 2
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    refine Fin.addCases ?_ ?_ j <;> intro j
    · by_cases hj : j.val < S.k
      · simp [b2LoadCfg, b2Slots, hj]
      · simp only [b2LoadCfg, b2Slots, Action.apply, Fin.addCases_left, dif_neg hj]
        rw [List.take_succ_eq_append_getElem hi, bufferTape_append,
          List.length_take_of_le (Nat.le_of_lt hi)]
    · by_cases hj : j.val < V.k <;> simp [b2LoadCfg, b2Slots]
  · funext j
    refine Fin.addCases ?_ ?_ j <;> intro j
    · by_cases hj : j.val < S.k <;> simp [b2LoadCfg, b2Slots, hj]
    · by_cases hj : j.val < V.k <;> simp [b2LoadCfg, b2Slots]

/-- The original input prefix is copied in exactly one transition per bit,
independently of all physical choices. Induction on the consumed choices
uses the one-step copier and never reads the guessed-data buffer. -/
private lemma b2_copy_run (S V : FinTM Bool) (x w : List Bool)
    (i : ℕ) (hi : i + w.length ≤ x.length) :
    (b2Host S V).tm.runWith w
      (b2LoadCfg S V (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i) =
        b2LoadCfg S V (x := x) 0 ⟨i + w.length + 1, by omega⟩
          (x.take (i + w.length)) (i + w.length) := by
  induction w generalizing i with
  | nil => simp
  | cons bit w ih =>
    rw [NDTM.runWith_cons, b2_copy_step S V x i (by simp only [List.length_cons] at hi; omega)]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.cast_add,
      add_assoc, add_comm, add_left_comm] using
      ih (i + 1) (by simp only [List.length_cons] at hi; omega)

/-- At the left blank, one choice-independent transition starts the scheduler
at head one with blank source tapes and the preserved original input buffer. -/
private lemma b2_rewind_done (S V : FinTM Bool) (x : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2LoadCfg S V (x := x) 1 0 x x.length) =
      b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) [] := by
  have hr : (b2LoadCfg S V (x := x) 1 0 x x.length).inputSymbol = none := by
    simp [b2LoadCfg, Cfg.inputSymbol]
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 1) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl, hr, controlAction_apply]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [b2LoadCfg, b2GuessCfg, leftCfg, contGuessCfg, MultiTapeTM.initCfg,
      Cfg.init, moveInputPos]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2LoadCfg, b2Slots, b2GuessCfg, leftCfg, contGuessCfg, b2UnaryTM, h,
          MultiTapeTM.initCfg, Cfg.init]
    · by_cases h : i.val < V.k <;>
        simp [b2LoadCfg, b2Slots, b2GuessCfg, leftCfg, contGuessCfg]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2LoadCfg, b2Slots, b2GuessCfg, leftCfg, contGuessCfg, b2UnaryTM, h,
          MultiTapeTM.initCfg, Cfg.init]
    · by_cases h : i.val < V.k <;>
        simp [b2LoadCfg, b2Slots, b2GuessCfg, leftCfg, contGuessCfg]

/-- Each interior rewind transition moves the physical input head left by
one, preserving the copied word and both blank machine banks. -/
private lemma b2_rewind_step (S V : FinTM Bool) (x : List Bool) (j : ℕ)
    (hj : j < x.length) (bit : Bool) :
    (b2Host S V).tm.stepWith bit
      (b2LoadCfg S V (x := x) 1 ⟨j + 1, by omega⟩ x x.length) =
        b2LoadCfg S V (x := x) 1 ⟨j, by omega⟩ x x.length := by
  have hr : (b2LoadCfg S V (x := x) 1 ⟨j + 1, by omega⟩ x x.length).inputSymbol =
      some x[j] := inputSymbolInner j (by simp [b2LoadCfg]; omega) hj
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 1) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_neg (by decide : (1 : Fin 3) ≠ 0), if_pos rfl, hr, controlAction_apply]
  refine Cfg.ext rfl ?_ rfl rfl rfl
  apply Fin.ext
  change (moveInputPos (⟨j + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = j
  rw [moveInputPos_neg_val]
  simp

/-- The physical rewind reaches the genuine scheduler startup in exactly
`j+1` steps from position `j`. Decreasing-position induction applies to
every choice word, including the empty-input left blank. -/
private lemma b2_rewind_run (S V : FinTM Bool) (x : List Bool) (j : ℕ)
    (hj : j ≤ x.length) (w : List Bool) (hw : w.length = j + 1) :
    (b2Host S V).tm.runWith w
      (b2LoadCfg S V (x := x) 1 ⟨j, by omega⟩ x x.length) =
        b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) [] := by
  induction j generalizing w with
  | zero =>
    cases w with
    | nil => simp at hw
    | cons bit w =>
      have he : w = [] := by simpa using hw
      subst w
      exact b2_rewind_done S V x bit
  | succ j ih =>
    cases w with
    | nil => simp at hw
    | cons bit w =>
      rw [NDTM.runWith_cons, b2_rewind_step S V x j (by omega)]
      exact ih (by omega) w (by simpa using hw)

/-- The host's blank-tape initial configuration is exactly the empty loader
configuration, rather than an assumed prepared assembly tape. -/
private lemma b2_initial (S V : FinTM Bool) (x : List Bool) :
    (b2Host S V).tm.initCfg x = b2LoadCfg S V (x := x) 0 1 [] 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2LoadCfg, b2Slots]
    · by_cases h : i.val < V.k <;> simp [b2LoadCfg, b2Slots]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2LoadCfg, b2Slots]
    · by_cases h : i.val < V.k <;> simp [b2LoadCfg, b2Slots]

/-- The right input blank triggers a mandatory left move before the rewind
scan, so an empty input is handled without confusing its two boundaries. -/
private lemma b2_copy_done (S V : FinTM Bool) (x : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit
      (b2LoadCfg S V (x := x) 0 ⟨x.length + 1, by omega⟩ x x.length) =
        b2LoadCfg S V (x := x) 1 ⟨x.length, by omega⟩ x x.length := by
  have hr : (b2LoadCfg S V (x := x) 0 ⟨x.length + 1, by omega⟩ x x.length).inputSymbol =
      none := (inputSymbol_at _ x.length (le_refl _) rfl).trans (by simp)
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 0) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_pos rfl, hr, controlAction_apply]
  refine Cfg.ext rfl ?_ rfl rfl rfl
  apply Fin.ext
  change (moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = x.length
  rw [moveInputPos_neg_val]
  simp

/-- Startup preserves the original input and installs the normalized scheduler
after exactly `2*|x|+2` physical choices, all ignored.
**Proof sketch.** Split off `|x|` choices for the copier. One blank transition
starts the rewind; the remaining `|x|+1` choices return the input head to one
with blank scheduler/verifier banks and assembly buffer exactly `x`. -/
private lemma b2_start (S V : FinTM Bool) (x w : List Bool)
    (hw : w.length = 2 * x.length + 2) :
    (b2Host S V).tm.runWith w ((b2Host S V).tm.initCfg x) =
      b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) [] := by
  have hp : (w.take x.length).length = x.length := List.length_take_of_le (by omega)
  have hcopy : (b2Host S V).tm.runWith (w.take x.length)
      ((b2Host S V).tm.initCfg x) =
        b2LoadCfg S V (x := x) 0 ⟨x.length + 1, by omega⟩ x x.length := by
    rw [b2_initial]
    simpa [hp] using b2_copy_run S V x (w.take x.length) 0 (by omega)
  have hdlen : (w.drop x.length).length = x.length + 2 := by
    rw [List.length_drop, hw]
    omega
  cases hd : w.drop x.length with
  | nil => simp [hd] at hdlen
  | cons bit rest =>
    have hrest : rest.length = x.length + 1 := by simpa [hd] using hdlen
    have hsplit : w = w.take x.length ++ bit :: rest := by
      rw [← hd, List.take_append_drop]
    rw [hsplit, NDTM.runWith_append, hcopy, NDTM.runWith_cons, b2_copy_done]
    exact b2_rewind_run S V x x.length (le_refl _) rest hrest

/-- A captured guessing word is determined by its tape contents. This reads
every nonnegative tape cell, so it also covers the zero-length word. -/
private lemma b2_guess_word_injective (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) {u v : List Bool}
    (h : contGuessCfg M c u = contGuessCfg M c v) : u = v := by
  apply List.ext_getElem?
  intro i
  have he := congrArg (fun g => g.workTapes (Fin.last M.k) (i : ℤ)) h
  simpa [contGuessCfg] using he

/-- Reuse the predecessor's native coverage at the actual first scheduler
halt, and transfer its full-word extraction/coverage into the host. The
assembly buffer has original prefix `x` and exactly the extracted suffix.
**Proof sketch.** Standalone coverage supplies the guessed word. Equality of
its capture tape identifies that word with physical-mask selection; the
guarded host run then gives the same selection after the preserved prefix. -/
private lemma b2_guess_coverage (S V : FinTM Bool) (x v : List Bool) (T : ℕ)
    (hS : (b2UnaryTM S).ComputesInTime x v T)
    (hlive : ∀ s < T, ((b2UnaryTM S).tm.runFrom
      ((b2UnaryTM S).tm.initCfg x) s).state ≠ none) :
    (∀ w : List Bool, w.length = T → ∃ u : List Bool, u.length = v.length ∧
      (b2Host S V).tm.runWith w
        (b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) []) =
          b2GuessCfg S V ((b2UnaryTM S).tm.runFrom
            ((b2UnaryTM S).tm.initCfg x) T) u) ∧
    (∀ u : List Bool, u.length = v.length → ∃ w : List Bool, w.length = T ∧
      (b2Host S V).tm.runWith w
        (b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) []) =
          b2GuessCfg S V ((b2UnaryTM S).tm.runFrom
            ((b2UnaryTM S).tm.initCfg x) T) u) := by
  have hcov := cont_guess_coverage (b2UnaryTM S) x v T hS
  have htransfer (w u : List Bool) (hw : w.length = T)
      (hr : (contGuessTM (b2UnaryTM S)).tm.runWith w
        ((contGuessTM (b2UnaryTM S)).tm.initCfg x) =
          contGuessCfg (b2UnaryTM S) ((b2UnaryTM S).tm.runFrom
            ((b2UnaryTM S).tm.initCfg x) T) u) :
      (b2Host S V).tm.runWith w
        (b2GuessCfg S V ((b2UnaryTM S).tm.initCfg x) []) =
          b2GuessCfg S V ((b2UnaryTM S).tm.runFrom
            ((b2UnaryTM S).tm.initCfg x) T) u := by
    rw [cont_guess_initial, cont_guess_run, hw, List.nil_append] at hr
    have hu := b2_guess_word_injective _ _ hr
    rw [b2_guess_run S V _ [] w (by simpa [hw] using hlive), hw, List.nil_append, hu]
  constructor
  · intro w hw
    obtain ⟨u, hu, hr⟩ := hcov.1 w hw
    exact ⟨u, hu, htransfer w u hw hr⟩
  · intro u hu
    obtain ⟨w, hw, hr⟩ := hcov.2 u hu
    exact ⟨w, hw, htransfer w u hw hr⟩

/-- Verifier invariant: its input is the assembly buffer with a guarded
virtual head, its own source tapes are exact, all emitted bits are captured,
and the scheduler's bank remains unchanged. Physical output is still empty. -/
private def b2VerifyCfg (S V : FinTM Bool) {x y : List Bool}
    (c : Cfg V.k Bool V.State y) (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin S.k → ℤ → Option Bool) (heads : Fin S.k → ℤ) :
    Cfg (b2Host S V).k Bool (b2Host S V).State x :=
  ⟨some (.inr (.inr (c.state, tag, capturedSummary c.output))), p,
    b2Slots S V tapes (bufferTape y) c.workTapes (bufferTape c.output),
    b2Slots S V heads ((c.inputPos.val : ℤ) - 1) c.workTapePos c.output.length, []⟩

/-- The assembled-input rewind retains the completed scheduler bank and
the blank verifier bank. Its assembly head is explicitly recorded. -/
private def b2ReadyCfg (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (y : List Bool) (j : ℤ) :
    Cfg (b2Host S V).k Bool (b2Host S V).State x :=
  ⟨some (.inl 2), c.inputPos,
    b2Slots S V c.workTapes (bufferTape y) (fun _ _ => none) (fun _ => none),
    b2Slots S V c.workTapePos j (fun _ => 0) 0, []⟩

/-- A live verifier step reads the exact assembly input, clamps both virtual
boundaries correctly, and captures even an emission on a halting transition.
Its physical choice is ignored.
**Proof sketch.** The assembly-buffer read is the source input read. The
library virtual-head identity supplies the new head and boundary tag. Check
the scheduler/assembly and verifier/capture banks separately; the capture
append identity and finite-summary update retain the whole emitted word. -/
private lemma b2_verify_step (S V : FinTM Bool) {x y : List Bool}
    (c : Cfg V.k Bool V.State y) (hc : c.state ≠ none)
    (tag : Bool) (htag : VirtualTag c.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin S.k → ℤ → Option Bool) (heads : Fin S.k → ℤ) (bit : Bool) :
    ∃ tag', VirtualTag (V.tm.step c).inputPos tag' ∧
      (b2Host S V).tm.stepWith bit (b2VerifyCfg S V c tag p tapes heads) =
        b2VerifyCfg S V (V.tm.step c) tag' p tapes heads := by
  cases hs : c.state with
  | none => exact False.elim (hc hs)
  | some q =>
    let a := V.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := virtualMove tag c.inputSymbol a.inputTape
    have hm := virtualMove_correct c tag htag a.inputTape
    have hstep : V.tm.step c = a.apply c := by simp [MultiTapeTM.step, hs, a]
    have hi : (b2VerifyCfg S V c tag p tapes heads).workTapeSymbols
        (Fin.castAdd (V.k + 1) (Fin.last S.k)) = c.inputSymbol := by
      simp [b2VerifyCfg, b2Slots, Cfg.workTapeSymbols, bufferTape_inputSymbol]
    have hw : (fun i : Fin V.k => (b2VerifyCfg S V c tag p tapes heads).workTapeSymbols
        (Fin.natAdd (S.k + 1) i.castSucc)) = c.workTapeSymbols := by
      funext i
      simp [b2VerifyCfg, b2Slots, Cfg.workTapeSymbols, i.isLt]
    refine ⟨virtualNextTag tag m, ?_, ?_⟩
    · simpa only [hstep, Action.apply] using hm.2
    · rw [hstep]
      unfold NDTM.stepWith
      change ((b2Host S V).tm.tr bit
        (.inr (.inr (c.state, tag, capturedSummary c.output))) _ _).apply _ = _
      rw [hs]
      dsimp only [b2Host]
      rw [hi, hw]
      change (Action.mk 0 (b2Slots S V (fun _ => (none, 0)) (none, m) a.workTapes
        (a.output.map some, if a.output.isSome then 1 else 0)) none
        (some (.inr (.inr (a.state, virtualNextTag tag m,
          captureEmission (capturedSummary c.output) a.output))))).apply
            (b2VerifyCfg S V c tag p tapes heads) = _
      refine Cfg.ext (by simp [b2VerifyCfg, captureEmission_correct])
        (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro i
        · by_cases h : i.val < S.k <;> simp [b2VerifyCfg, b2Slots, h]
        · by_cases h : i.val < V.k
          · simp [b2VerifyCfg, b2Slots, h]
          · cases he : a.output <;> simp [b2VerifyCfg, b2Slots, h, he, bufferTape_append]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro i
        · by_cases h : i.val < S.k
          · simp [b2VerifyCfg, b2Slots, h]
          · simpa [b2VerifyCfg, b2Slots, h, m] using hm.1
        · by_cases h : i.val < V.k
          · simp [b2VerifyCfg, b2Slots, h]
          · cases he : a.output <;> simp [b2VerifyCfg, b2Slots, h, he]

/-- Every physical choice word simulates the same verifier until its first
halt, with exact output capture and a valid boundary tag. Induction applies
the choice-independent one-step invariant and shifts the liveness guard. -/
private lemma b2_verify_run (S V : FinTM Bool) {x y : List Bool}
    (c : Cfg V.k Bool V.State y) (tag : Bool) (htag : VirtualTag c.inputPos tag)
    (p : Fin (x.length + 2)) (tapes : Fin S.k → ℤ → Option Bool)
    (heads : Fin S.k → ℤ) (w : List Bool)
    (hlive : ∀ s < w.length, (V.tm.runFrom c s).state ≠ none) :
    ∃ tag', VirtualTag (V.tm.runFrom c w.length).inputPos tag' ∧
      (b2Host S V).tm.runWith w (b2VerifyCfg S V c tag p tapes heads) =
        b2VerifyCfg S V (V.tm.runFrom c w.length) tag' p tapes heads := by
  induction w generalizing c tag with
  | nil => exact ⟨tag, htag, rfl⟩
  | cons bit w ih =>
    obtain ⟨tag', htag', hs⟩ := b2_verify_step S V c (hlive 0 (by simp))
      tag htag p tapes heads bit
    have ht : ∀ s < w.length, (V.tm.runFrom (V.tm.step c) s).state ≠ none := by
      intro s hs
      rw [← MultiTapeTM.runFrom_succ_eq_step]
      exact hlive (s + 1) (by simpa using hs)
    obtain ⟨tag'', htag'', hr⟩ := ih (V.tm.step c) tag' htag' ht
    refine ⟨tag'', ?_, ?_⟩
    · simpa only [List.length_cons, MultiTapeTM.runFrom_succ_eq_step] using htag''
    · rw [NDTM.runWith_cons, hs, hr]
      simp only [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]

/-- After the verifier halts, one physical transition emits exactly one
verdict bit and halts the host. Acceptance tests the entire captured word. -/
private lemma b2_verify_finish (S V : FinTM Bool) {x y : List Bool}
    (c : Cfg V.k Bool V.State y) (hc : c.state = none) (tag : Bool)
    (p : Fin (x.length + 2)) (tapes : Fin S.k → ℤ → Option Bool)
    (heads : Fin S.k → ℤ) (bit : Bool) :
    let out := (b2Host S V).tm.stepWith bit (b2VerifyCfg S V c tag p tapes heads)
    out.state = none ∧ out.output = [decide (c.output = [true])] := by
  simp [NDTM.stepWith, b2Host, b2VerifyCfg, hc, capturedSummary_true]

/-- The actual scheduler-return state dispatches to assembly rewind. This
transition is available only after the represented scheduler has halted. -/
private lemma b2_guess_return (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (hc : c.state = none) (u : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2GuessCfg S V c u) =
      b2ReadyCfg S V c (x ++ u) ((x ++ u).length - 1 : ℤ) := by
  have hs : (b2GuessCfg S V c u).state = some (.inr (.inl none)) := by
    simp [b2GuessCfg, leftCfg, contGuessCfg, hc]
  unfold NDTM.stepWith
  rw [hs]
  dsimp only [b2Host]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2GuessCfg, leftCfg, contGuessCfg, b2UnaryTM, b2ReadyCfg, b2Slots, h]
    · by_cases h : i.val < V.k <;>
        simp [b2GuessCfg, leftCfg, b2ReadyCfg, b2Slots]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2GuessCfg, leftCfg, contGuessCfg, b2UnaryTM, b2ReadyCfg, b2Slots, h,
          sub_eq_add_neg]
    · by_cases h : i.val < V.k <;>
        simp [b2GuessCfg, leftCfg, b2ReadyCfg, b2Slots]

/-- The assembly rewind moves left across a populated cell while retaining
the entire assembled word and the completed scheduler configuration. -/
private lemma b2_ready_step (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (y : List Bool) (j : ℕ)
    (hj : j < y.length) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2ReadyCfg S V c y j) =
      b2ReadyCfg S V c y ((j : ℤ) - 1) := by
  have hr : (b2ReadyCfg S V c y j).workTapeSymbols
      (Fin.castAdd (V.k + 1) (Fin.last S.k)) = some y[j] := by
    simp [b2ReadyCfg, b2Slots, Cfg.workTapeSymbols, List.getElem?_eq_getElem hj]
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 2) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_neg (by decide : (2 : Fin 3) ≠ 0),
    if_neg (by decide : (2 : Fin 3) ≠ 1), hr]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2ReadyCfg, b2Slots, h]
    · by_cases h : i.val < V.k <;> simp [b2ReadyCfg, b2Slots]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2ReadyCfg, b2Slots, h, sub_eq_add_neg]
    · by_cases h : i.val < V.k <;> simp [b2ReadyCfg, b2Slots]

/-- The assembly's left blank starts the verifier at its genuine initial
configuration: virtual head one, blank source tapes, and empty captured output.
This applies equally to an empty assembled input. -/
private lemma b2_ready_done (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (y : List Bool) (bit : Bool) :
    (b2Host S V).tm.stepWith bit (b2ReadyCfg S V c y (-1)) =
      b2VerifyCfg S V (V.tm.initCfg y) true c.inputPos c.workTapes c.workTapePos := by
  have hr : (b2ReadyCfg S V c y (-1)).workTapeSymbols
      (Fin.castAdd (V.k + 1) (Fin.last S.k)) = none := by
    simp [b2ReadyCfg, b2Slots, Cfg.workTapeSymbols]
  unfold NDTM.stepWith
  change ((b2Host S V).tm.tr bit (.inl 2) _ _).apply _ = _
  dsimp only [b2Host]
  rw [if_neg (by decide : (2 : Fin 3) ≠ 0),
    if_neg (by decide : (2 : Fin 3) ≠ 1), hr]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;> simp [b2ReadyCfg, b2VerifyCfg, b2Slots, h]
    · by_cases h : i.val < V.k <;>
        simp [b2ReadyCfg, b2VerifyCfg, b2Slots, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i
    · by_cases h : i.val < S.k <;>
        simp [b2ReadyCfg, b2VerifyCfg, b2Slots, h, MultiTapeTM.initCfg, Cfg.init]
    · by_cases h : i.val < V.k <;>
        simp [b2ReadyCfg, b2VerifyCfg, b2Slots, MultiTapeTM.initCfg, Cfg.init]

/-- Assembly rewind takes exactly `j+1` transitions from head `j-1`, with
every physical choice ignored. Decreasing-head induction ends with the
proper verifier startup, including the empty-buffer case. -/
private lemma b2_ready_run (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (y : List Bool) (j : ℕ) (hj : j ≤ y.length)
    (w : List Bool) (hw : w.length = j + 1) :
    (b2Host S V).tm.runWith w (b2ReadyCfg S V c y ((j : ℤ) - 1)) =
      b2VerifyCfg S V (V.tm.initCfg y) true c.inputPos c.workTapes c.workTapePos := by
  induction j generalizing w with
  | zero =>
    cases w with
    | nil => simp at hw
    | cons bit w =>
      have he : w = [] := by simpa using hw
      subst w
      simpa using b2_ready_done S V c y bit
  | succ j ih =>
    cases w with
    | nil => simp at hw
    | cons bit w =>
      have he : ((j + 1 : ℕ) : ℤ) - 1 = j := by omega
      rw [NDTM.runWith_cons, he, b2_ready_step S V c y j (by omega)]
      exact ih (by omega) w (by simpa using hw)

/-- From an actual scheduler halt, `|x++u|+2` transitions install the
relocated verifier. The guessed suffix is already appended to the preserved
prefix, so assembly needs only a rewind and dispatch. -/
private lemma b2_assembly (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (hc : c.state = none) (u w : List Bool)
    (hw : w.length = (x ++ u).length + 2) :
    (b2Host S V).tm.runWith w (b2GuessCfg S V c u) =
      b2VerifyCfg S V (V.tm.initCfg (x ++ u)) true c.inputPos c.workTapes c.workTapePos := by
  cases w with
  | nil => simp at hw
  | cons bit w =>
    rw [NDTM.runWith_cons, b2_guess_return S V c hc]
    exact b2_ready_run S V c (x ++ u) (x ++ u).length (le_refl _) w (by simpa using hw)

/-- Every branch of the verifier phase halts with its single verdict within
the source budget plus one. Actual first halts may depend on the assembled
certificate; the declared upper bound is common.
**Proof sketch.** Take the source's first halt, simulate the corresponding
choice prefix, and execute one verdict transition. All remaining choices
are absorbed by the halted host. Output uniqueness identifies the completed
source output with its specified singleton. -/
private lemma b2_verify_timed (S V : FinTM Bool) {x : List Bool}
    (y : List Bool) (b : Bool) (T : ℕ) (hV : V.ComputesInTime y [b] T)
    (p : Fin (x.length + 2)) (tapes : Fin S.k → ℤ → Option Bool)
    (heads : Fin S.k → ℤ) (w : List Bool) (hw : w.length = T + 1) :
    let out := (b2Host S V).tm.runWith w
      (b2VerifyCfg S V (V.tm.initCfg y) true p tapes heads)
    out.state = none ∧ out.output = [b] := by
  classical
  have hex : ∃ t, (V.tm.runFrom (V.tm.initCfg y) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hV).1⟩
  let t := Nat.find hex
  let c := V.tm.runFrom (V.tm.initCfg y) t
  have ht : t ≤ T := Nat.find_min' hex ((computesInTime_iff _ _ _ _).mp hV).1
  have hc : c.state = none := Nat.find_spec hex
  have hcomp : V.ComputesInTime y c.output t :=
    (computesInTime_iff _ _ _ _).mpr ⟨hc, rfl⟩
  have ho : c.output = [b] := hcomp.output_unique hV
  have hp : (w.take t).length = t := List.length_take_of_le (by omega)
  obtain ⟨tag, _, hr⟩ := b2_verify_run S V (V.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (w.take t)
    (fun s hs => Nat.find_min hex (show s < t from hp ▸ hs))
  rw [hp] at hr
  have hlen : 0 < (w.drop t).length := by rw [List.length_drop]; omega
  cases hd : w.drop t with
  | nil => simp [hd] at hlen
  | cons bit rest =>
    have hf := b2_verify_finish S V c hc tag p tapes heads bit
    have hout : ((b2Host S V).tm.stepWith bit
        (b2VerifyCfg S V c tag p tapes heads)).output = [b] := by
      rw [hf.2, ho]
      cases b <;> simp
    have hsplit : w = w.take t ++ bit :: rest := by rw [← hd, List.take_append_drop]
    dsimp only
    rw [hsplit, NDTM.runWith_append, hr, NDTM.runWith_cons,
      NDTM.runWith_of_halt _ hf.1]
    exact ⟨hf.1, hout⟩

/-- Assembly and verification terminate on every suffix choice word at a
common bound and emit the verifier's single decision bit.
**Proof sketch.** Split the physical word at the exact assembly-rewind
length; the rest has the verifier budget plus its verdict transition. Apply
the two timed phase contracts in order. -/
private lemma b2_finish (S V : FinTM Bool) {x : List Bool}
    (c : Cfg S.k Bool S.State x) (hc : c.state = none) (u : List Bool)
    (b : Bool) (T : ℕ) (hV : V.ComputesInTime (x ++ u) [b] T)
    (w : List Bool) (hw : w.length = (x ++ u).length + 2 + (T + 1)) :
    let out := (b2Host S V).tm.runWith w (b2GuessCfg S V c u)
    out.state = none ∧ out.output = [b] := by
  let a := (x ++ u).length + 2
  have hp : (w.take a).length = a := List.length_take_of_le (by dsimp [a]; omega)
  have ht : (w.drop a).length = T + 1 := by rw [List.length_drop, hw]; dsimp [a]; omega
  have hr := b2_assembly S V c hc u (w.take a) hp
  have hf := b2_verify_timed S V (x ++ u) b T hV c.inputPos c.workTapes
    c.workTapePos (w.drop a) ht
  dsimp only at hf ⊢
  rw [← hr, ← NDTM.runWith_append, List.take_append_drop] at hf
  exact hf

/-- The integrated host has both branch extraction and witness coverage at
one common budget. Guess positions are offset by the exact startup length;
administrative choices may all be false. Every branch, accepted or rejected,
halts with the verifier's single bit for an exact-length certificate.
**Proof sketch.** Split each full choice word into startup, the actual
scheduler interval, and a completion suffix. Native coverage gives the
unique scheduled certificate length. Startup, guessing, and completion run
contracts compose at their actual configurations. Conversely, choose any
covered guessing word and surround it by arbitrary administrative choices. -/
private lemma b2_host_contract (S M : FinTM Bool) (V : Language Bool)
    (x v : List Bool) (T A d : ℕ)
    (hS : (b2UnaryTM S).ComputesInTime x v T)
    (hlive : ∀ s < T, ((b2UnaryTM S).tm.runFrom
      ((b2UnaryTM S).tm.initCfg x) s).state ≠ none)
    (hM : M.DecidesInTime V (fun n => A * (n + 1) ^ d)) :
    let H := 2 * x.length + 2 + T +
      (x.length + v.length + 2 + (A * (x.length + v.length + 1) ^ d + 1))
    (∀ w : List Bool, w.length = H → ∃ u : List Bool, u.length = v.length ∧
      ((b2Host S M).tm.runWith w ((b2Host S M).tm.initCfg x)).state = none ∧
      ((b2Host S M).tm.runWith w ((b2Host S M).tm.initCfg x)).output =
        [MultiTapeTM.indicator V (x ++ u)]) ∧
    (∀ u : List Bool, u.length = v.length → ∃ w : List Bool, w.length = H ∧
      ((b2Host S M).tm.runWith w ((b2Host S M).tm.initCfg x)).state = none ∧
      ((b2Host S M).tm.runWith w ((b2Host S M).tm.initCfg x)).output =
        [MultiTapeTM.indicator V (x ++ u)]) := by
  let c := (b2UnaryTM S).tm.runFrom ((b2UnaryTM S).tm.initCfg x) T
  have hc : c.state = none := ((computesInTime_iff _ _ _ _).mp hS).1
  let B := x.length + v.length + 2 + (A * (x.length + v.length + 1) ^ d + 1)
  have hcov := b2_guess_coverage S M x v T hS hlive
  have hpieces (a g z u : List Bool) (ha : a.length = 2 * x.length + 2)
      (hu : u.length = v.length) (hz : z.length = B)
      (hg : (b2Host S M).tm.runWith g
        (b2GuessCfg S M ((b2UnaryTM S).tm.initCfg x) []) = b2GuessCfg S M c u) :
      ((b2Host S M).tm.runWith (a ++ g ++ z) ((b2Host S M).tm.initCfg x)).state = none ∧
      ((b2Host S M).tm.runWith (a ++ g ++ z) ((b2Host S M).tm.initCfg x)).output =
        [MultiTapeTM.indicator V (x ++ u)] := by
    rw [NDTM.runWith_append, NDTM.runWith_append, b2_start S M x a ha, hg]
    exact b2_finish S M c hc u (MultiTapeTM.indicator V (x ++ u))
      (A * ((x ++ u).length + 1) ^ d) (hM (x ++ u)) z
      (by simpa only [List.length_append, hu] using hz)
  dsimp only
  constructor
  · intro w hw
    let a := w.take (2 * x.length + 2)
    let rest := w.drop (2 * x.length + 2)
    let g := rest.take T
    let z := rest.drop T
    have ha : a.length = 2 * x.length + 2 := List.length_take_of_le (by omega)
    have hr : rest.length = T + B := by dsimp [rest, B]; rw [List.length_drop, hw]; omega
    have hglen : g.length = T := List.length_take_of_le (by omega)
    have hz : z.length = B := by dsimp [z]; rw [List.length_drop, hr]; omega
    have he : a ++ g ++ z = w := by
      dsimp [a, g, z, rest]
      rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
    obtain ⟨u, hu, hg⟩ := hcov.1 g hglen
    exact ⟨u, hu, he ▸ hpieces a g z u ha hu hz hg⟩
  · intro u hu
    obtain ⟨g, hglen, hg⟩ := hcov.2 u hu
    let a := List.replicate (2 * x.length + 2) false
    let z := List.replicate B false
    refine ⟨a ++ g ++ z, ?_, hpieces a g z u (by simp [a]) hu (by simp [z]) hg⟩
    simp only [List.length_append, List.length_replicate, a, z, hglen, B]

/-- The complete native ledger fits the required polynomial envelope, even
at zero coefficient/degree and empty input. Startup and assembly contribute
`3n+Q(n)+5`; scheduler and verifier contribute their actual proved budgets.
**Proof sketch.** Set the envelope degree to `c+d+1`. Its base dominates
`n+1`, and its degree dominates both `c+1` and `d`, as well as one. Bound the
linear overhead by five times the base, then add all three coefficients. -/
private lemma b2_host_bound (C c B A d n T : ℕ)
    (hT : T ≤ B * (n + 1) ^ (c + 1)) :
    2 * n + 2 + T + (n + C * (n + 1) ^ c + 2 +
      (A * (n + C * (n + 1) ^ c + 1) ^ d + 1)) ≤
      (B + A + 5) * (n + C * (n + 1) ^ c + 1) ^ (c + d + 1) := by
  let m := n + C * (n + 1) ^ c + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hs : T ≤ B * m ^ (c + d + 1) := hT.trans
    (Nat.mul_le_mul_left B ((Nat.pow_le_pow_left (by dsimp [m]; omega) (c + 1)).trans
      (Nat.pow_le_pow_right hm (by omega : c + 1 ≤ c + d + 1))))
  have hv : A * m ^ d ≤ A * m ^ (c + d + 1) :=
    Nat.mul_le_mul_left A (Nat.pow_le_pow_right hm (by omega))
  have hl : 3 * n + C * (n + 1) ^ c + 5 ≤ 5 * m ^ (c + d + 1) := by
    have hp : m ≤ m ^ (c + d + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hm (by omega : 1 ≤ c + d + 1)
    exact (show 3 * n + C * (n + 1) ^ c + 5 ≤ 5 * m by dsimp [m]; omega).trans
      (Nat.mul_le_mul_left 5 hp)
  change 2 * n + 2 + T + (n + C * (n + 1) ^ c + 2 + (A * m ^ d + 1)) ≤ _
  calc
    _ ≤ B * m ^ (c + d + 1) + A * m ^ (c + d + 1) + 5 * m ^ (c + d + 1) := by omega
    _ = _ := by dsimp [m]; ring

/-- The integrated reverse compiler decides the certificate language on all
branches within the required envelope.
**Proof sketch.** Instantiate the unary polynomial scheduler and use its
length-indexed first halt. The host contract gives all-branch termination,
exact-length extraction, and coverage at the complete phase ledger. The
certificate characterization turns its verifier outputs into language
acceptance. Enlarge to the common polynomial envelope using halting
absorption in both directions, including nonaccepting branches. -/
private lemma b2_compile (L : Language Bool) (C c : ℕ) (V : Language Bool)
    (hcert : ∀ x, x ∈ L ↔ ∃ u : List Bool,
      u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V)
    (M : FinTM Bool) (A d : ℕ)
    (hM : M.DecidesInTime V (fun n => A * (n + 1) ^ d)) :
    ∃ (K r : ℕ) (N : FinNDTM Bool),
      N.DecidesInTime L (fun n => K * (n + C * (n + 1) ^ c + 1) ^ r) := by
  classical
  obtain ⟨S, B, hS⟩ := computesFunInTime_polyUnary C c
  obtain ⟨τ, hτ⟩ := b2_unary_first S (fun n => List.replicate (C * (n + 1) ^ c) true)
    (fun n => B * (n + 1) ^ (c + 1)) (fun n => by
      simpa only [List.length_replicate] using hS (List.replicate n true))
  refine ⟨B + A + 5, c + d + 1, b2Host S M, fun x => ?_⟩
  let H := 2 * x.length + 2 + τ x.length + (x.length + C * (x.length + 1) ^ c + 2 +
    (A * (x.length + C * (x.length + 1) ^ c + 1) ^ d + 1))
  have hc := b2_host_contract S M V x (List.replicate (C * (x.length + 1) ^ c) true)
    (τ x.length) A d (hτ x).2.1 (hτ x).2.2 hM
  simp only [List.length_replicate] at hc
  have hhalt : (b2Host S M).tm.HaltsWithin x H := by
    intro w hw
    obtain ⟨u, _, hh, _⟩ := hc.1 w hw
    exact hh
  have hacc : x ∈ L ↔ (b2Host S M).AcceptsWithin x H := by
    rw [hcert x]
    constructor
    · rintro ⟨u, hu, hv⟩
      obtain ⟨w, hw, hh, ho⟩ := hc.2 u hu
      refine ⟨w, hw, hh, ?_⟩
      rw [ho]
      simp [MultiTapeTM.indicator, hv]
    · rintro ⟨w, hw, _, ho⟩
      obtain ⟨u, hu, _, hout⟩ := hc.1 w hw
      refine ⟨u, hu, ?_⟩
      have he := hout.symm.trans ho
      by_contra hv
      simp [MultiTapeTM.indicator, hv] at he
  have ht := b2_host_bound C c B A d x.length (τ x.length) (hτ x).1
  exact ⟨hhalt.mono ht, hacc.trans (acceptsWithin_iff_of_halts hhalt ht).symm⟩

/-- **Guess the certificate** [AB09, Theorem 2.6, ⊇-direction of the union]: `NP` is
contained in the union of the fixed-degree nondeterministic time classes.

**Proof sketch.** Let `L ∈ NP` with parameters `(C, c, V)` and, via
`Complexity.mem_P_iff`, a machine `M_V` deciding `V` within `A·(m+1)^d`. The NDTM, on
input `x` of length `n`: (i) evaluate `Q n = C·(n+1)^c` in binary (the shared
polynomial-evaluation obligation) and initialize a countdown; (ii) **guessing phase**
— write exactly `Q n` guessed bits onto a guess tape, `δ₀` writing `false` and `δ₁`
writing `true` on each nondeterministic write step ([AB09]'s concrete recipe, p. 42),
interleaved with deterministic countdown bookkeeping (the phase boundaries are
identical across branches: only the guessed content diverges, never the timing); (iii) assemble `x ++ u` on an assembly tape (copy the
input, append the guess tape); (iv) run `M_V` **with its input relocated to the
assembly tape** — the input-relocation obligation: the fixed machine `M_V`'s
input-tape reads are served from a work tape through a binary head-position counter
with the window guard, symmetric to the simulation obligation of
`Complexity.ntime_poly_subset_NP`; (v) capture `M_V`'s output in a buffer (isolation,
as always) and emit the verdict: `[true]` if the buffer is exactly `[true]`, else
`[false]`, then halt. Outside the guessing phase the two transition functions
coincide, so every choice word drives the same phases and every branch halts within
the deterministic budget — `HaltsWithin` holds on all inputs. Acceptance: branches of
the guessing phase realize exactly the strings `u` with `|u| = Q n`, and the verdict
is `[true]` precisely when `x ++ u ∈ V` (`M_V` decides `V`), so some branch accepts
iff `x ∈ L`; non-members' branches all emit `[false] ≠ [true]`. Padding accepting
branches to the exact budget is `Turing.FinNDTM.AcceptsWithin.mono`. Total time is
polynomial in `n` — guessing `Q n` steps with `O(log Q n)`-bit countdowns, assembly
`O(n + Q n)`, and the relocated `M_V` run `A·(n + Q n + 1)^d` with polynomial
per-step bookkeeping — hence at most `a'·(n^e + 1)` for a fixed degree `e` (normalize
with `Complexity.succ_pow_le`), landing `L` in the degree-`e` component.

**Continuation checkpoint (E2-cont-B, incomplete).** `contGuessTM` and
`cont_guess_run` provide a native, silent emission-driven guessing phase;
`cont_guess_coverage` proves extraction and coverage at actual physical
write positions. `cont_poly_guess_phase` instantiates the audited unary
polynomial generator on the unary input of length `n`, giving a schedule
determined by `n` and covering zero coefficients. This standalone phase has
a live return state, not a completed decider. Preserving the original input,
installing the scheduler/countdown in a host, assembling `x++u`, and the
captured verifier phase with all-branch totality remain open. The exact
remaining machine-existence goal is exposed below; `cont_guess_normalize`
proves all final exponent/coefficient arithmetic and budget padding once that
machine contract is supplied.

**B2 completion.** The reverse host is now complete. `b2UnaryTM` normalizes
only input reads; `b2_unary_run` and `b2_unary_first` prove exact unary
lockstep and length-only first halts. Startup copies `x` before guessing;
`b2_guess_coverage` lifts the banked phase at its actual completion, and
`b2_host_contract` accounts for the startup offset in full branch words.
Guesses append directly after `x`; `b2_assembly` installs the relocated
verifier with blank tapes, and `b2_verify_timed` captures all output before
emitting one verdict. `b2_tables_coincide` is by construction. `b2_compile`
proves all-branch totality and acceptance at a common envelope with coefficient
`B+A+5` and degree `c+d+1`, then the banked normalization closes the target.
The emission scheduler implements the exact guess count; no upper bound is
used as a native clock and no untimed composition is used. -/
theorem NP_subset_iUnion_NTIME : NP ⊆ ⋃ c : ℕ, NTIME fun n => n ^ c + 1 := by
  rintro L ⟨C, c, V, hV, hcert⟩
  obtain ⟨A, d, M, hM⟩ := mem_P_iff.mp hV
  apply cont_guess_normalize L C c
  exact b2_compile L C c V hcert M A d hM

/-- **Theorem 2.6** [AB09]: `NP = ⋃ c, NTIME (n^c + 1)` — the verifier-certificate
definition and the nondeterministic-machine definition of `NP` coincide (with the
`+ 1` padding of the union recorded in the deviations list).

**Proof sketch.** Antisymmetry: `Complexity.NP_subset_iUnion_NTIME` one way;
`Set.iUnion_subset` with `Complexity.ntime_poly_subset_NP` at every degree the
other. -/
theorem NP_eq_iUnion_NTIME : NP = ⋃ c : ℕ, NTIME fun n => n ^ c + 1 := by
  exact Set.Subset.antisymm NP_subset_iUnion_NTIME
    (Set.iUnion_subset fun c => ntime_poly_subset_NP c)

/-! ### Exponential split and evaluation infrastructure -/

/-- Exponential padding has a unique split, including coefficient zero and
degree zero: the prefix length increases strictly and the suffix length
is nondecreasing. -/
private lemma e3_split_strictMono (C c : ℕ) :
    StrictMono (fun n : ℕ => n + C * 2 ^ (n + 1) ^ c) := by
  intro n m hnm
  exact Nat.add_lt_add_of_lt_of_le hnm (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left (by omega) c)))

/-- Exact exponential widths make both parts of a concatenation unique. -/
private lemma e3_split_unique (C c : ℕ) {x u y v : List Bool}
    (hu : u.length = C * 2 ^ (x.length + 1) ^ c)
    (hv : v.length = C * 2 ^ (y.length + 1) ^ c) (h : x ++ u = y ++ v) :
    x = y ∧ u = v := by
  have hlen := congrArg List.length h
  simp only [List.length_append, hu, hv] at hlen
  have hx := (e3_split_strictMono C c).injective hlen
  exact ⟨List.append_inj_left h hx, List.append_inj_right h hx⟩

/-- The finite exponential-length search, with an explicit failure value. -/
private def e3Split (C c m : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? (fun n => decide (n + C * 2 ^ (n + 1) ^ c = m))

/-- A successful search certifies its exact length equation and input bound. -/
private lemma e3_split_spec (C c m n : ℕ) (h : e3Split C c m = some n) :
    n ≤ m ∧ n + C * 2 ^ (n + 1) ^ c = m := by
  have hn := List.mem_of_find?_eq_some h
  have he := List.find?_some h
  exact ⟨Nat.le_of_lt_succ (List.mem_range.mp hn), of_decide_eq_true he⟩

/-- Exhaustion excludes every natural split, not only a chosen default. -/
private lemma e3_split_none_iff (C c m : ℕ) :
    e3Split C c m = none ↔ ¬∃ n, n + C * 2 ^ (n + 1) ^ c = m := by
  rw [e3Split, List.find?_eq_none]
  constructor
  · intro h hex
    obtain ⟨n, hn⟩ := hex
    exact h n (List.mem_range.mpr (by omega)) (by simpa using hn)
  · intro h n _ hn
    exact h ⟨n, of_decide_eq_true hn⟩

/-- Every valid exponential split is recovered by the finite search. -/
private lemma e3_split_complete (C c m n : ℕ)
    (hn : n + C * 2 ^ (n + 1) ^ c = m) : e3Split C c m = some n := by
  cases hs : e3Split C c m with
  | none => exact False.elim ((e3_split_none_iff C c m).mp hs ⟨n, hn⟩)
  | some k =>
    have hk := (e3_split_spec C c m k hs).2
    exact congrArg some ((e3_split_strictMono C c).injective (hk.trans hn.symm))

/-- A positive exponential coefficient rejects the empty verifier input. -/
private lemma e3_split_empty (C c : ℕ) (hC : 0 < C) : e3Split C c 0 = none := by
  apply (e3_split_none_iff C c 0).mpr
  rintro ⟨n, hn⟩
  have hp : 0 < C * 2 ^ (n + 1) ^ c := Nat.mul_pos hC (Nat.pow_pos (by omega))
  omega

/-- The choice-word verifier with the exact exponential certificate width. -/
private def e3ChoiceVerifier (N : FinNDTM Bool) (C c : ℕ) : Language Bool :=
  {y | ∃ x u : List Bool, u.length = C * 2 ^ (x.length + 1) ^ c ∧ y = x ++ u ∧
    (N.tm.runWith u (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith u (N.tm.initCfg x)).output = [true]}

/-- On a valid concatenation, membership tests exactly its own choice word. -/
private lemma e3_choice_append (N : FinNDTM Bool) (C c : ℕ)
    (x u : List Bool) (hu : u.length = C * 2 ^ (x.length + 1) ^ c) :
    x ++ u ∈ e3ChoiceVerifier N C c ↔
      (N.tm.runWith u (N.tm.initCfg x)).state = none ∧
      (N.tm.runWith u (N.tm.initCfg x)).output = [true] := by
  constructor
  · rintro ⟨y, v, hv, heq, hhalt, hout⟩
    obtain ⟨rfl, rfl⟩ := e3_split_unique C c hu hv heq
    exact ⟨hhalt, hout⟩
  · rintro ⟨hhalt, hout⟩
    exact ⟨x, u, hu, rfl, hhalt, hout⟩

/-- Failed exponential split search requires rejection. -/
private lemma e3_choice_no_split (N : FinNDTM Bool) (C c : ℕ) (y : List Bool)
    (h : e3Split C c y.length = none) : y ∉ e3ChoiceVerifier N C c := by
  rintro ⟨x, u, hu, hy, _, _⟩
  have hlen := congrArg List.length hy
  simp only [List.length_append, hu] at hlen
  exact (e3_split_none_iff C c y.length).mp h ⟨x.length, hlen.symm⟩

/-- The exact padded certificate covers the source time budget at every length. -/
private lemma e3_choice_budget (a c n : ℕ) :
    a * 2 ^ n ^ c ≤ a * 2 ^ (n + 1) ^ c := by
  exact Nat.mul_le_mul_left a
    (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left (Nat.le_succ n) c))

/-- All-branch halting justifies both padding and truncation of choice words;
the certificate length itself remains exactly the prescribed exponential. -/
private lemma e3_choice_certificate (N : FinNDTM Bool) (L : Language Bool)
    (a c : ℕ) (hN : N.DecidesInTime L (fun n => a * 2 ^ n ^ c)) (x : List Bool) :
    x ∈ L ↔ ∃ u : List Bool, u.length = a * 2 ^ (x.length + 1) ^ c ∧
      x ++ u ∈ e3ChoiceVerifier N a c := by
  rw [(hN x).2, ← acceptsWithin_iff_of_halts (hN x).1 (e3_choice_budget a c x.length)]
  constructor
  · rintro ⟨u, hu, hhalt, hout⟩
    exact ⟨u, hu, (e3_choice_append N a c x u hu).mpr ⟨hhalt, hout⟩⟩
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, hu, (e3_choice_append N a c x u hu).mp hv⟩

/-- A decider cannot have zero time coefficient: its initial state on the
empty input is live even on the unique empty choice word. -/
private lemma e3_coefficient_pos (N : FinNDTM Bool) (L : Language Bool)
    (a c : ℕ) (hN : N.DecidesInTime L (fun n => a * 2 ^ n ^ c)) : 0 < a := by
  by_contra ha
  have hz : a = 0 := by omega
  have hh := (hN []).1 [] (by simp [hz])
  simp [NDTM.runWith, NDTM.initCfg, Cfg.init] at hh

/-- Multiplication by a power of two prefixes zeroes to a nonzero binary word.
This is an exact binary representation, not an exponential unary emission. -/
private lemma e3_bits_shift (C p : ℕ) (hC : C ≠ 0) :
    Nat.bits (C * 2 ^ p) = List.replicate p false ++ Nat.bits C := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hp : C * 2 ^ p ≠ 0 := Nat.mul_ne_zero hC (Nat.ne_of_gt (Nat.pow_pos (by omega)))
    rw [show C * 2 ^ (p + 1) = 2 * (C * 2 ^ p) by ring, Nat.bit0_bits _ hp, ih]
    simp [List.replicate_succ]

/-- Before any padding validation, binary evaluation has polynomial output
length in the enclosing input length, because the candidate prefix is bounded. -/
private lemma e3_bits_length_bound (C c n m : ℕ) (hn : n ≤ m) :
    (Nat.bits (C * 2 ^ (n + 1) ^ c)).length ≤ (m + 1) ^ c + (Nat.bits C).length := by
  by_cases hC : C = 0
  · simp [hC]
  · rw [e3_bits_shift C _ hC, List.length_append, List.length_replicate]
    exact Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) c) _

/-- Replace each input symbol by a zero bit, then append a fixed binary word.
The scanner and fixed emission chain use no work tapes. -/
private def e3ShiftTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Unit ⊕ Fin (w.length + 1)
  tm := {
    q₀ := .inl ()
    tr := fun q inp _ => match q with
      | .inl _ => match inp with
        | some _ => ⟨.pos, fun i => i.elim0, some false, some (.inl ())⟩
        | none => controlAction 0 (some (.inr 0))
      | .inr i => emitAction w Sum.inr i }

/-- The shift scanner advances one input position and emits one zero per
step, retaining its live scanner state until the boundary blank. -/
private lemma e3_shift_scan (w x : List Bool) : ∀ t, t ≤ x.length →
    ((e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) t).state = some (.inl ()) ∧
    (((e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) t).inputPos : ℕ) = t + 1 ∧
    ((e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) t).output =
      List.replicate t false := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hs, hp, ho⟩ := ih (by omega)
    have hstep : (e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) (t + 1) =
        ((e3ShiftTM w).tm.tr (.inl ()) (some (x[t]'(by omega)))
          (((e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) t).workTapeSymbols)).apply
          ((e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hstep]
      simp [e3ShiftTM, Action.apply]
    · rw [hstep]
      simp only [e3ShiftTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show (((e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hstep]
      simp only [e3ShiftTM, Action.apply, ho]
      exact List.replicate_succ'.symm

/-- The scanner's blank transition enters the emission chain; the final
halting transition is charged explicitly. The total is `|x|+|w|+2`. -/
private lemma e3_shift_computes (w x : List Bool) :
    (e3ShiftTM w).ComputesInTime x (List.replicate x.length false ++ w)
      (x.length + w.length + 2) := by
  obtain ⟨hs, hp, ho⟩ := e3_shift_scan w x x.length (le_refl _)
  let cfg := (e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) x.length
  have hp' : (cfg.inputPos : ℕ) = x.length + 1 := hp
  have hzero : cfg.inputPos ≠ 0 := by
    intro h
    rw [h] at hp'
    simp at hp'
  have hinp : cfg.inputSymbol = none := by
    unfold Cfg.inputSymbol
    rw [dif_neg hzero, dif_pos (by omega)]
  have henter : (e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) (x.length + 1) =
      (controlAction 0 (some (.inr (0 : Fin (w.length + 1))))).apply cfg := by
    rw [MultiTapeTM.runFrom_succ_eq_step']
    change (e3ShiftTM w).tm.step cfg = _
    simp only [MultiTapeTM.step, show cfg.state = some (.inl ()) from hs, e3ShiftTM, hinp]
  let next := (e3ShiftTM w).tm.runFrom ((e3ShiftTM w).tm.initCfg x) (x.length + 1)
  have hnext : next.state = some (.inr (0 : Fin (w.length + 1))) := by
    dsimp only [next]
    rw [henter]
    rfl
  have houtput : next.output = List.replicate x.length false := by
    dsimp only [next]
    rw [henter]
    simp only [controlAction, Action.apply, Option.toList_none, List.append_nil]
    exact ho
  obtain ⟨hh, hout⟩ := emit_halts (e3ShiftTM w).tm w Sum.inr
    (fun _ _ _ => rfl) next hnext
  apply (computesInTime_iff _ _ _ _).mpr
  rw [show x.length + w.length + 2 = (x.length + 1) + (w.length + 1) by omega,
    MultiTapeTM.runFrom_add]
  exact ⟨hh, by simpa only [houtput] using hout⟩

/-- The fixed-word binary shift has a monotone linear budget on all inputs. -/
private lemma e3_shift_timed (w : List Bool) :
    (e3ShiftTM w).ComputesFunInTime (fun x => List.replicate x.length false ++ w)
      (fun n => (w.length + 2) * (n + 1)) := by
  intro x
  apply (e3_shift_computes w x).mono
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- The exact binary value of exponential padding is polynomial-time
computable before any validity check.
**Proof sketch.** At coefficient zero emit the empty binary word. Otherwise
the catalog emits `(n+1)^c` unary symbols. The native shift scanner emits
that many zeroes followed by the fixed nonzero coefficient's bits. Timed
buffered composition and the binary shift identity identify the value;
the monotone linear second-stage cost yields degree `c+1` uniformly. -/
private lemma e3_exp_bits_timed (C c : ℕ) :
    ∃ (M : FinTM Bool) (A : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * 2 ^ (x.length + 1) ^ c))
        (fun n => A * (n + 1) ^ (c + 1)) := by
  by_cases hC : C = 0
  · obtain ⟨M, A, hM⟩ := computesFunInTime_const ([] : List Bool)
    refine ⟨M, A, fun x => ?_⟩
    simpa only [hC, Nat.zero_mul, Nat.zero_bits] using (hM x).mono
      (Nat.mul_le_mul_left A (by
        simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
          (show 1 ≤ c + 1 by omega)))
  · obtain ⟨U, a, hU⟩ := computesFunInTime_polyUnary 1 c
    obtain ⟨M, b, hM⟩ := computesFunInTime_comp hU (e3_shift_timed (Nat.bits C))
      (by intro m n h; exact Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))
    let k := (Nat.bits C).length + 2
    refine ⟨M, b * (a + 1) * (k + 1), fun x => ?_⟩
    have hc := hM x
    simp only [Function.comp_apply, List.length_replicate, Nat.one_mul,
      ← e3_bits_shift C _ hC] at hc
    apply hc.mono
    let p := (x.length + 1) ^ (c + 1)
    have hp : 1 ≤ p := Nat.one_le_pow _ _ (Nat.succ_pos _)
    change b * (a * p + k * (a * p + 1) + 1) ≤ b * (a + 1) * (k + 1) * p
    calc
      _ = b * (a * (k + 1) * p + (k + 1)) := by ring
      _ ≤ b * (a * (k + 1) * p + (k + 1) * p) :=
        Nat.mul_le_mul_left b (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hp) _)
      _ = _ := by ring

/-- The exponential search returns a threaded pair, or an empty rejection word. -/
private def e3SplitWord (C c : ℕ) (y : List Bool) : List Bool :=
  match e3Split C c y.length with
  | some i => pairEncode (y.take i) (y.drop i)
  | none => []

/-- The emitted split has a linear length bound, including malformed inputs. -/
private lemma e3_split_length (C c : ℕ) (y : List Bool) :
    (e3SplitWord C c y).length ≤ 2 * y.length + 2 := by
  cases hs : e3Split C c y.length with
  | none => simp [e3SplitWord, hs]
  | some i =>
    have hi := (e3_split_spec C c y.length i hs).1
    simp [e3SplitWord, hs, pairEncode]
    omega

/-- The existing paired loader and captured choice simulator handle every
exponential search result in linear time, including explicit failure.
**Proof sketch.** Failure excludes verifier membership and the empty-word
loader rejects. Success certifies the exact dropped length, so split
uniqueness identifies the native simulation verdict with membership. The
linear emitted-length bound supplies one common loader budget. -/
private lemma e3_split_answer (N : FinNDTM Bool) (C c : ℕ) (y : List Bool) :
    (contPairTM N).ComputesInTime (e3SplitWord C c y)
      [MultiTapeTM.indicator (e3ChoiceVerifier N C c) y] (3 * (2 * y.length + 3)) := by
  classical
  cases hs : e3Split C c y.length with
  | none =>
    have hn := e3_choice_no_split N C c y hs
    simpa only [e3SplitWord, hs, MultiTapeTM.indicator, if_neg hn] using
      (cont_pair_empty N).mono (by omega : 1 ≤ 3 * (2 * y.length + 3))
  | some i =>
    obtain ⟨hi, he⟩ := e3_split_spec C c y.length i hs
    have hu : (y.drop i).length = C * 2 ^ ((y.take i).length + 1) ^ c := by
      rw [List.length_drop, List.length_take_of_le hi]
      omega
    have hv := e3_choice_append N C c (y.take i) (y.drop i) hu
    rw [List.take_append_drop] at hv
    have hout : MultiTapeTM.indicator (e3ChoiceVerifier N C c) y =
        decide ((N.tm.runWith (y.drop i) (N.tm.initCfg (y.take i))).state = none ∧
          (N.tm.runWith (y.drop i) (N.tm.initCfg (y.take i))).output = [true]) := by
      simp only [MultiTapeTM.indicator, hv]
      split <;> simp_all
    rw [e3SplitWord, hs, hout]
    apply (cont_pair_computes N (y.take i) (y.drop i)).mono
    have hl := e3_split_length C c y
    simp only [e3SplitWord, hs] at hl
    omega

/-- A polynomial-time exponential split emitter suffices for the complete
blank-tape choice verifier; all subsequent machine phases are already proved.
**Proof sketch.** Timed buffered composition runs split recovery and then the
unchanged paired loader/simulator. Charge the actual intermediate length,
never a substituted arbitrary time function. The loader and rewind overhead
fit thirteen copies of the positive polynomial envelope. -/
private lemma e3_verifier_of_split (N : FinNDTM Bool) (C c : ℕ)
    (M : FinTM Bool) (A r : ℕ)
    (hM : M.ComputesFunInTime (e3SplitWord C c)
      (fun n => A * (n + 1) ^ (r + 1))) : e3ChoiceVerifier N C c ∈ P := by
  refine mem_P_iff.mpr ⟨A + 13, r + 1, bufferedCompTM M (contPairTM N), ?_⟩
  intro y
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start M (contPairTM N) y (e3SplitWord C c y) _ (hM y)
  dsimp only at ha
  obtain ⟨tag, _, hr⟩ := bufferedSecondCfg_run M (contPairTM N)
    ((contPairTM N).tm.initCfg (e3SplitWord C c y)) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads
    (3 * (2 * y.length + 3))
  have hc := (computesInTime_iff _ _ _ _).mp (e3_split_answer N C c y)
  have hbase : (bufferedCompTM M (contPairTM N)).ComputesInTime y
      [MultiTapeTM.indicator (e3ChoiceVerifier N C c) y] (a + 3 * (2 * y.length + 3)) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  apply hbase.mono
  have hl := e3_split_length C c y
  have hp : y.length + 1 ≤ (y.length + 1) ^ (r + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos y.length)
      (show 1 ≤ r + 1 by omega)
  calc
    a + 3 * (2 * y.length + 3) ≤
        A * (y.length + 1) ^ (r + 1) + 13 * (y.length + 1) := by omega
    _ ≤ A * (y.length + 1) ^ (r + 1) + 13 * (y.length + 1) ^ (r + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 13 hp) _
    _ = (A + 13) * (y.length + 1) ^ (r + 1) := by ring

/-- The bounded search advances unary candidate length and stalls just past
the input, so its invariant is closed on every possible round state. -/
private def e3SplitStep (w s : List Bool) : List Bool :=
  if s.length ≤ w.length then s ++ [true] else s

/-- The search round tests the exact exponential length equation. -/
private def e3SplitAccept (C c : ℕ) (w s : List Bool) : Bool :=
  decide (s.length + C * 2 ^ (s.length + 1) ^ c = w.length)

/-- Search-state length is preserved by the one-past-end stall. -/
private lemma e3_step_inv (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    (e3SplitStep w s).length ≤ w.length + 1 := by
  unfold e3SplitStep
  split <;> simp_all

/-- The tested orbit consists exactly of the unary candidate indices. -/
private lemma e3_step_orbit (w : List Bool) : ∀ i, i ≤ w.length + 1 →
    (e3SplitStep w)^[i] [] = List.replicate i true := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [e3SplitStep, List.length_replicate, if_pos (by omega : i ≤ w.length)]
    exact List.replicate_succ'.symm

/-- Predicate equality on a finite list preserves the least-success result. -/
private lemma e3_find_congr {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a ∈ xs, p a = q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

/-- The loop's bounded orbit search is the specified exponential split search. -/
private lemma e3_find_eq (C c : ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => e3SplitAccept C c w ((e3SplitStep w)^[i] [])) = e3Split C c w.length := by
  apply e3_find_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [e3_step_orbit w i (by omega)]
  simp only [e3SplitAccept, List.length_replicate]

/-- Both successful payloads and exhaustion agree with the split emitter. -/
private lemma e3_loop_result (C c : ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => e3SplitAccept C c w ((e3SplitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((e3SplitStep w)^[i] []).length)
          (w.drop ((e3SplitStep w)^[i] []).length)
      | none => []) = e3SplitWord C c w := by
  rw [e3_find_eq]
  cases hs : e3Split C c w.length with
  | none => simp [e3SplitWord, hs]
  | some i =>
    have hi := (e3_split_spec C c w.length i hs).1
    simp only [e3SplitWord, hs, e3_step_orbit w i (by omega), List.length_replicate]

/-- The result-bearing loop increases the round exponent by one. -/
private lemma e3_loop_bound (b A r n : ℕ) :
    b * (A * (n + 1) ^ (r + 1) + 1) * (n + 2) ≤
      (2 * b * (A + 1)) * (n + 1) ^ (r + 2) := by
  have hp : 1 ≤ (n + 1) ^ (r + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hfirst : A * (n + 1) ^ (r + 1) + 1 ≤ (A + 1) * (n + 1) ^ (r + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ b * ((A + 1) * (n + 1) ^ (r + 1)) * (2 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left b hfirst) (by omega)
    _ = _ := by rw [show r + 2 = (r + 1) + 1 by omega, Nat.pow_succ]; ring

/-- Concrete startup and scratch-restoring round contracts suffice for
polynomial-time exponential split recovery through the audited loop engine.
**Proof sketch.** Use the binary input-length machine as fuel, enlarge the
common round coefficient to cover fuel generation, and invoke the public
result-bearing loop. The proved unary orbit identifies the least valid
split and the payload, with the empty output on exhaustion. The loop bound
raises the round exponent by one. No body contract is inferred from a
function-level evaluator or from an untimed computation. -/
private lemma e3_split_of_body (C c : ℕ) (body : FinTM Bool) (anchor : body.State)
    (A r : ℕ)
    (hstart : ∀ w : List Bool, ∃ t ≤ A * (w.length + 1) ^ (r + 1),
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg w) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg w) t = Cfg.ofWords anchor (stateWord body.k []))
    (hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ A * (w.length + 1) ^ (r + 1) ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if e3SplitAccept C c w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (e3SplitStep w s))) :
    ∃ (M : FinTM Bool) (B : ℕ),
      M.ComputesFunInTime (e3SplitWord C c) (fun n => B * (n + 1) ^ (r + 2)) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_lengthBits
  have hn (n : ℕ) : n + 1 ≤ (n + 1) ^ (r + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ r + 1 by omega)
  have hbody (n : ℕ) : A * (n + 1) ^ (r + 1) ≤ (A + a) * (n + 1) ^ (r + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hF' : F.ComputesFunInTime (fun w => Nat.bits w.length)
      (fun n => (A + a) * (n + 1) ^ (r + 1)) := by
    intro w
    apply (hF w).mono
    exact (Nat.mul_le_mul_left a (hn w.length)).trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨M, b, hM⟩ := exists_loopFindTM body F anchor
    (fun w s => s.length ≤ w.length + 1) e3SplitStep (e3SplitAccept C c)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (n + 1) ^ (r + 1)) hF'
    (by intro w; simp) e3_step_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, htpos, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * b * (A + a + 1), fun w => ?_⟩
  have hm := hM w
  dsimp only [id_eq] at hm
  convert hm.mono (e3_loop_bound b (A + a) r w.length) using 1
  exact (e3_loop_result C c w).symm

/-- At degree zero the exponential split is the existing constant-width
catalog split, with coefficient exactly `2*C`. -/
private lemma e3_split_degree_zero (C : ℕ) :
    ∃ (M : FinTM Bool) (A : ℕ),
      M.ComputesFunInTime (e3SplitWord C 0) (fun n => A * (n + 1) ^ 2) := by
  obtain ⟨M, A, hM⟩ := computesFunInTime_splitSolve (C * 2) 0
  refine ⟨M, A, fun w => ?_⟩
  have he : e3Split C 0 w.length = solveSplit (C * 2) 0 w.length := by
    apply e3_find_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp [beq_iff_eq]
  simpa only [e3SplitWord, he] using hM w

/-- Coefficient zero also has the existing constant-width split, irrespective
of the degree. The sole suffix is empty. -/
private lemma e3_split_coefficient_zero (c : ℕ) :
    ∃ (M : FinTM Bool) (A : ℕ),
      M.ComputesFunInTime (e3SplitWord 0 c) (fun n => A * (n + 1) ^ 2) := by
  obtain ⟨M, A, hM⟩ := computesFunInTime_splitSolve 0 0
  refine ⟨M, A, fun w => ?_⟩
  have he : e3Split 0 c w.length = solveSplit 0 0 w.length := by
    apply e3_find_congr
    intro i _
    apply Bool.eq_iff_iff.mpr
    simp [beq_iff_eq]
  simpa only [e3SplitWord, he] using hM w

/-- A zero-tape placeholder supplies only the empty inactive bank of the
virtual-input wrapper. Its own transition is never entered by this phase. -/
private def e3cIdleTM : FinTM Bool where
  k := 0
  State := Unit
  tm := ⟨(), fun _ _ _ => controlAction 0 none⟩

/-- The candidate evaluator is the guarded virtual-input phase of the proved
buffered simulator, wrapped by the capture transformer. Its completed state
is a live return state; no evaluated bit reaches the physical output. -/
private def e3cEvalTM (M : FinTM Bool) : FinTM Bool where
  k := (bufferedCompTM e3cIdleTM M).k + 1
  State := (bufferedCompTM e3cIdleTM M).State ⊕ Unit
  tm := {
    q₀ := .inl (bufferedCompTM e3cIdleTM M).tm.q₀
    tr := fun q inp work => match q with
      | .inl q => captureAction Sum.inl (.inr ())
          ((bufferedCompTM e3cIdleTM M).tm.tr q inp (fun i => work i.castSucc))
      | .inr () => controlAction 0 (some (.inr ())) }

/-- Exact evaluator configuration: the preserved candidate occupies tape zero,
the source work bank follows it, and the final tape captures every source
emission, including the halting emission. The original input head is fixed. -/
private def e3cEvalCfg (M : FinTM Bool) {w s : List Bool}
    (c : Cfg M.k Bool M.State s) (b : Bool) (p : Fin (w.length + 2)) :
    Cfg (e3cEvalTM M).k Bool (e3cEvalTM M).State w :=
  captureCfg Sum.inl (.inr ()) [] []
    (bufferedSecondCfg e3cIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0))

/-- Guarded virtual simulation and capture commute through every live source
prefix. The completed configuration, rather than a time bound, selects return.
**Proof sketch.** The public virtual-input theorem supplies a valid arrival
tag and the exact source configuration at each time. Its live prefixes meet
the capture theorem's guard, so the latter captures exactly that same run. -/
private lemma e3c_eval_run (M : FinTM Bool) {w s : List Bool}
    (c : Cfg M.k Bool M.State s) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (w.length + 2)) (t : ℕ)
    (hlive : ∀ j < t, (M.tm.runFrom c j).state ≠ none) :
    ∃ b', VirtualTag (M.tm.runFrom c t).inputPos b' ∧
      (e3cEvalTM M).tm.runFrom (e3cEvalCfg M c b p) t =
        e3cEvalCfg M (M.tm.runFrom c t) b' p := by
  have hvirtual (j : ℕ) := bufferedSecondCfg_run e3cIdleTM M c b hb p
    (fun i => i.elim0) (fun i => i.elim0) j
  have hguard : ∀ j < t, ¬((bufferedCompTM e3cIdleTM M).tm.runFrom
      (bufferedSecondCfg e3cIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0)) j).Halted := by
    intro j hj
    obtain ⟨tag, _, he⟩ := hvirtual j
    rw [he]
    simpa only [Cfg.Halted, bufferedSecondCfg, Option.map_eq_none_iff] using hlive j hj
  have hcap := capture_run (bufferedCompTM e3cIdleTM M).tm (e3cEvalTM M).tm
    Sum.inl (.inr ()) (fun _ _ _ => rfl) [] []
    (bufferedSecondCfg e3cIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0)) t hguard
  obtain ⟨tag, htag, he⟩ := hvirtual t
  rw [he] at hcap
  exact ⟨tag, htag, hcap⟩

/-- A prepared candidate with blank source work and an empty capture tape is
exactly the library state-word seam at the evaluator's initial virtual state.
**Proof sketch.** Compare all configuration fields. Split a tape index into the candidate,
source bank, and capture slot; all work heads start at zero. -/
private lemma e3c_eval_initial (M : FinTM Bool) (w s : List Bool) :
    e3cEvalCfg (w := w) M (M.tm.initCfg s) true 1 =
      Cfg.ofWords (.inl (.inr (.inr (M.tm.q₀, true))))
        (stateWord (e3cEvalTM M).k s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    change (if h : i.val < 0 + (1 + M.k) then
      tapeBlocks (fun j : Fin 0 => j.elim0) (bufferTape s)
        (fun _ : Fin M.k => fun _ => none) ⟨i.val, h⟩
      else bufferTape []) = bufferTape (if i.val = 0 then s else [])
    by_cases hi : i.val < 0 + (1 + M.k)
    · rw [dif_pos hi]
      by_cases hz : i.val = 0
      · simp [tapeBlocks, Fin.addCases, hz]
      · have h1 : ¬ i.val < 1 := by omega
        simp [tapeBlocks, Fin.addCases, hz, h1]
    · rw [dif_neg hi]
      have hz : i.val ≠ 0 := by omega
      simp [hz]
  · funext i
    dsimp only [e3cEvalCfg, captureCfg, bufferedSecondCfg,
      MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords]
    simp only [Fin.val_one, Nat.cast_one, sub_self, List.nil_append, List.length_nil, Nat.cast_zero]
    split
    · simp [tapeBlocks, Fin.addCases, e3cIdleTM]
    · rfl

/-- A timed evaluator reaches the actual first source halt, with no earlier
visit to the live return state and with the exact complete capture buffer.
**Proof sketch.** Take the least halting time justified by totality. Absorption
identifies the output there with the specified output at the deadline. Apply
captured virtual lockstep through that time and through every earlier prefix.
The deadline is used only for the inequality, never as a native clock. -/
private lemma e3c_eval_first (M : FinTM Bool) (w s out : List Bool) (T : ℕ)
    (hM : M.ComputesInTime s out T) :
    ∃ t ≤ T, ∃ b,
      VirtualTag (M.tm.runFrom (M.tm.initCfg s) t).inputPos b ∧
      (M.tm.runFrom (M.tm.initCfg s) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg s) t).output = out ∧
      (∀ j < t, ((e3cEvalTM M).tm.runFrom
        (e3cEvalCfg (w := w) M (M.tm.initCfg s) true 1) j).state ≠ some (.inr ())) ∧
      (e3cEvalTM M).tm.runFrom
        (e3cEvalCfg (w := w) M (M.tm.initCfg s) true 1) t =
          e3cEvalCfg (w := w) M (M.tm.runFrom (M.tm.initCfg s) t) b 1 := by
  classical
  have hspec := (computesInTime_iff M s out T).mp hM
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg s) t).state = none := ⟨T, hspec.1⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hspec.1
  have hh : (M.tm.runFrom (M.tm.initCfg s) t).state = none := Nat.find_spec hex
  have hlive : ∀ j < t, (M.tm.runFrom (M.tm.initCfg s) j).state ≠ none :=
    fun j hj => Nat.find_min hex hj
  have hout : (M.tm.runFrom (M.tm.initCfg s) t).output = out :=
    ((computesInTime_iff M s _ t).mpr ⟨hh, rfl⟩).output_unique hM
  have htag : VirtualTag (M.tm.initCfg s).inputPos true := by
    simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]
  obtain ⟨b, hb, hr⟩ := e3c_eval_run M (M.tm.initCfg s) true htag
    (1 : Fin (w.length + 2)) t hlive
  refine ⟨t, ht, b, hb, hh, hout, ?_, hr⟩
  intro j hj
  obtain ⟨b', _, hr'⟩ := e3c_eval_run M (M.tm.initCfg s) true htag
    (1 : Fin (w.length + 2)) j (fun l hl => hlive l (by omega))
  rw [hr']
  cases hs : (M.tm.runFrom (M.tm.initCfg s) j).state with
  | none => exact False.elim (hlive j hj hs)
  | some q =>
    dsimp only [e3cEvalCfg, captureCfg, bufferedSecondCfg]
    rw [hs]
    simp

/-- The candidate's one-past-end allowance costs the explicit factor `2^r`.
This is a pre-validation bound: no accepted-padding equation is assumed. -/
private lemma e3c_candidate_envelope (B r : ℕ) (w s : List Bool)
    (hs : s.length ≤ w.length + 1) :
    B * (s.length + 1) ^ r ≤ (B * 2 ^ r) * (w.length + 1) ^ r := by
  calc
    B * (s.length + 1) ^ r ≤ B * (2 * (w.length + 1)) ^ r :=
      Nat.mul_le_mul_left B (Nat.pow_le_pow_left (by omega) r)
    _ = _ := by rw [Nat.mul_pow]; ring

/-- Equality of one-longer prefixes checks the entire old prefix and the next
optional bit. In particular, a missing bit differs from a present false bit. -/
private lemma e3c_take_succ_eq (u v : List Bool) (j : ℕ) :
    u.take (j + 1) = v.take (j + 1) ↔
      u.take j = v.take j ∧ u[j]? = v[j]? := by
  constructor
  · intro h
    constructor
    · have hh := congrArg (List.take j) h
      simpa only [List.take_take, Nat.min_eq_left (by omega : j ≤ j + 1)] using hh
    · have hh := congrArg (fun xs : List Bool => xs[j]?) h
      simpa only [List.getElem?_take, Nat.lt_succ_self, ↓reduceIte] using hh
  · rintro ⟨hpre, hbit⟩
    rw [List.take_succ, List.take_succ, hpre, hbit]

/-- Two read-only word tapes are compared through their common right blank,
then both heads are restored to zero. The returned Boolean is stored in finite
control; the phase never emits. Empty words use the same positive-time path. -/
private def e3cCompareTM : FinTM Bool where
  k := 2
  State := Fin 3 × Bool
  tm := {
    q₀ := (0, true)
    tr := fun q _ work => match q.1.val with
      | 0 =>
        if work 0 = none ∧ work 1 = none then
          ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
        else
          ⟨0, fun _ => (none, .pos), none,
            some (0, q.2 && decide (work 0 = work 1))⟩
      | 1 =>
        if work 0 = none ∧ work 1 = none then
          ⟨0, fun _ => (none, .pos), none, some (2, q.2)⟩
        else ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
      | _ => controlAction 0 (some (2, q.2)) }

/-- Both comparison heads are aligned; the physical input and its head are
untouched, both word tapes are preserved, and the physical output is empty. -/
private def e3cCompareCfg (w u v : List Bool) (p : Fin (w.length + 2))
    (q : Fin 3) (b : Bool) (h : ℤ) : Cfg 2 Bool e3cCompareTM.State w :=
  ⟨some (q, b), p, (fun i => if i.val = 0 then bufferTape u else bufferTape v), fun _ => h, []⟩

/-- The comparator cannot mistake an interior aligned position for the common
right blank: at least one of the two complete words still has a bit there. -/
private lemma e3c_compare_nonblank (u v : List Bool) (j : ℕ)
    (hj : j < max u.length v.length) : ¬(u[j]? = none ∧ v[j]? = none) := by
  intro h
  have hu := List.getElem?_eq_none_iff.mp h.1
  have hv := List.getElem?_eq_none_iff.mp h.2
  have : max u.length v.length ≤ j := max_le hu hv
  omega

/-- After `j` forward comparisons the register records equality of the whole
length-`j` prefixes, including any unequal-length mismatch.
**Proof sketch.** Induct on the consumed prefix length. Reading both optional bits extends
prefix equality by one and advances both heads together. -/
private lemma e3c_compare_scan (w u v : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ max u.length v.length →
      e3cCompareTM.tm.runFrom (e3cCompareCfg w u v p 0 true 0) j =
        e3cCompareCfg w u v p 0 (decide (u.take j = v.take j)) j := by
  intro j
  induction j with
  | zero => intro _; simp [e3cCompareCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread : ¬(u[j]? = none ∧ v[j]? = none) :=
      e3c_compare_nonblank u v j (by omega)
    have heq : (decide (u.take j = v.take j) && decide (u[j]? = v[j]?)) =
        decide (u.take (j + 1) = v.take (j + 1)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact (e3c_take_succ_eq u v j).symm
    simp only [MultiTapeTM.step, e3cCompareCfg, e3cCompareTM,
      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
      if_neg hread]
    refine Cfg.ext ?_ (moveInputPos_zero _) rfl ?_ rfl
    · exact congrArg (fun b => some (0, b)) heq
    · funext i; simp [Action.apply]

/-- The common rewind passes all remaining aligned word cells and their left
blank, preserving the comparison register and restoring both heads exactly.
**Proof sketch.** Induct on the aligned distance to the left blank. At least one word
still occupies each interior position; the final positive move restores zero. -/
private lemma e3c_compare_rewind (w u v : List Bool) (p : Fin (w.length + 2))
    (b : Bool) : ∀ j, j ≤ max u.length v.length →
      e3cCompareTM.tm.runFrom (e3cCompareCfg w u v p 1 b ((j : ℤ) - 1)) (j + 1) =
        e3cCompareCfg w u v p 2 b 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub, MultiTapeTM.step,
      e3cCompareCfg, e3cCompareTM, Cfg.workTapeSymbols,
      Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_left, and_self, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hread := e3c_compare_nonblank u v j (by omega : j < max u.length v.length)
    have hs : e3cCompareTM.tm.step
        (e3cCompareCfg w u v p 1 b (((j + 1 : ℕ) : ℤ) - 1)) =
          e3cCompareCfg w u v p 1 b ((j : ℤ) - 1) := by
      have hpos : (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) := by omega
      rw [hpos]
      simp only [MultiTapeTM.step, e3cCompareCfg, e3cCompareTM,
        Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
        if_neg hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Whole-word comparison returns silently in exactly twice the longer word's
length plus two steps, with both tapes and the physical input head unchanged.
**Proof sketch.** The forward invariant compares full prefixes, so at the
longer length its register is literal word equality. The common-right-blank
transition enters the rewind; the rewind restores both heads at the origin. -/
private lemma e3c_compare_run (w u v : List Bool) (p : Fin (w.length + 2)) :
    e3cCompareTM.tm.runFrom (e3cCompareCfg w u v p 0 true 0)
      (2 * (max u.length v.length + 1)) =
        e3cCompareCfg w u v p 2 (decide (u = v)) 0 := by
  let l := max u.length v.length
  have hu : u.length ≤ l := le_max_left _ _
  have hv : v.length ≤ l := le_max_right _ _
  have hscan := e3c_compare_scan w u v p l (le_refl _)
  rw [List.take_of_length_le hu, List.take_of_length_le hv] at hscan
  have hturn : e3cCompareTM.tm.step (e3cCompareCfg w u v p 0 (decide (u = v)) l) =
      e3cCompareCfg w u v p 1 (decide (u = v)) ((l : ℤ) - 1) := by
    simp only [MultiTapeTM.step, e3cCompareCfg, e3cCompareTM,
      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
      List.getElem?_eq_none hu, List.getElem?_eq_none hv, and_self, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, sub_eq_add_neg]
  have hfirst : e3cCompareTM.tm.runFrom (e3cCompareCfg w u v p 0 true 0) (l + 1) =
      e3cCompareCfg w u v p 1 (decide (u = v)) ((l : ℤ) - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hscan, hturn]
  rw [show 2 * (max u.length v.length + 1) = (l + 1) + (l + 1) by dsimp [l]; omega,
    MultiTapeTM.runFrom_add, hfirst]
  exact e3c_compare_rewind w u v p (decide (u = v)) l (le_refl _)

/-- A contiguous visited interval, marked independently of the simulated data.
The bounds are proof data; the cleaner reads only the marker tape. -/
private def e3cInterval (left : ℤ) (width : ℕ) (z : ℤ) : Option Bool :=
  if left ≤ z ∧ z < left + width then some true else none

/-- Erase the first `j` cells of a visited interval without changing any other
cell. This describes the cleaner's successive physical tape contents. -/
private def e3cCleared (data : ℤ → Option Bool) (left : ℤ) (j : ℕ) (z : ℤ) : Option Bool :=
  if left ≤ z ∧ z < left + j then none else data z

/-- One native erasure enlarges the cleared interval by exactly one cell. -/
private lemma e3c_cleared_step (data : ℤ → Option Bool) (left : ℤ) (j : ℕ) :
    Function.update (e3cCleared data left j) (left + j) none =
      e3cCleared data left (j + 1) := by
  funext z
  by_cases hz : z = left + j
  · subst z; simp [e3cCleared]
  · rw [Function.update_of_ne hz]
    have hiff : (left ≤ z ∧ z < left + j) ↔
        (left ≤ z ∧ z < left + (j + 1 : ℕ)) := by omega
    simp only [e3cCleared, hiff]

/-- A marked finite work interval can be cleared natively despite arbitrary
blank holes in its data. Tape one marks the visited interval; tape two marks
only the origin. All three heads stay aligned. Return state three is silent. -/
private def e3cClearTM : FinTM Bool where
  k := 3
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q _ work => match q.val with
      | 0 => if work 1 = none then
          ⟨0, fun _ => (none, .pos), none, some 1⟩
        else ⟨0, fun _ => (none, .neg), none, some 0⟩
      | 1 => if work 1 = none then
          ⟨0, fun _ => (none, .neg), none, some 2⟩
        else ⟨0, fun i => (if i = 2 then none else some none, .pos), none, some 1⟩
      | 2 => if work 2 = none then
          ⟨0, fun _ => (none, .neg), none, some 2⟩
        else ⟨0, fun i => (if i = 2 then some none else none, 0), none, some 3⟩
      | _ => controlAction 0 (some 3) }

/-- The cleaner's three tapes hold data, the interval marker, and the origin
marker, respectively. The native input and physical output are untouched. -/
private def e3cClearCfg (w : List Bool) (p : Fin (w.length + 2)) (q : Fin 4)
    (data marks origin : ℤ → Option Bool) (h : ℤ) : Cfg 3 Bool e3cClearTM.State w :=
  ⟨some q, p, (fun i => match i.val with | 0 => data | 1 => marks | _ => origin), fun _ => h, []⟩

/-- The initial left scan reaches the marked interval's left end in `j+2`
steps, independently of blank holes in the data being cleared.
**Proof sketch.** Induct on the distance from the marked left endpoint. The marker,
independent of the data, forces every left move; its first blank triggers
the one-step return to the first marked cell. -/
private lemma e3c_clear_left (w : List Bool) (p : Fin (w.length + 2))
    (data : ℤ → Option Bool) (left : ℤ) (width : ℕ) :
    ∀ j, j < width →
      e3cClearTM.tm.runFrom
        (e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true]) (left + j))
        (j + 2) =
      e3cClearCfg w p 1 data (e3cInterval left width) (bufferTape [true]) left := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hmark : e3cInterval left width left = some true := by
      simp [e3cInterval]; omega
    have hblank : e3cInterval left width (left - 1) = none := by
      simp [e3cInterval]
    have hs : e3cClearTM.tm.step
        (e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true]) left) =
        e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true]) (left - 1) := by
      simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols,
        hmark, reduceCtorEq, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    have hs' : e3cClearTM.tm.step
        (e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true]) (left - 1)) =
        e3cClearCfg w p 1 data (e3cInterval left width) (bufferTape [true]) left := by
      simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols,
        hblank, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply]
    simpa only [Nat.cast_zero, add_zero] using
      show e3cClearTM.tm.step (e3cClearTM.tm.step
        (e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true]) left)) = _
        from by rw [hs, hs']
  | succ j ih =>
    intro hj
    have hmark : e3cInterval left width (left + (j + 1 : ℕ)) = some true := by
      simp [e3cInterval]; omega
    have hs : e3cClearTM.tm.step
        (e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true])
          (left + (j + 1 : ℕ))) =
        e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true]) (left + j) := by
      simp only [e3cClearCfg, MultiTapeTM.step, e3cClearTM, Cfg.workTapeSymbols,
        Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply]; omega
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Before any erasure, the data tape is unchanged. -/
private lemma e3c_cleared_zero (data : ℤ → Option Bool) (left : ℤ) :
    e3cCleared data left 0 = data := by
  funext z
  simp [e3cCleared]

/-- Clearing the full marked interval removes all data if there was no data
outside it. No assumption is made about holes or values inside the interval. -/
private lemma e3c_cleared_all (data : ℤ → Option Bool) (left : ℤ) (width : ℕ)
    (hdata : ∀ z, ¬(left ≤ z ∧ z < left + width) → data z = none) :
    e3cCleared data left width = fun _ => none := by
  funext z
  by_cases hz : left ≤ z ∧ z < left + width
  · simp [e3cCleared, hz]
  · simp [e3cCleared, hz, hdata z hz]

/-- The right scan clears data and its interval marker in lockstep while
leaving the separate origin marker intact.
**Proof sketch.** Induct on the number of remaining marked cells. Each transition clears
one data cell and its marker, advances both heads, and preserves the origin. -/
private lemma e3c_clear_scan (w : List Bool) (p : Fin (w.length + 2))
    (data : ℤ → Option Bool) (left : ℤ) (width : ℕ) :
    ∀ j, j ≤ width →
      e3cClearTM.tm.runFrom
        (e3cClearCfg w p 1 data (e3cInterval left width) (bufferTape [true]) left) j =
      e3cClearCfg w p 1 (e3cCleared data left j)
        (e3cCleared (e3cInterval left width) left j) (bufferTape [true]) (left + j) := by
  intro j
  induction j with
  | zero => intro _; simp [e3c_cleared_zero]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hmark : e3cCleared (e3cInterval left width) left j (left + j) = some true := by
      simp [e3cCleared, e3cInterval]; omega
    simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM,
      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hmark,
      reduceCtorEq, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      fin_cases i
      · simpa [Action.apply] using e3c_cleared_step data left j
      · simpa [Action.apply] using e3c_cleared_step (e3cInterval left width) left j
      · simp [Action.apply]
    · funext i; simp [Action.apply]; omega

/-- Removing the only origin marker makes its entire tape blank. -/
private lemma e3c_origin_erase :
    Function.update (bufferTape [true]) 0 none = fun _ => none := by
  funext z
  by_cases hz : z = 0
  · subst z; simp
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hn : 0 < z.toNat := by omega
      simp [bufferTape, h0, List.getElem?_eq_none (by simp; omega : [true].length ≤ z.toNat)]
    · simp [bufferTape, h0]

/-- Once the interval is erased, the surviving origin marker returns all
three heads to zero and is itself erased on the final transition.
**Proof sketch.** Induct on the distance to zero. The singleton origin marker distinguishes
the stopping cell; that transition erases the marker and retains all heads there. -/
private lemma e3c_clear_origin (w : List Bool) (p : Fin (w.length + 2)) :
    ∀ n : ℕ, e3cClearTM.tm.runFrom
      (e3cClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n) (n + 1) =
      e3cClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
  intro n
  induction n with
  | zero =>
    change (⟨0, (fun i : Fin 3 => (if i = 2 then some none else none, 0)),
      none, some (3 : Fin 4)⟩ : Action 3 Bool (Fin 4)).apply
      (e3cClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) 0) = _
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      fin_cases i <;> simp [Action.apply, e3cClearCfg, e3c_origin_erase]
    · funext i; simp [Action.apply, e3cClearCfg]
  | succ n ih =>
    have hblank : bufferTape [true] ((n + 1 : ℕ) : ℤ) = none := by
      rw [bufferTape_nat]; simp
    have hs : e3cClearTM.tm.step
        (e3cClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) (n + 1 : ℕ)) =
        e3cClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
      simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols,
        Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih

/-- Native cleanup of a finite marked work interval returns three blank tapes
with all heads at zero in a positive, linear number of steps.
**Proof sketch.** Scan left to the interval boundary, clear the entire interval
while moving right, then use the untouched origin marker to rewind. That last
marker is erased only when the heads are already at zero. All dispatches use
observed tape symbols; the interval bounds occur solely in the proof. -/
private lemma e3c_clear_run (w : List Bool) (p : Fin (w.length + 2))
    (data : ℤ → Option Bool) (left : ℤ) (width j : ℕ)
    (hleft : left ≤ 0) (hright : 0 < left + width) (hj : j < width)
    (hdata : ∀ z, ¬(left ≤ z ∧ z < left + width) → data z = none) :
    ∃ t, 0 < t ∧ t ≤ 3 * width + 4 ∧
      e3cClearTM.tm.runFrom
        (e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true]) (left + j)) t =
      e3cClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
  let n := (left + width - 1).toNat
  have hn : (n : ℤ) = left + width - 1 := by dsimp [n]; omega
  have hnlt : n < width := by omega
  have hscan := e3c_clear_scan w p data left width width (le_refl _)
  rw [e3c_cleared_all data left width hdata,
    e3c_cleared_all (e3cInterval left width) left width
      (by intro z hz; simp [e3cInterval, hz])] at hscan
  have hturn : e3cClearTM.tm.step
      (e3cClearCfg w p 1 (fun _ => none) (fun _ => none)
        (bufferTape [true]) (left + width)) =
      e3cClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
    simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols,
      Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]; omega
  have hforward : e3cClearTM.tm.runFrom
      (e3cClearCfg w p 1 data (e3cInterval left width) (bufferTape [true]) left)
      (width + 1) =
      e3cClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hscan, hturn]
  have hfirst : e3cClearTM.tm.runFrom
      (e3cClearCfg w p 0 data (e3cInterval left width) (bufferTape [true]) (left + j))
      ((j + 2) + (width + 1)) =
      e3cClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
    rw [MultiTapeTM.runFrom_add, e3c_clear_left w p data left width j hj, hforward]
  refine ⟨(j + 2) + (width + 1) + (n + 1), by omega, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, hfirst, e3c_clear_origin]

/-- A closed visited-cell interval; nonblank data may have arbitrary holes
inside this independently maintained marker. -/
private def e3cSpan (lo hi z : ℤ) : Option Bool :=
  if lo ≤ z ∧ z ≤ hi then some true else none

/-- Marking a cell at most one step outside a contiguous visited interval
extends exactly its appropriate endpoint. -/
private lemma e3c_span_extend (lo hi h : ℤ) (hord : lo ≤ hi)
    (hnear : lo - 1 ≤ h ∧ h ≤ hi + 1) :
    Function.update (e3cSpan lo hi) h (some true) = e3cSpan (min lo h) (max hi h) := by
  funext z
  by_cases hz : z = h
  · subst z
    simp [e3cSpan, min_le_right, le_max_right]
  · rw [Function.update_of_ne hz]
    have he : (lo ≤ z ∧ z ≤ hi) ↔ (min lo h ≤ z ∧ z ≤ max hi h) := by omega
    simp only [e3cSpan, he]

/-- Three separate banks hold simulated data, visited-cell markers, and
origin markers. Corresponding heads always move together. -/
private def e3cSlots {α : Type} {k : ℕ} (data marks origin : Fin k → α) :
    Fin (k + (k + k)) → α := Fin.addCases data (Fin.addCases marks origin)

/-- A tracked evaluator uses two native steps per source step. The first
performs the source action; the second marks the new head cells before
possibly halting. Initialization marks each origin in both marker banks.
Physical output remains the source output, ready for the capture wrapper. -/
private def e3cTrackTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + (M.k + M.k)
  State := M.State ⊕ (Option M.State ⊕ Unit)
  tm := {
    q₀ := .inr (.inr ())
    tr := fun q inp work => match q with
      | .inr (.inr ()) =>
        ⟨0, e3cSlots (fun _ => (none, 0))
          (fun _ => (some (some true), 0)) (fun _ => (some (some true), 0)),
          none, some (.inl M.tm.q₀)⟩
      | .inl q =>
        let a := M.tm.tr q inp (fun i => work (Fin.castAdd (M.k + M.k) i))
        ⟨a.inputTape, e3cSlots a.workTapes
          (fun i => (none, (a.workTapes i).2)) (fun i => (none, (a.workTapes i).2)),
          a.output, some (.inr (.inl a.state))⟩
      | .inr (.inl next) =>
        ⟨0, e3cSlots (fun _ => (none, 0))
          (fun _ => (some (some true), 0)) (fun _ => (none, 0)),
          none, next.map Sum.inl⟩ }

/-- A completed tracked source step, with source data unchanged and the
visited interval covering each current source head. -/
private def e3cTrackCfg (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) :
    Cfg (e3cTrackTM M).k Bool (e3cTrackTM M).State x :=
  ⟨c.state.map Sum.inl, c.inputPos,
    e3cSlots c.workTapes (fun i => e3cSpan (lo i) (hi i)) (fun _ => bufferTape [true]),
    e3cSlots c.workTapePos c.workTapePos c.workTapePos, c.output⟩

/-- The intermediate stamp state retains the previous interval markers while
the source data, input, heads, and emitted output already reflect its action. -/
private def e3cTrackMid (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) :
    Cfg (e3cTrackTM M).k Bool (e3cTrackTM M).State x :=
  { e3cTrackCfg M c lo hi with state := some (.inr (.inl c.state)) }

/-- The source-action microstep preserves the exact data simulation and moves
both marker heads by that same action. It includes any halting emission.
**Proof sketch.** Unfold the actual source action and compare all configuration fields.
Separate the three tape banks: data performs the source write, while both
marker banks move without writing and retain aligned heads. -/
private lemma e3c_track_action (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) (hc : c.state ≠ none) :
    (e3cTrackTM M).tm.step (e3cTrackCfg M c lo hi) =
      e3cTrackMid M (M.tm.step c) lo hi := by
  cases hs : c.state with
  | none => exact False.elim (hc hs)
  | some q =>
    have hin : (e3cTrackCfg M c lo hi).inputSymbol = c.inputSymbol := rfl
    have hwork : (fun i => (e3cTrackCfg M c lo hi).workTapeSymbols
        (Fin.castAdd (M.k + M.k) i)) = c.workTapeSymbols := by
      funext i
      simp [e3cTrackCfg, Cfg.workTapeSymbols, e3cSlots]
    have hs' : (e3cTrackCfg M c lo hi).state = some (.inl q) := by
      simp only [e3cTrackCfg, hs, Option.map_some]
    simp only [MultiTapeTM.step, hs', hs]
    change ((e3cTrackTM M).tm.tr (.inl q) _ _).apply _ = _
    dsimp only [e3cTrackTM]
    rw [hin, hwork]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [e3cTrackMid, e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [e3cTrackMid, e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [e3cTrackMid, e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [e3cTrackMid, e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat]

/-- The second microstep stamps every new current head, extending the
contiguous visited interval and halting only after those stamps are complete.
**Proof sketch.** Split the three tape banks. The source and origin tapes are unchanged;
writing the newly reached cell in the visited bank extends its interval
by the one-step head bound, before the stored successor state is dispatched. -/
private lemma e3c_track_stamp (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ)
    (hord : ∀ i, lo i ≤ hi i)
    (hnear : ∀ i, lo i - 1 ≤ c.workTapePos i ∧ c.workTapePos i ≤ hi i + 1) :
    (e3cTrackTM M).tm.step (e3cTrackMid M c lo hi) =
      e3cTrackCfg M c (fun i => min (lo i) (c.workTapePos i))
        (fun i => max (hi i) (c.workTapePos i)) := by
  simp only [MultiTapeTM.step, e3cTrackMid, e3cTrackTM]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j
        simpa [e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat] using
          e3c_span_extend (lo j) (hi j) (c.workTapePos j) (hord j) (hnear j)
      · intro j; simp [e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [e3cTrackCfg, e3cSlots, Action.apply, -Fin.natAdd_eq_addNat]
  · simp [e3cTrackCfg, Action.apply]

/-- Leftmost visited source-head position, including the initial origin. -/
private def e3cLo (M : FinTM Bool) (x : List Bool) : ℕ → Fin M.k → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun i => min (e3cLo M x t i)
      ((M.tm.runFrom (M.tm.initCfg x) (t + 1)).workTapePos i)

/-- Rightmost visited source-head position, including the initial origin. -/
private def e3cHi (M : FinTM Bool) (x : List Bool) : ℕ → Fin M.k → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun i => max (e3cHi M x t i)
      ((M.tm.runFrom (M.tm.initCfg x) (t + 1)).workTapePos i)

/-- The visited interval contains zero and the current head and has width
at most twice the elapsed source time plus one. -/
private lemma e3c_track_extent (M : FinTM Bool) (x : List Bool) :
    ∀ t (i : Fin M.k), e3cLo M x t i ≤ 0 ∧ 0 ≤ e3cHi M x t i ∧
      e3cLo M x t i ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ e3cHi M x t i ∧
      -(t : ℤ) ≤ e3cLo M x t i ∧ e3cHi M x t i ≤ t := by
  intro t
  induction t with
  | zero => intro i; simp [e3cLo, e3cHi, MultiTapeTM.initCfg, Cfg.init]
  | succ t ih =>
    intro i
    have hp := M.tm.workTapePos_step_le (M.tm.runFrom (M.tm.initCfg x) t) i
    rw [abs_le, ← MultiTapeTM.runFrom_succ_eq_step'] at hp
    have hh := ih i
    dsimp only [e3cLo, e3cHi]
    push_cast
    omega

/-- Every cell written by the source lies inside its visited interval.
The claim concerns actual writes and allows arbitrary blank cells inside it.
**Proof sketch.** Induct over the actual source trace. An unwritten cell retains its old
support bound; a newly written cell is the previous head, already in the
previous interval and therefore in the enlarged interval. -/
private lemma e3c_track_support (M : FinTM Bool) (x : List Bool) :
    ∀ t (i : Fin M.k) (z : ℤ),
      ¬(e3cLo M x t i ≤ z ∧ z ≤ e3cHi M x t i) →
        (M.tm.runFrom (M.tm.initCfg x) t).workTapes i z = none := by
  intro t
  induction t with
  | zero => intro i z hz; rfl
  | succ t ih =>
    intro i z hz
    have hb := e3c_track_extent M x t i
    have hz' : ¬(e3cLo M x t i ≤ z ∧ z ≤ e3cHi M x t i) := by
      dsimp only [e3cLo, e3cHi] at hz
      omega
    have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i := by omega
    rw [MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    cases hs : (M.tm.runFrom (M.tm.initCfg x) t).state with
    | none => exact ih i z hz'
    | some q =>
      dsimp only [Action.apply]
      cases hw : ((M.tm.tr q (M.tm.runFrom (M.tm.initCfg x) t).inputSymbol
        (M.tm.runFrom (M.tm.initCfg x) t).workTapeSymbols).workTapes i).1
      · exact ih i z hz'
      · dsimp only
        rw [Function.update_of_ne hne]
        exact ih i z hz'

/-- The singleton origin marker is the zero-width source trace's visited span. -/
private lemma e3c_span_zero : e3cSpan 0 0 = bufferTape [true] := by
  funext z
  by_cases hz : z = 0
  · subst z; rfl
  · have hspan : ¬(0 ≤ z ∧ z ≤ 0) := by omega
    by_cases hn : 0 ≤ z
    · have hlen : [true].length ≤ z.toNat := by simp; omega
      simp [e3cSpan, hspan, bufferTape, hn, List.getElem?_eq_none hlen]; omega
    · simp [e3cSpan, hspan, bufferTape, hn]

/-- A single native initialization step installs both origin markers while
leaving source work blank, the source input head at one, and output empty. -/
private lemma e3c_track_initial (M : FinTM Bool) (x : List Bool) :
    (e3cTrackTM M).tm.runFrom ((e3cTrackTM M).tm.initCfg x) 1 =
      e3cTrackCfg M (M.tm.initCfg x) (fun _ => 0) (fun _ => 0) := by
  change (e3cTrackTM M).tm.step ((e3cTrackTM M).tm.initCfg x) = _
  simp only [MultiTapeTM.step, MultiTapeTM.initCfg, Cfg.init, e3cTrackTM]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [Action.apply, e3cTrackCfg, e3cSlots, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simpa only [Action.apply, e3cTrackCfg, e3cSlots, Fin.addCases_left,
          Fin.addCases_right, e3c_span_zero, bufferTape_nil] using
            (bufferTape_append [] true).symm
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [Action.apply, e3cTrackCfg, e3cSlots, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply, e3cTrackCfg, e3cSlots, -Fin.natAdd_eq_addNat]

/-- The tracked machine has the exact source configuration after two native
steps per source step, plus initialization. Its interval markers record the
actual trace, including after the source has halted.
**Proof sketch.** Initialization marks the origins. For a live source, its
action moves all three corresponding heads together, then the stamp expands
the visited interval by at most one cell. A halted source and its tracked
image are both absorbing, and the already-contained head changes neither bound. -/
private lemma e3c_track_run (M : FinTM Bool) (x : List Bool) :
    ∀ t, (e3cTrackTM M).tm.runFrom ((e3cTrackTM M).tm.initCfg x) (1 + 2 * t) =
      e3cTrackCfg M (M.tm.runFrom (M.tm.initCfg x) t) (e3cLo M x t) (e3cHi M x t) := by
  intro t
  induction t with
  | zero => simpa [e3cLo, e3cHi] using e3c_track_initial M x
  | succ t ih =>
    let c := M.tm.runFrom (M.tm.initCfg x) t
    have hb := e3c_track_extent M x t
    have hnext : M.tm.runFrom (M.tm.initCfg x) (t + 1) = M.tm.step c := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
    rw [show 1 + 2 * (t + 1) = (1 + 2 * t) + 2 by omega, MultiTapeTM.runFrom_add, ih]
    cases hs : c.state with
    | none =>
      have hl : e3cLo M x (t + 1) = e3cLo M x t := by
        funext i
        simp only [e3cLo, MultiTapeTM.runFrom_succ_eq_step']
        change min (e3cLo M x t i) ((M.tm.step c).workTapePos i) = _
        rw [MultiTapeTM.step_of_halt hs, min_eq_left (hb i).2.2.1]
      have hr : e3cHi M x (t + 1) = e3cHi M x t := by
        funext i
        simp only [e3cHi, MultiTapeTM.runFrom_succ_eq_step']
        change max (e3cHi M x t i) ((M.tm.step c).workTapePos i) = _
        rw [MultiTapeTM.step_of_halt hs, max_eq_left (hb i).2.2.2.1]
      have hhalt : (e3cTrackCfg M c (e3cLo M x t) (e3cHi M x t)).state = none := by
        simp only [e3cTrackCfg, hs, Option.map_none]
      rw [hl, hr, hnext]
      change (e3cTrackTM M).tm.runFrom (e3cTrackCfg M c _ _) 2 = e3cTrackCfg M (M.tm.step c) _ _
      rw [MultiTapeTM.runFrom_of_halt _ hhalt, MultiTapeTM.step_of_halt hs]
    | some q =>
      have hlive : c.state ≠ none := by rw [hs]; simp
      have hnear (i : Fin M.k) : e3cLo M x t i - 1 ≤ (M.tm.step c).workTapePos i ∧
          (M.tm.step c).workTapePos i ≤ e3cHi M x t i + 1 := by
        have hm := M.tm.workTapePos_step_le c i
        rw [abs_le] at hm
        have hh := hb i
        dsimp only [c] at hm ⊢
        omega
      change (e3cTrackTM M).tm.step ((e3cTrackTM M).tm.step (e3cTrackCfg M c _ _)) = _
      rw [e3c_track_action M c _ _ hlive,
        e3c_track_stamp M (M.tm.step c) _ _ (fun i => by have hh := hb i; omega) hnear]
      dsimp only [e3cLo, e3cHi]
      rw [hnext]

/-- The trace markers cost exactly two native steps per source step and one
initialization step. The output and halting judgment are unchanged. -/
private lemma e3c_track_computes (M : FinTM Bool) (x out : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x out T) :
    (e3cTrackTM M).ComputesInTime x out (1 + 2 * T) := by
  have hc := (computesInTime_iff M x out T).mp hM
  apply (computesInTime_iff _ _ _ _).mpr
  rw [e3c_track_run]
  exact ⟨by simp only [e3cTrackCfg, hc.1, Option.map_none], hc.2⟩

/-! Native accepting emission, adapted from the audited split emitter in
`Build/Primitives.lean` at the pinned base. The administrative bank is blank,
so it can enter after the new round's cleanup; no library source is changed. -/

/-- A physical input position after consuming a unary count, saturated at the
right boundary. -/
private def e3cSplitPos (w : List Bool) (j : ℕ) : Fin (w.length + 2) :=
  ⟨min j w.length + 1, by omega⟩

/-- A saturated countdown read is blank exactly after all input bits. -/
private lemma e3cSplitPos_read {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = e3cSplitPos w j) :
    cfg.inputSymbol = if h : j < w.length then some (w[j]'h) else none := by
  by_cases hj : j < w.length
  · rw [dif_pos hj]
    exact inputSymbolInner j
      (by simp [hp, e3cSplitPos, Nat.min_eq_left (by omega : j ≤ w.length), Nat.add_comm]) hj
  · rw [dif_neg hj]
    simp [Cfg.inputSymbol, hp, e3cSplitPos, Nat.min_eq_right (by omega : w.length ≤ j)]

/-- A forward move increments a saturated unary countdown position. -/
private lemma e3cSplitPos_succ (w : List Bool) (j : ℕ) :
    moveInputPos (e3cSplitPos w j) .pos = e3cSplitPos w (j + 1) := by
  by_cases hj : j < w.length
  · rw [moveInputPos_pos_of_ne_right _ (by simp [e3cSplitPos] <;> omega)]
    apply Fin.ext
    simp only [e3cSplitPos, Fin.val_mk]
    omega
  · have he : e3cSplitPos w j = ⟨w.length + 1, by omega⟩ := by
      apply Fin.ext
      simp [e3cSplitPos, Nat.min_eq_right (by omega : w.length ≤ j)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [e3cSplitPos, Nat.min_eq_right (by omega : w.length ≤ j + 1)]

/-- Emit a native-input split, using tape zero only as a length counter.
The first two states double native bits, state two completes the separator,
and state three copies the native suffix. No candidate bit is emitted. -/
private def e3cSplitEmitTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), some false, some 2⟩
        | some _ => ⟨0, fun _ => (none, 0), inp, some 1⟩
      | 1 => ⟨.pos, Fin.cases (none, .pos) (fun _ => (none, 0)), inp, some 0⟩
      | 2 => ⟨0, fun _ => (none, 0), some true, some 3⟩
      | _ => match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some 3⟩
        | none => controlAction 0 none }

/-- The accepting phase retains the candidate and an entirely blank scratch
bank. Its output is only the native prefix, separator, and native suffix. -/
private def e3cSplitEmitCfg (k : ℕ) (w s : List Bool) (q : Option (Fin 4))
    (j h : ℕ) (out : List Bool) : Cfg (k + 1) Bool (Fin 4) w :=
  ⟨q, e3cSplitPos w j, Fin.cases (bufferTape s) (fun _ => (fun _ => none)),
    Fin.cases (h : ℤ) (fun _ => 0), out⟩

/-- Two transitions emit two copies of the current native bit and advance
both the native head and the candidate counter. Arbitrary candidate bit
values are read only for their presence.
**Proof sketch.** Induct on the number of doubled cells. The two transitions
read the same native bit, emit it twice, and only then advance both heads. -/
private lemma e3cSplitEmit_double (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    ∀ j, j ≤ s.length → (e3cSplitEmitTM k).tm.runFrom
      (e3cSplitEmitCfg k w s (some 0) 0 0 []) (2 * j) =
      e3cSplitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread (q : Fin 4) (out : List Bool) :
        (e3cSplitEmitCfg k w s (some q) j j out).inputSymbol = some (w[j]'(by omega)) := by
      rw [e3cSplitPos_read w _ j rfl, dif_pos (by omega)]
    have hwork : (e3cSplitEmitCfg k w s (some 0) j j
        ((w.take j).flatMap fun b => [b, b])).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [e3cSplitEmitCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < s.length)]
    have hfirst : (e3cSplitEmitTM k).tm.step
        (e3cSplitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b])) =
        e3cSplitEmitCfg k w s (some 1) j j
          (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change ((e3cSplitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
      simp only [e3cSplitEmitTM, hwork, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, e3cSplitEmitCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change ((e3cSplitEmitTM k).tm.tr (1 : Fin 4) _ _).apply _ = _
    simp only [e3cSplitEmitTM, hread]
    refine Cfg.ext rfl (e3cSplitPos_succ w j) ?_ ?_ ?_
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp [Action.apply, e3cSplitEmitCfg]
    · change (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) ++
          [w[j]'(by omega)] = (w.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < w.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Once the counter is exhausted, emit the two separator bits without
moving the native head away from the beginning of the suffix. -/
private lemma e3cSplitEmit_separator (k : ℕ) (w s : List Bool) (out : List Bool) :
    (e3cSplitEmitTM k).tm.runFrom (e3cSplitEmitCfg k w s (some 0) s.length s.length out) 2 =
      e3cSplitEmitCfg k w s (some 3) s.length s.length (out ++ [false, true]) := by
  have hwork : (e3cSplitEmitCfg k w s (some 0) s.length s.length out).workTapeSymbols 0 = none := by
    simp [e3cSplitEmitCfg, Cfg.workTapeSymbols]
  have hf : (e3cSplitEmitTM k).tm.step (e3cSplitEmitCfg k w s (some 0) s.length s.length out) =
      e3cSplitEmitCfg k w s (some 2) s.length s.length (out ++ [false]) := by
    unfold MultiTapeTM.step
    change ((e3cSplitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
    simp only [e3cSplitEmitTM, hwork]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, e3cSplitEmitCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step,
    show (e3cSplitEmitTM k).tm.step _ = _ from hf, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext i; simp [MultiTapeTM.step, e3cSplitEmitTM, Action.apply, e3cSplitEmitCfg]
  · simp [MultiTapeTM.step, e3cSplitEmitTM, Action.apply, e3cSplitEmitCfg, List.append_assoc]

/-- The suffix-copy phase preserves all work tapes and copies native bits
verbatim, including the empty suffix and its final blank-reading halt.
**Proof sketch.** Induct on the remaining suffix while allowing arbitrary
already-copied prefix and output. The nonempty case copies one native bit;
the empty case reads the right blank and halts without an extra emission. -/
private lemma e3cSplitEmit_suffix (k : ℕ) (w s rest : List Bool) :
    ∀ pre out h, w = pre ++ rest → (e3cSplitEmitTM k).tm.runFrom
      (e3cSplitEmitCfg k w s (some 3) pre.length h out) (rest.length + 1) =
      e3cSplitEmitCfg k w s none w.length h (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out h hw
    have he : w = pre := by simpa using hw
    clear hw
    subst w
    simp only [List.append_nil, List.length_nil, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := e3cSplitPos_read pre (e3cSplitEmitCfg k pre s (some 3) pre.length h out) pre.length rfl
    simp only [Nat.lt_irrefl, ↓reduceDIte] at hr
    unfold MultiTapeTM.step
    change ((e3cSplitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [hr]
    simp [e3cSplitEmitTM, controlAction, e3cSplitEmitCfg]
  | cons b rest ih =>
    intro pre out h hw
    have hread : (e3cSplitEmitCfg k w s (some 3) pre.length h out).inputSymbol = some b := by
      rw [e3cSplitPos_read w _ pre.length rfl]
      simp [hw]
    have hstep : (e3cSplitEmitTM k).tm.step (e3cSplitEmitCfg k w s (some 3) pre.length h out) =
        e3cSplitEmitCfg k w s (some 3) (pre ++ [b]).length h (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((e3cSplitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
      rw [hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using e3cSplitPos_succ w pre.length
      · funext i; simp [e3cSplitEmitTM, Action.apply, e3cSplitEmitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) h (by simpa [List.append_assoc] using hw)

/-- The accepting emitter produces exactly the encoded native split in
`|s|+|w|+3` steps. Its candidate may contain any bit pattern.
**Proof sketch.** Double exactly the native prefix counted by the candidate,
emit the separator, and copy the remaining native suffix. Concatenate the
three exact runs and cancel the prefix length in the time expression. -/
private lemma e3cSplitEmit_run (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    (e3cSplitEmitTM k).tm.runFrom (e3cSplitEmitCfg k w s (some 0) 0 0 [])
      (s.length + w.length + 3) =
      e3cSplitEmitCfg k w s none w.length s.length
        (pairEncode (w.take s.length) (w.drop s.length)) := by
  have ht : s.length + w.length + 3 =
      2 * s.length + 2 + ((w.drop s.length).length + 1) := by
    simp only [List.length_drop]; omega
  rw [ht, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add _ (2 * s.length) 2,
    e3cSplitEmit_double k w s hs _ (le_refl _), e3cSplitEmit_separator]
  have h := e3cSplitEmit_suffix k w s (w.drop s.length) (w.take s.length)
    (((w.take s.length).flatMap fun b => [b, b]) ++ [false, true]) s.length
    (List.take_append_drop s.length w).symm
  simpa [List.length_take, Nat.min_eq_left hs, pairEncode] using h

/-- A closed visited span is the cleaner's half-open interval with exactly
one cell for each visited integer, including both endpoints. -/
private lemma e3c_span_interval (lo hi : ℤ) (h : lo ≤ hi) :
    e3cSpan lo hi = e3cInterval lo (hi - lo + 1).toNat := by
  funext z
  have hw : ((hi - lo + 1).toNat : ℤ) = hi - lo + 1 := by omega
  have he : (lo ≤ z ∧ z ≤ hi) ↔
      (lo ≤ z ∧ z < lo + ((hi - lo + 1).toNat : ℤ)) := by rw [hw]; omega
  simp only [e3cSpan, e3cInterval, he]

/-- Each actual source work tape, together with its tracked interval and
origin marker, satisfies the native cleaner's full restoration contract.
The common bound is linear in the actual elapsed source time.
**Proof sketch.** The trace invariant gives a visited interval containing the
head and zero, no nonblank cell outside it, and width at most `2T+1`.
Instantiate the proved interval cleaner, whose entire three-tape endpoint is
blank with every head zero, and absorb its cost into `6T+7`. -/
private lemma e3c_track_clearable (M : FinTM Bool) (x w : List Bool)
    (p : Fin (w.length + 2)) (T : ℕ) (i : Fin M.k) :
    ∃ t, 0 < t ∧ t ≤ 6 * T + 7 ∧
      e3cClearTM.tm.runFrom
        (e3cClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
          (e3cSpan (e3cLo M x T i) (e3cHi M x T i)) (bufferTape [true])
          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) t =
      e3cClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
  let lo := e3cLo M x T i
  let hi := e3cHi M x T i
  let h := (M.tm.runFrom (M.tm.initCfg x) T).workTapePos i
  let width := (hi - lo + 1).toNat
  let j := (h - lo).toNat
  have hb := e3c_track_extent M x T i
  have hw : (width : ℤ) = hi - lo + 1 := by dsimp only [width, hi, lo]; omega
  have hj : (j : ℤ) = h - lo := by dsimp only [j, h, lo]; omega
  have hwidth : width ≤ 2 * T + 1 := by dsimp only [hi, lo] at hw; omega
  have hpos : 0 < lo + width := by dsimp only [lo, hi] at hw ⊢; omega
  have hjlt : j < width := by dsimp only [h, lo, hi] at hw hj; omega
  have hdata : ∀ z, ¬(lo ≤ z ∧ z < lo + width) →
      (M.tm.runFrom (M.tm.initCfg x) T).workTapes i z = none := by
    intro z hz
    apply e3c_track_support M x T i z
    dsimp only [lo, hi] at hw hz
    omega
  obtain ⟨t, htpos, ht, hr⟩ := e3c_clear_run w p
    ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i) lo width j hb.1 hpos hjlt hdata
  refine ⟨t, htpos, by omega, ?_⟩
  have hhead : lo + j = h := by omega
  rw [hhead] at hr
  rw [e3c_span_interval _ _ (by have := hb; omega)]
  exact hr

/-- A phase with an absorbing return state can be cut at its actual first
return while retaining its complete configuration endpoint.
**Proof sketch.** Choose the least return-state visit. Absorption identifies
its configuration with the known bounded endpoint. The bound proves existence
and bounds the first visit; it is never used to dispatch native control. -/
private lemma e3c_first_entry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop) [DecidablePred stop]
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q := ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- The silent comparator reaches its exact endpoint on its first visit to
either Boolean return state, after a positive number of steps.
**Proof sketch.** Use the exact bounded comparator run and cut it at the first visit to
either absorbing return state. Absorption identifies the full endpoint;
the initial scan state excludes time zero. -/
private lemma e3c_compare_first (w u v : List Bool) (p : Fin (w.length + 2)) :
    ∃ t, 0 < t ∧ t ≤ 2 * (max u.length v.length + 1) ∧
      (∀ j < t, ∀ b, (e3cCompareTM.tm.runFrom
        (e3cCompareCfg w u v p 0 true 0) j).state ≠ some (2, b)) ∧
      e3cCompareTM.tm.runFrom (e3cCompareCfg w u v p 0 true 0) t =
        e3cCompareCfg w u v p 2 (decide (u = v)) 0 := by
  obtain ⟨t, ht, hfirst, hr⟩ := e3c_first_entry e3cCompareTM.tm
    (fun q : Fin 3 × Bool => q.1 = 2)
    (e3cCompareCfg w u v p 0 true 0) (e3cCompareCfg w u v p 2 (decide (u = v)) 0)
    (2 * (max u.length v.length + 1)) (by
      rintro z ⟨⟨q, b⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      unfold MultiTapeTM.step
      rw [hz]
      change (controlAction 0 (some (2, b))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    ⟨(2, decide (u = v)), rfl, rfl⟩ (e3c_compare_run w u v p)
  have hpos : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    have hh := congrArg Cfg.state hr
    simp [hz, e3cCompareCfg] at hh
    have hv := congrArg (fun q : Fin 3 × Bool => q.1.val) hh
    norm_num at hv
  exact ⟨t, hpos, ht, fun j hj b hb => hfirst j hj ⟨(2, b), hb, rfl⟩, hr⟩

/-- Each tracked tape's native cleanup can dispatch at its actual positive
first return with the exact blank endpoint, never at the analysis deadline.
**Proof sketch.** Apply the per-tape bounded cleanup, then cut the absorbing return state
at its first visit. The initial left-scan state proves positivity, and
absorption preserves the complete blank endpoint. -/
private lemma e3c_clear_first (M : FinTM Bool) (x w : List Bool)
    (p : Fin (w.length + 2)) (T : ℕ) (i : Fin M.k) :
    ∃ t, 0 < t ∧ t ≤ 6 * T + 7 ∧
      (∀ j < t, (e3cClearTM.tm.runFrom
        (e3cClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
          (e3cSpan (e3cLo M x T i) (e3cHi M x T i)) (bufferTape [true])
          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) j).state ≠ some (3 : Fin 4)) ∧
      e3cClearTM.tm.runFrom
        (e3cClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
          (e3cSpan (e3cLo M x T i) (e3cHi M x T i)) (bufferTape [true])
          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) t =
        e3cClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
  obtain ⟨t, _, ht, hr⟩ := e3c_track_clearable M x w p T i
  obtain ⟨a, ha, hfirst, he⟩ := e3c_first_entry e3cClearTM.tm
    (fun q : Fin 4 => q = 3) _ _ t (by
      rintro z ⟨q, hz, rfl⟩
      unfold MultiTapeTM.step
      rw [hz]
      change (controlAction 0 (some (3 : Fin 4))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all) ⟨(3 : Fin 4), rfl, rfl⟩ hr
  have hpos : 0 < a := by
    by_contra h
    have hz : a = 0 := by omega
    have hh := congrArg Cfg.state he
    have hv := congrArg (fun q : Option (Fin 4) => q.map Fin.val) hh
    norm_num [hz, e3cClearCfg] at hv
  exact ⟨a, hpos, ha.trans ht, fun j hj hh => hfirst j hj ⟨(3 : Fin 4), hh, rfl⟩, he⟩

/-- Canonical binary words represent natural numbers injectively. This is
used only to identify an already-completed whole-word comparison. -/
private lemma e3c_bits_injective : Function.Injective Nat.bits := by
  have decode (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
    induction n using Nat.binaryRec' with
    | zero => simp
    | bit b n hn ih => rw [Nat.bits_append_bit n b hn, List.foldr_cons, ih]
  intro m n h
  have he := congrArg (fun w : List Bool => w.foldr Nat.bit 0) h
  simpa only [decode] using he

/-- On a live candidate, the whole canonical binary comparison is exactly
the required exponential split equation, with the original suffix length. -/
private lemma e3c_binary_check (C c : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    (Nat.bits (C * 2 ^ (s.length + 1) ^ c) = Nat.bits (w.drop s.length).length) ↔
      s.length + C * 2 ^ (s.length + 1) ^ c = w.length := by
  rw [e3c_bits_injective.eq_iff, List.length_drop]
  omega

/-- Evaluation and its captured output both fit the same input-length-only
pre-validation envelope, including the one-past-end candidate. -/
private lemma e3c_eval_budget (M : FinTM Bool) (C c B : ℕ)
    (hM : M.ComputesFunInTime (fun s => Nat.bits (C * 2 ^ (s.length + 1) ^ c))
      (fun n => B * (n + 1) ^ (c + 1)))
    (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    M.ComputesInTime s (Nat.bits (C * 2 ^ (s.length + 1) ^ c))
      ((B * 2 ^ (c + 1)) * (w.length + 1) ^ (c + 1)) ∧
    (Nat.bits (C * 2 ^ (s.length + 1) ^ c)).length ≤
      (B * 2 ^ (c + 1)) * (w.length + 1) ^ (c + 1) := by
  have hc := (hM s).mono (e3c_candidate_envelope B (c + 1) w s hs)
  refine ⟨hc, ?_⟩
  have hout := ((computesInTime_iff _ _ _ _).mp hc).2
  simpa only [hout] using M.tm.output_length_le s
    ((B * 2 ^ (c + 1)) * (w.length + 1) ^ (c + 1))

/-- After the source's actual halt, move to the native right input boundary
without altering its output or work tapes. The initial positive move handles
both blanks correctly, including the two distinct blanks of an empty input. -/
private def e3cRightTM (M : FinTM Bool) : FinTM Bool where
  k := M.k
  State := M.State ⊕ Bool
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl q =>
        let a := M.tm.tr q inp work
        { a with state := some ((a.state.map Sum.inl).getD (.inr false)) }
      | .inr false => controlAction .pos (some (.inr true))
      | .inr true => match inp with
        | some _ => controlAction .pos (some (.inr true))
        | none => controlAction 0 none }

/-- Before the right-boundary scan, the entire source configuration is
preserved, with its halt replaced by a live administrative state. -/
private def e3cRightCfg (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Cfg M.k Bool (e3cRightTM M).State x :=
  ⟨some ((c.state.map Sum.inl).getD (.inr false)), c.inputPos,
    c.workTapes, c.workTapePos, c.output⟩

/-- The wrapper follows each genuine source transition exactly, including its
halting emission; only the successor control encoding changes. -/
private lemma e3c_right_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (hc : c.state ≠ none) :
    (e3cRightTM M).tm.step (e3cRightCfg M c) = e3cRightCfg M (M.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hc hs)
  | some q =>
    have hstate : (e3cRightCfg M c).state = some (.inl q) := by
      simp only [e3cRightCfg, hs, Option.map_some, Option.getD_some]
    simp only [MultiTapeTM.step, hstate, hs]
    rfl

/-- The right-boundary wrapper simulates exactly up to the actual source halt.
No bound is substituted for the halting transition. -/
private lemma e3c_right_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ)
    (hlive : ∀ j < t, (M.tm.runFrom c j).state ≠ none) :
    (e3cRightTM M).tm.runFrom (e3cRightCfg M c) t =
      e3cRightCfg M (M.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      e3c_right_step M _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- A rightward scan configuration carries the completed source data and
output verbatim; its physical input position is the only moving field. -/
private def e3cRightScan (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q : Option Bool) (j : ℕ) (hj : j ≤ x.length) :
    Cfg M.k Bool (e3cRightTM M).State x :=
  ⟨q.map Sum.inr, ⟨j + 1, by omega⟩, c.workTapes, c.workTapePos, c.output⟩

/-- From any interior position, the native scan reaches the right blank and
halts silently. The scan does not confuse a blank work cell with an input end.
**Proof sketch.** Induct on the number of remaining native input cells. A live
cell costs one right move; the right blank costs the final silent halt. -/
private lemma e3c_right_scan (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    ∀ r j (hj : j ≤ x.length), j + r = x.length →
      (e3cRightTM M).tm.runFrom (e3cRightScan M c (some true) j hj) (r + 1) =
        e3cRightScan M c none x.length (le_refl _) := by
  intro r
  induction r with
  | zero =>
    intro j hj he
    have hje : j = x.length := by omega
    subst j
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have hin : (e3cRightScan M c (some true) x.length (le_refl _)).inputSymbol = none := by
      simp [e3cRightScan, Cfg.inputSymbol]
    simp only [MultiTapeTM.step, e3cRightScan, Option.map_some]
    change (match (e3cRightScan M c (some true) x.length (le_refl _)).inputSymbol with
      | some _ => controlAction .pos (some (Sum.inr true))
      | none => controlAction 0 none).apply _ = _
    rw [hin, controlAction_apply, moveInputPos_zero]
    rfl
  | succ r ih =>
    intro j hj he
    have hjlt : j < x.length := by omega
    have hin : (e3cRightScan M c (some true) j hj).inputSymbol = some (x[j]'hjlt) :=
      inputSymbolInner j (by simp [e3cRightScan, Nat.add_comm]) hjlt
    have hs : (e3cRightTM M).tm.step (e3cRightScan M c (some true) j hj) =
        e3cRightScan M c (some true) (j + 1) (by omega) := by
      simp only [MultiTapeTM.step, e3cRightScan, Option.map_some]
      change (match (e3cRightScan M c (some true) j hj).inputSymbol with
        | some _ => controlAction .pos (some (Sum.inr true))
        | none => controlAction 0 none).apply _ = _
      rw [hin, controlAction_apply]
      refine Cfg.ext rfl ?_ rfl rfl rfl
      exact moveInputPos_pos_of_ne_right _ (by simp; omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (j + 1) (by omega) (by omega)

/-- The completed source enters the right scan by a positive native move.
Clamping guarantees a position at least one even on empty input.
**Proof sketch.** The mandatory positive move reaches a position of at least one.
Apply the right-scan induction to its remaining distance; neither that move
nor the scan changes the completed source work tapes or output. -/
private lemma e3c_right_finish (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (hc : c.state = none) :
    ∃ t ≤ x.length + 2,
      (e3cRightTM M).tm.runFrom (e3cRightCfg M c) t =
        e3cRightScan M c none x.length (le_refl _) := by
  let p := moveInputPos c.inputPos .pos
  have hp : 1 ≤ p.val := by
    dsimp [p, moveInputPos]
    split <;> simp_all <;> omega
  let j := p.val - 1
  have hj : j ≤ x.length := by have := p.isLt; dsimp [j]; omega
  have hs : (e3cRightTM M).tm.step (e3cRightCfg M c) =
      e3cRightScan M c (some true) j hj := by
    simp only [MultiTapeTM.step, e3cRightCfg, hc, Option.map_none, Option.getD_none]
    change (controlAction .pos (some (Sum.inr true))).apply _ = _
    rw [controlAction_apply]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    apply Fin.ext
    change p.val = j + 1
    dsimp [j]; omega
  refine ⟨1 + (x.length - j + 1), by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, show (e3cRightTM M).tm.runFrom (e3cRightCfg M c) 1 = _ from hs]
  exact e3c_right_scan M c (x.length - j) j hj (by omega)

/-- Right-boundary normalization preserves the entire completed source
configuration, not just its output. This retains the tracked cleanup witnesses.
**Proof sketch.** Choose the actual first source halt. The native right scan
then costs at most `|x|+2`; absorb only the completed run to the advertised
budget. Source absorption identifies its work tapes with those at the original
deadline, including when that deadline exceeds the actual halt. -/
private lemma e3c_right_endpoint (M : FinTM Bool) (x : List Bool) (T : ℕ)
    (hc : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    (e3cRightTM M).tm.runFrom ((e3cRightTM M).tm.initCfg x) (T + x.length + 2) =
      e3cRightScan M (M.tm.runFrom (M.tm.initCfg x) T) none x.length (le_refl _) := by
  classical
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, hc⟩
  let t := Nat.find hex
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hex hc
  have hs : c.state = none := Nat.find_spec hex
  have hcT : M.tm.runFrom (M.tm.initCfg x) T = c := by
    rw [show T = t + (T - t) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hs]
  have hi : (e3cRightTM M).tm.initCfg x = e3cRightCfg M (M.tm.initCfg x) := rfl
  have hr := e3c_right_run M (M.tm.initCfg x) t (fun j hj => Nat.find_min hex hj)
  obtain ⟨r, hrle, hfinish⟩ := e3c_right_finish M c hs
  have hrun : (e3cRightTM M).tm.runFrom ((e3cRightTM M).tm.initCfg x) (t + r) =
      e3cRightScan M c none x.length (le_refl _) := by
    rw [hi, MultiTapeTM.runFrom_add, hr]
    exact hfinish
  have hle : t + r ≤ T + x.length + 2 := by omega
  rw [show T + x.length + 2 = (t + r) + (T + x.length + 2 - (t + r)) by omega,
    MultiTapeTM.runFrom_add, hrun, MultiTapeTM.runFrom_of_halt _ (by rfl), hcT]

/-- Every timed computation can finish at the right input boundary with only
linear extra time, preserving the source's complete output. -/
private lemma e3c_right_computes (M : FinTM Bool) (x out : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x out T) :
    (e3cRightTM M).ComputesInTime x out (T + x.length + 2) ∧
      ((e3cRightTM M).tm.runFrom ((e3cRightTM M).tm.initCfg x)
        (T + x.length + 2)).inputPos.val = x.length + 1 := by
  have hc := (computesInTime_iff M x out T).mp hM
  have he := e3c_right_endpoint M x T hc.1
  constructor
  · apply (computesInTime_iff _ _ _ _).mpr
    rw [he]
    exact ⟨rfl, hc.2⟩
  · rw [he]
    rfl

/-- A captured, tracked evaluator has an actual positive first return with
its full trace banks, complete output buffer, and candidate head at the right
boundary. It emits nothing to the physical output and fixes the physical input
head at one. The entry is the canonical prepared state-word configuration by
`e3c_eval_initial`. This is a phase contract, not the complete split-search body.
**Proof sketch.** Track every source step, then normalize its virtual input
head after its actual halt. Capture this composite through its first completed
source state. Absorption equates that endpoint with the exact tracked trace at
the advertised deadline; the virtual right boundary fixes the candidate head
even for the empty word. The source deadline is never used as a native clock. -/
private lemma e3c_prepared_eval_first (M : FinTM Bool) (w s out : List Bool) (T : ℕ)
    (hM : M.ComputesInTime s out T) :
    let R := e3cRightTM (e3cTrackTM M)
    ∃ t, 0 < t ∧ t ≤ 1 + 2 * T + s.length + 2 ∧
      (∀ j < t, ((e3cEvalTM R).tm.runFrom
        (e3cEvalCfg (w := w) R (R.tm.initCfg s) true 1) j).state ≠ some (.inr ())) ∧
      (e3cEvalTM R).tm.runFrom
        (e3cEvalCfg (w := w) R (R.tm.initCfg s) true 1) t =
          e3cEvalCfg (w := w) R
            (e3cRightScan (e3cTrackTM M)
              (e3cTrackCfg M (M.tm.runFrom (M.tm.initCfg s) T)
                (e3cLo M s T) (e3cHi M s T)) none s.length (le_refl _)) false 1 := by
  dsimp only
  let R := e3cRightTM (e3cTrackTM M)
  let D := 1 + 2 * T + s.length + 2
  have htrack := e3c_track_computes M s out T hM
  have hright := (e3c_right_computes (e3cTrackTM M) s out (1 + 2 * T) htrack).1
  obtain ⟨t, ht, b, _, hh, _, hfirst, hr⟩ := e3c_eval_first R w s out D hright
  have hpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := by omega
    simp [ht0, MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg, Cfg.init] at hh
  have habs : R.tm.runFrom (R.tm.initCfg s) D = R.tm.runFrom (R.tm.initCfg s) t := by
    rw [show D = t + (D - t) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
  have hend := e3c_right_endpoint (e3cTrackTM M) s (1 + 2 * T)
    ((computesInTime_iff _ _ _ _).mp htrack).1
  rw [e3c_track_run] at hend
  refine ⟨t, hpos, ht, hfirst, ?_⟩
  rw [hr, ← habs, hend]
  rfl

/-- **Exponential choice words are exponential certificates**: every fixed-exponent
`NTIME (2^(n^c))` class is contained in the certificate-form `Complexity.NEXP`.

**Proof sketch.** The exponential analogue of `Complexity.ntime_poly_subset_NP`, same
verifier machine, different arithmetic. Let `N` decide `L` within `T n = a·2^(n^c)`
(if `a = 0` the budget is `0` and no decider exists — `Turing.NDTM.HaltsWithin` fails
on the empty choice word — so the case is vacuous). Certificate parameters: `C = a`,
degree `c`, length `Q n = a·2^((n+1)^c) ≥ T n`. The verifier language is the same
accepting-run language over the split `y = x ++ u`; `n ↦ n + Q n` is strictly
increasing (in `n` alone already), the split search over `n ≤ m` writes each candidate
`Q n` in binary — `(n+1)^c + O(log a)` bits, polynomial in `m` (the check recorded in
the `Complexity.EXP_subset_NEXP` sketch) — and **rejects explicitly when no solution
exists**. The simulation runs `|u| = Q n ≤ m` steps of the fixed machine `N` at
polynomial bookkeeping per step — polynomial in `m`, which is the whole point of
exponential padding: `V ∈ P`. Forward/backward certificate correspondence is verbatim
the polynomial case (pad with `false`-bits; truncate to the length-`T n` prefix and
absorb).

**Partial-fill appendix (epoch 3A).** The exponential split specification,
uniqueness, explicit failure, pre-validation binary-length bound, and a
native polynomial-time binary evaluator are proved in the `e3*` layer.
The existing paired loader and choice core provide the completed verifier
after split recovery; `e3_split_of_body` supplies the audited result-bearing
loop and its full polynomial time bound from concrete round contracts.
Coefficient zero is excluded for a decider and the degree-zero case is
closed through the catalog's constant-width split. The sole remaining
local admission below constructs the positive-degree native search body:
its startup, positive first-return rounds, comparison of the evaluated
binary width with the remaining input length, exact success payload, and
restoration of all scratch at rejection. The evaluator alone does not
discharge this configuration-level obligation. This theorem remains
dependent on `sorryAx`; no complete target closure is claimed.

**Partial-fill appendix (epoch 3 continuation A).** The new `e3c*` layer
proves captured virtual evaluation at actual first halt; tracked source work
with native per-tape cleanup; whole-word binary comparison with rewound
heads; exact accepting split emission; and the explicit `2^r` allowance
for one-past-end candidate evaluation. The composed evaluator phase also
retains its exact trace banks and normalizes the candidate head to the
right boundary, including for empty input. These are proved native phase
contracts. The controller that prepares the suffix, connects comparison
and cleanup, restores every administrative tape, increments the candidate,
and establishes the startup and positive first-return round contracts is
still missing. The body existential below and all six public target
admissions are unchanged. No new private helper is admitted. -/
theorem ntime_expPow_subset_NEXP (c : ℕ) : NTIME (fun n => 2 ^ n ^ c) ⊆ NEXP := by
  rintro L ⟨a, N, hN⟩
  have ha : 0 < a := e3_coefficient_pos N L a c hN
  refine ⟨a, c, e3ChoiceVerifier N a c, ?_, e3_choice_certificate N L a c hN⟩
  by_cases hc : c = 0
  · subst c
    obtain ⟨M, A, hM⟩ := e3_split_degree_zero a
    exact e3_verifier_of_split N a 0 M A 1 hM
  · obtain ⟨Eval, B, hEval⟩ := e3_exp_bits_timed a c
    -- Native frontier: consume the proved binary evaluator on the current
    -- candidate, with a length-only polynomial bound on every round state.
    -- Both the successful output and the complete restored seam are required.
    obtain ⟨body, anchor, A, r, hstart, hround⟩ :
        ∃ (body : FinTM Bool) (anchor : body.State) (A r : ℕ),
          (∀ w : List Bool, ∃ t ≤ A * (w.length + 1) ^ (r + 1),
            (∀ t' < t, (body.tm.runFrom (body.tm.initCfg w) t').state ≠ some anchor) ∧
            body.tm.runFrom (body.tm.initCfg w) t =
              Cfg.ofWords anchor (stateWord body.k [])) ∧
          (∀ (w s : List Bool), s.length ≤ w.length + 1 →
            ∃ t, 0 < t ∧ t ≤ A * (w.length + 1) ^ (r + 1) ∧
              (∀ t', 0 < t' → t' < t →
                (body.tm.runFrom (Cfg.ofWords (input := w) anchor
                  (stateWord body.k s)) t').state ≠ some anchor) ∧
              if e3SplitAccept a c w s then
                (body.tm.runFrom (Cfg.ofWords (input := w) anchor
                  (stateWord body.k s)) t).state = none ∧
                (body.tm.runFrom (Cfg.ofWords (input := w) anchor
                  (stateWord body.k s)) t).output =
                    pairEncode (w.take s.length) (w.drop s.length)
              else
                body.tm.runFrom (Cfg.ofWords (input := w) anchor
                  (stateWord body.k s)) t =
                    Cfg.ofWords anchor (stateWord body.k (e3SplitStep w s))) := by
      sorry
    obtain ⟨M, D, hM⟩ := e3_split_of_body a c body anchor A r hstart hround
    exact e3_verifier_of_split N a c M D (r + 1) hM

/-! ### A2 binary-countdown reverse host -/

/-- Fixed-width little-endian decrement and its success flag. Underflow
sets the existing cells to true and returns false, without extending the word. -/
private def a2Debit : List Bool → List Bool × Bool
  | [] => ([], false)
  | true :: bs => (false :: bs, true)
  | false :: bs => (true :: (a2Debit bs).1, (a2Debit bs).2)

/-- Number of low zero bits traversed by a borrow. -/
private def a2BorrowPos : List Bool → ℕ
  | false :: bs => a2BorrowPos bs + 1
  | _ => 0

/-- The borrow scan cannot cross more cells than the fixed width. -/
private lemma a2BorrowPos_le (u : List Bool) : a2BorrowPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [a2BorrowPos, List.length_cons] <;> omega

/-- Both successful decrements and underflow preserve the counter width. -/
private lemma a2Debit_length (u : List Bool) : (a2Debit u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [a2Debit, ih]

/-- Little-endian counter value; high zero cells contribute nothing. -/
private def a2Value : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * a2Value bs + if b then 1 else 0

/-- The fuel machine's binary word has its declared numerical value. -/
private lemma a2Value_bits (n : ℕ) : a2Value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [a2Value]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [a2Value, ih, Nat.bit_val]

/-- A successful debit reduces value by one; underflow occurs only at zero.
**Proof sketch.** A low one is cleared immediately. A low zero becomes one
while the inductive debit reduces the higher part; doubling that equation
gives the successor equation for the full word. -/
private lemma a2Debit_value (u : List Bool) :
    if (a2Debit u).2 then a2Value (a2Debit u).1 + 1 = a2Value u
    else a2Value u = 0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | true => simp [a2Debit, a2Value]
    | false =>
      cases h : (a2Debit u).2 <;>
        simp only [a2Debit, h, Bool.false_eq_true, ↓reduceIte,
          a2Value, Nat.add_zero] at ih ⊢ <;> omega

/-- The borrow returns success exactly for positive counter values. -/
private lemma a2Debit_success (u : List Bool) :
    (a2Debit u).2 = true ↔ 0 < a2Value u := by
  have h := a2Debit_value u
  cases hb : (a2Debit u).2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    simp [h]
  · simp only [hb, ↓reduceIte] at h
    simp only [true_iff]
    omega

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma a2Buffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma a2Buffer_write (pre bs : List Bool) (old new : Bool) :
    Function.update (bufferTape (pre ++ old :: bs)) (pre.length : ℤ) (some new) =
      bufferTape (pre ++ new :: bs) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold bufferTape
    by_cases hn : 0 ≤ z
    · simp only [if_pos hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
    · simp only [if_neg hn]

/-- A native binary countdown emitter. Startup copies the input and rewinds;
borrow/rewind transitions implement fixed-width subtraction. Each successful
subtraction emits one `true` at its return state; underflow halts silently.
The debit subroutine is adapted in-file from the proved private template in
`Build/Loop.lean` at the pinned base; no emitter spec contract is used. -/
private def a2DebitTM : FinTM Bool where
  k := 1
  State := Bool ⊕ (Option Bool ⊕ Bool)
  tm :=
    { q₀ := .inl false
      tr := fun q inp work => match q with
        | .inl false => match inp with
          | some b => ⟨1, fun _ => (some (some b), 1), none, some (.inl false)⟩
          | none => ⟨0, fun _ => (none, -1), none, some (.inl true)⟩
        | .inl true => match work 0 with
          | some _ => ⟨0, fun _ => (none, -1), none, some (.inl true)⟩
          | none => ⟨0, fun _ => (none, 1), none, some (.inr (.inl none))⟩
        | .inr (.inl none) => match work 0 with
          | some false => ⟨0, fun _ => (some (some true), 1), none,
              some (.inr (.inl none))⟩
          | some true => ⟨0, fun _ => (some (some false), -1), none,
              some (.inr (.inl (some true)))⟩
          | none => ⟨0, fun _ => (none, -1), none,
              some (.inr (.inl (some false)))⟩
        | .inr (.inl (some b)) => match work 0 with
          | some _ => ⟨0, fun _ => (none, -1), none, some (.inr (.inl (some b)))⟩
          | none => ⟨0, fun _ => (none, 1), none, some (.inr (.inr b))⟩
        | .inr (.inr true) =>
          ⟨0, fun _ => (none, 0), some true, some (.inr (.inl none))⟩
        | .inr (.inr false) => controlAction 0 none }

/-- A candidate on the borrow tape, with arbitrary native input-head position. -/
private def a2DebitCfg (out : List Bool) (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg a2DebitTM.k Bool a2DebitTM.State x :=
  ⟨some (.inr q), p, fun _ => bufferTape u, fun _ => z, out⟩

/-- One borrow transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma a2Borrow_step (out : List Bool) (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    a2DebitTM.tm.step (a2DebitCfg out x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => a2DebitCfg out x p (.inl (some false)) (pre.length - 1) pre
      | true :: us => a2DebitCfg out x p (.inl (some true)) (pre.length - 1) (pre ++ false :: us)
      | false :: us => a2DebitCfg out x p (.inl none) (pre.length + 1) (pre ++ true :: us) := by
  unfold MultiTapeTM.step
  change (a2DebitTM.tm.tr (.inr (.inl none)) _ _).apply _ = _
  simp only [a2DebitTM, a2DebitCfg, Cfg.workTapeSymbols, a2Buffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ (by simp [Action.apply])
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ (by simp [Action.apply])
    all_goals first
      | (funext i; exact a2Buffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The borrow phase takes one step beyond the leading false prefix, including
one blank test on underflow.
**Proof sketch.** Induct on the remaining candidate. Each false bit is set
and added to the processed prefix. A true bit or the right blank starts
rewind without changing the width. -/
private lemma a2Borrow_run (out : List Bool) (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    a2DebitTM.tm.runFrom (a2DebitCfg out x p (.inl none) pre.length (pre ++ u))
        (a2BorrowPos u + 1) =
      a2DebitCfg out x p (.inl (some (a2Debit u).2))
        ((pre.length : ℤ) + a2BorrowPos u - 1) (pre ++ (a2Debit u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [a2BorrowPos, a2Debit, MultiTapeTM.runFrom_succ_eq_step] using
      a2Borrow_step out x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | true =>
      simpa [a2BorrowPos, a2Debit, MultiTapeTM.runFrom_succ_eq_step] using
        a2Borrow_step out x p pre (true :: u)
    | false =>
      simp only [a2BorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, a2Borrow_step]
      simpa [a2Debit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma a2Borrow_rewind (out : List Bool) (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    a2DebitTM.tm.runFrom (a2DebitCfg out x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = a2DebitCfg out x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [a2DebitTM, a2DebitCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ (by simp [Action.apply])
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : a2DebitTM.tm.step
        (a2DebitCfg out x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          a2DebitCfg out x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [a2DebitTM, a2DebitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ (by simp [Action.apply])
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width decrement and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading false-prefix length. It returns live at cell zero,
retains the input head and already-emitted prefix, and emits nothing.
Width zero returns underflow after a blank test and rewind. -/
private lemma a2Borrow_correct (out : List Bool) (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * a2BorrowPos u + 2 ≤ 2 * u.length + 2 ∧
      a2DebitTM.tm.runFrom (a2DebitCfg out x p (.inl none) 0 u)
          (2 * a2BorrowPos u + 2) =
        a2DebitCfg out x p (.inr (a2Debit u).2) 0 (a2Debit u).1 := by
  refine ⟨by have := a2BorrowPos_le u; omega, ?_⟩
  have hr := a2Borrow_run out x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * a2BorrowPos u + 2 = (a2BorrowPos u + 1) + (a2BorrowPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact a2Borrow_rewind out x p (a2Debit u).1 (a2Debit u).2 _
    (by rw [a2Debit_length]; exact a2BorrowPos_le u)

/-- Exhausting the countdown emits exactly its numerical value, with arbitrary
already-emitted output retained. Each round dispatches at the actual debit
return, then emits once or halts; the budget is only an upper bound.
**Proof sketch.** Strong induction on counter value. A successful fixed-width
debit lowers the value by one and preserves width. Its return transition
emits one symbol. Underflow proves value zero and halts without emission. -/
private lemma a2_countdown (x : List Bool) (p : Fin (x.length + 2)) (n : ℕ) :
    ∀ (u out : List Bool), a2Value u = n →
    ∃ t ≤ (n + 1) * (2 * u.length + 3),
      (a2DebitTM.tm.runFrom (a2DebitCfg out x p (.inl none) 0 u) t).state = none ∧
      (a2DebitTM.tm.runFrom (a2DebitCfg out x p (.inl none) 0 u) t).output =
        out ++ List.replicate n true := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u out hv
    obtain ⟨hb, hr⟩ := a2Borrow_correct out x p u
    have hd := a2Debit_value u
    cases hs : (a2Debit u).2 with
    | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at hd
      have hn : n = 0 := hv.symm.trans hd
      rw [hn]
      refine ⟨(2 * a2BorrowPos u + 2) + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, hr]
      simp [MultiTapeTM.runFrom, MultiTapeTM.step, a2DebitCfg, a2DebitTM,
        hs, controlAction, Action.apply]
    | true =>
      simp only [hs, ↓reduceIte] at hd
      have hlt : a2Value (a2Debit u).1 < n := by omega
      obtain ⟨t, ht, hh, ho⟩ := ih _ hlt (a2Debit u).1 (out ++ [true]) rfl
      have hstep : a2DebitTM.tm.runFrom
          (a2DebitCfg out x p (.inr true) 0 (a2Debit u).1) 1 =
          a2DebitCfg (out ++ [true]) x p (.inl none) 0 (a2Debit u).1 := by
        refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
        funext i; simp [MultiTapeTM.runFrom, MultiTapeTM.step, a2DebitCfg,
          a2DebitTM, Action.apply]
      refine ⟨(2 * a2BorrowPos u + 2) + 1 + t, ?_, ?_⟩
      · rw [a2Debit_length] at ht
        have he : n = a2Value (a2Debit u).1 + 1 := by omega
        rw [he, Nat.add_mul, Nat.one_mul]
        omega
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hr, hs, hstep]
        refine ⟨hh, ?_⟩
        rw [ho, List.append_assoc]
        have he : n = a2Value (a2Debit u).1 + 1 := by omega
        simp [he, List.replicate_succ]

/-- The countdown's startup buffer, before entering the borrow states. -/
private def a2LoadCfg (x : List Bool) (q : Bool) (p : Fin (x.length + 2))
    (u : List Bool) (z : ℤ) : Cfg a2DebitTM.k Bool a2DebitTM.State x :=
  ⟨some (.inl q), p, fun _ => bufferTape u, fun _ => z, []⟩

/-- Copy one original input bit to the counter without emitting it. -/
private lemma a2_copy_step (x : List Bool) (i : ℕ) (hi : i < x.length) :
    a2DebitTM.tm.step (a2LoadCfg x false ⟨i + 1, by omega⟩ (x.take i) i) =
      a2LoadCfg x false ⟨i + 2, by omega⟩ (x.take (i + 1)) (i + 1) := by
  have hr : (a2LoadCfg x false ⟨i + 1, by omega⟩ (x.take i) i).inputSymbol =
      some x[i] := inputSymbolInner i (by simp [a2LoadCfg]; omega) hi
  unfold MultiTapeTM.step
  change (a2DebitTM.tm.tr (.inl false) _ _).apply _ = _
  dsimp only [a2DebitTM]
  rw [hr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 2
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    simp only [Action.apply, a2LoadCfg]
    rw [List.take_succ_eq_append_getElem hi, bufferTape_append,
      List.length_take_of_le (Nat.le_of_lt hi)]
  · funext j; simp [Action.apply, a2LoadCfg]

/-- Startup copies every bit from the genuine blank-tape initial configuration.
Induction follows the physical input and buffer heads in lockstep. -/
private lemma a2_copy_run (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    a2DebitTM.tm.runFrom (a2DebitTM.tm.initCfg x) i =
      a2LoadCfg x false ⟨i + 1, by omega⟩ (x.take i) i := by
  induction i with
  | zero =>
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext j z
    simp [MultiTapeTM.initCfg, Cfg.init, a2LoadCfg, bufferTape]
  | succ i ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), a2_copy_step x i (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]

/-- Rewind the copied counter from a known right-hand position; a mandatory
left move before this phase distinguishes the two blanks for empty input. -/
private lemma a2_load_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (j : ℕ) (hj : j ≤ u.length) :
    a2DebitTM.tm.runFrom (a2LoadCfg x true p u ((j : ℤ) - 1)) (j + 1) =
      a2DebitCfg [] x p (.inl none) 0 u := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [a2DebitTM, a2LoadCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply, a2DebitCfg]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : a2DebitTM.tm.step
        (a2LoadCfg x true p u ((j + 1 : ℕ) - 1)) =
          a2LoadCfg x true p u ((j : ℤ) - 1) := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [a2DebitTM, a2LoadCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, a2LoadCfg, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- Genuine startup reaches the full countdown configuration in `2|x|+2`
steps, with head zero and empty output, including empty binary input. -/
private lemma a2_start (x : List Bool) :
    a2DebitTM.tm.runFrom (a2DebitTM.tm.initCfg x) (2 * x.length + 2) =
      a2DebitCfg [] x ⟨x.length + 1, by omega⟩ (.inl none) 0 x := by
  have hc := a2_copy_run x x.length (le_refl _)
  rw [List.take_length] at hc
  have hstep : a2DebitTM.tm.step
      (a2LoadCfg x false ⟨x.length + 1, by omega⟩ x x.length) =
      a2LoadCfg x true ⟨x.length + 1, by omega⟩ x ((x.length : ℤ) - 1) := by
    have hr : (a2LoadCfg x false ⟨x.length + 1, by omega⟩ x x.length).inputSymbol = none :=
      by simp [Cfg.inputSymbol, a2LoadCfg]
    unfold MultiTapeTM.step
    change (a2DebitTM.tm.tr (.inl false) _ _).apply _ = _
    dsimp only [a2DebitTM]
    rw [hr]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, a2LoadCfg, sub_eq_add_neg]
  have henter : a2DebitTM.tm.runFrom (a2DebitTM.tm.initCfg x) (x.length + 1) =
      a2LoadCfg x true ⟨x.length + 1, by omega⟩ x ((x.length : ℤ) - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hstep]
  rw [show 2 * x.length + 2 = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, henter]
  exact a2_load_rewind x _ x x.length (le_refl _)

/-- The native emitter decodes an arbitrary fixed-width binary word. Its
complete time bound includes genuine input copying and the final underflow. -/
private lemma a2_decode_computes (x : List Bool) :
    a2DebitTM.ComputesInTime x (List.replicate (a2Value x) true)
      (2 * x.length + 2 + (a2Value x + 1) * (2 * x.length + 3)) := by
  obtain ⟨t, ht, hh, ho⟩ := a2_countdown x ⟨x.length + 1, by omega⟩ (a2Value x) x [] rfl
  have hc : a2DebitTM.ComputesInTime x (List.replicate (a2Value x) true)
      (2 * x.length + 2 + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, a2_start]
    exact ⟨hh, by simpa using ho⟩
  exact hc.mono (by omega)

/-- Binary evaluation followed by one bespoke countdown-emission phase
produces the exact exponential guess count. This is a timed native
composition, dispatching on actual completed evaluation states.
**Proof sketch.** Capture the proved evaluator's bits, rewind its completed
output, and run the native countdown on that exact intermediate word. Its
width is bounded by the evaluator's time on every input. All copying,
rewinding, decrements and the final underflow fit the displayed envelope. -/
private lemma a2_exp_scheduler (C c : ℕ) :
    ∃ (S : FinTM Bool) (B : ℕ), S.ComputesFunInTime
      (fun x => List.replicate (C * 2 ^ (x.length + 1) ^ c) true)
      (fun n => B * (n + C * 2 ^ (n + 1) ^ c + 1) ^ (c + 2)) := by
  obtain ⟨E, A, hE⟩ := e3_exp_bits_timed C c
  refine ⟨bufferedCompTM E a2DebitTM, 6 * A + 7, fun x => ?_⟩
  let R := C * 2 ^ (x.length + 1) ^ c
  let bits := Nat.bits R
  let P := (x.length + 1) ^ (c + 1)
  let m := x.length + R + 1
  have he : E.ComputesInTime x bits (A * P) := hE x
  have hlen : bits.length ≤ A * P := by
    have ho := ((computesInTime_iff _ _ _ _).mp he).2
    simpa only [ho] using E.tm.output_length_le x (A * P)
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ := bufferedComp_start E a2DebitTM x bits _ he
  let T := 2 * bits.length + 2 + (R + 1) * (2 * bits.length + 3)
  have hd : a2DebitTM.ComputesInTime bits (List.replicate R true) T := by
    simpa only [bits, a2Value_bits] using a2_decode_computes bits
  obtain ⟨tag, _, hr⟩ := bufferedSecondCfg_run E a2DebitTM
    (a2DebitTM.tm.initCfg bits) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads T
  have hc := (computesInTime_iff _ _ _ _).mp hd
  have hcomp : (bufferedCompTM E a2DebitTM).ComputesInTime x
      (List.replicate R true) (a + T) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  apply hcomp.mono
  have hp : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hm : 0 < m := by dsimp [m]; omega
  have hP : P ≤ m ^ (c + 1) := Nat.pow_le_pow_left (by dsimp [m]; omega) _
  have hR : R + 1 ≤ m := by dsimp [m]; omega
  have hprod : (R + 1) * P ≤ m ^ (c + 2) := by
    calc (R + 1) * P ≤ m * m ^ (c + 1) := Nat.mul_le_mul hR hP
         _ = m ^ (c + 2) := by rw [Nat.pow_succ]; ring
  have hsmall : a + T ≤ (6 * A + 7) * ((R + 1) * P) := by
    have hlin : a + (2 * bits.length + 2) ≤ (4 * A + 4) * P := by
      calc a + (2 * bits.length + 2) ≤ 4 * (A * P) + 4 := by omega
           _ ≤ 4 * (A * P) + 4 * P := by omega
           _ = _ := by ring
    have hround : 2 * bits.length + 3 ≤ (2 * A + 3) * P := by
      calc 2 * bits.length + 3 ≤ 2 * (A * P) + 3 * P := by omega
           _ = _ := by ring
    have hbase : (4 * A + 4) * P ≤ (R + 1) * ((4 * A + 4) * P) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos R)
    calc a + T = (a + (2 * bits.length + 2)) +
             (R + 1) * (2 * bits.length + 3) := by dsimp [T]; omega
         _ ≤ (R + 1) * ((4 * A + 4) * P) +
             (R + 1) * ((2 * A + 3) * P) :=
           Nat.add_le_add (hlin.trans hbase) (Nat.mul_le_mul_left _ hround)
         _ = _ := by ring
  exact hsmall.trans (Nat.mul_le_mul_left _ hprod)

/-- The B2 host's complete ledger fits a polynomial in the input plus the
exact exponential certificate length. The scheduler's actual first halt is
bounded, never used as a native clock. -/
private lemma a2_host_bound (Q B r A d n T : ℕ)
    (hT : T ≤ B * (n + Q + 1) ^ r) :
    2 * n + 2 + T + (n + Q + 2 + (A * (n + Q + 1) ^ d + 1)) ≤
      (B + A + 5) * (n + Q + 1) ^ (r + d + 1) := by
  let m := n + Q + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hs : T ≤ B * m ^ (r + d + 1) := hT.trans
    (Nat.mul_le_mul_left B (Nat.pow_le_pow_right hm (by omega)))
  have hv : A * m ^ d ≤ A * m ^ (r + d + 1) :=
    Nat.mul_le_mul_left A (Nat.pow_le_pow_right hm (by omega))
  have hl : 3 * n + Q + 5 ≤ 5 * m ^ (r + d + 1) := by
    have hp : m ≤ m ^ (r + d + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hm (by omega : 1 ≤ r + d + 1)
    exact (show 3 * n + Q + 5 ≤ 5 * m by dsimp [m]; omega).trans
      (Nat.mul_le_mul_left 5 hp)
  change 2 * n + 2 + T + (n + Q + 2 + (A * m ^ d + 1)) ≤ _
  calc
    _ ≤ B * m ^ (r + d + 1) + A * m ^ (r + d + 1) + 5 * m ^ (r + d + 1) := by omega
    _ = _ := by dsimp [m]; ring

/-- The integrated reverse compiler decides the certificate language on all
branches within the required envelope.
**Proof sketch.** Instantiate the binary countdown scheduler and use its
length-indexed first halt. The host contract gives all-branch termination,
exact-length extraction, and coverage at the complete phase ledger. The
certificate characterization turns its verifier outputs into language
acceptance. Enlarge to the common polynomial envelope in input plus
certificate length using halting absorption in both directions, including nonaccepting branches. -/
private lemma a2_compile (L : Language Bool) (C c : ℕ) (V : Language Bool)
    (hcert : ∀ x, x ∈ L ↔ ∃ u : List Bool,
      u.length = C * 2 ^ (x.length + 1) ^ c ∧ x ++ u ∈ V)
    (M : FinTM Bool) (A d : ℕ)
    (hM : M.DecidesInTime V (fun n => A * (n + 1) ^ d)) :
    ∃ (K r : ℕ) (N : FinNDTM Bool),
      N.DecidesInTime L (fun n => K * (n + C * 2 ^ (n + 1) ^ c + 1) ^ r) := by
  classical
  obtain ⟨S, B, hS⟩ := a2_exp_scheduler C c
  obtain ⟨τ, hτ⟩ := b2_unary_first S (fun n => List.replicate (C * 2 ^ (n + 1) ^ c) true)
    (fun n => B * (n + C * 2 ^ (n + 1) ^ c + 1) ^ (c + 2)) (fun n => by
      simpa only [List.length_replicate] using hS (List.replicate n true))
  refine ⟨B + A + 5, (c + 2) + d + 1, b2Host S M, fun x => ?_⟩
  let H := 2 * x.length + 2 + τ x.length + (x.length + C * 2 ^ (x.length + 1) ^ c + 2 +
    (A * (x.length + C * 2 ^ (x.length + 1) ^ c + 1) ^ d + 1))
  have hc := b2_host_contract S M V x (List.replicate (C * 2 ^ (x.length + 1) ^ c) true)
    (τ x.length) A d (hτ x).2.1 (hτ x).2.2 hM
  simp only [List.length_replicate] at hc
  have hhalt : (b2Host S M).tm.HaltsWithin x H := by
    intro w hw
    obtain ⟨u, _, hh, _⟩ := hc.1 w hw
    exact hh
  have hacc : x ∈ L ↔ (b2Host S M).AcceptsWithin x H := by
    rw [hcert x]
    constructor
    · rintro ⟨u, hu, hv⟩
      obtain ⟨w, hw, hh, ho⟩ := hc.2 u hu
      refine ⟨w, hw, hh, ?_⟩
      rw [ho]
      simp [MultiTapeTM.indicator, hv]
    · rintro ⟨w, hw, _, ho⟩
      obtain ⟨u, hu, _, hout⟩ := hc.1 w hw
      refine ⟨u, hu, ?_⟩
      have he := hout.symm.trans ho
      by_contra hv
      simp [MultiTapeTM.indicator, hv] at he
  have ht := a2_host_bound (C * 2 ^ (x.length + 1) ^ c) B (c + 2) A d x.length (τ x.length) (hτ x).1
  exact ⟨hhalt.mono ht, hacc.trans (acceptsWithin_iff_of_halts hhalt ht).symm⟩

/-- A fixed polynomial in `n+1` in the exponent is absorbed into `n^e`,
with a uniform multiplicative constant for lengths zero and one.
**Proof sketch.** For `n ≥ 2`, use `K ≤ 2^K ≤ n^K` and `n+1 ≤ n^2`.
For `n ≤ 1`, bound the exponent by `K·2^k` and absorb its exponential. -/
private lemma a2_exponent_bound (K k : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ, 2 ^ (K * (n + 1) ^ k) ≤ A * 2 ^ n ^ e := by
  refine ⟨2 ^ (K * 2 ^ k), K + 2 * k, fun n => ?_⟩
  by_cases hn : 2 ≤ n
  · have hK : K ≤ n ^ K :=
      (Nat.le_of_lt (Nat.lt_two_pow_self (n := K))).trans (Nat.pow_le_pow_left hn K)
    have hn' : n + 1 ≤ n ^ 2 := by
      calc n + 1 ≤ 2 * n := by omega
           _ ≤ n * n := Nat.mul_le_mul_right n hn
           _ = n ^ 2 := by ring
    have hexp : K * (n + 1) ^ k ≤ n ^ (K + 2 * k) := by
      calc K * (n + 1) ^ k ≤ n ^ K * (n ^ 2) ^ k :=
             Nat.mul_le_mul hK (Nat.pow_le_pow_left hn' k)
           _ = n ^ (K + 2 * k) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    exact (Nat.pow_le_pow_right (by omega) hexp).trans
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  · have hs : (n + 1) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left (by omega) k
    calc 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) :=
           Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left K hs)
         _ ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) :=
           Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))


/-- Every fixed polynomial in input length plus exponential certificate
length fits a fixed-exponent `NTIME` budget, with a uniform constant for all
small lengths and zero coefficients/degrees.
**Proof sketch.** Bound the sum by `(C+1)` times an exponential whose exponent
is `(n+1)^(c+1)`. Raising to the fixed polynomial degree multiplies that
exponent. The preceding absorption lemma handles all input lengths. -/
private lemma a2_envelope (C c K r : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ,
      K * (n + C * 2 ^ (n + 1) ^ c + 1) ^ r ≤ A * 2 ^ n ^ e := by
  obtain ⟨A, e, hA⟩ := a2_exponent_bound r (c + 1)
  refine ⟨K * (C + 1) ^ r * A, e, fun n => ?_⟩
  have hc : (n + 1) ^ c ≤ (n + 1) ^ (c + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have hn : n + 1 ≤ (n + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos n) (by omega : 1 ≤ c + 1)
  have hnexp : n + 1 ≤ 2 ^ (n + 1) ^ (c + 1) :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := n + 1))).trans
      (Nat.pow_le_pow_right (by omega) hn)
  have hsum : n + C * 2 ^ (n + 1) ^ c + 1 ≤
      (C + 1) * 2 ^ (n + 1) ^ (c + 1) := by
    have hm := Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega : 0 < 2) hc)
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    K * (n + C * 2 ^ (n + 1) ^ c + 1) ^ r ≤
        K * ((C + 1) * 2 ^ (n + 1) ^ (c + 1)) ^ r :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_left hsum r)
    _ = (K * (C + 1) ^ r) * 2 ^ (r * (n + 1) ^ (c + 1)) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm ((n + 1) ^ (c + 1)) r,
        Nat.mul_assoc]
    _ ≤ (K * (C + 1) ^ r) * (A * 2 ^ n ^ e) :=
      Nat.mul_le_mul_left _ (hA n)
    _ = _ := by ring

/-- Complete all-branch decoding at an exponential polynomial envelope gives
one component of the exponential `NTIME` union. Halting absorption proves
backward truncation as well as forward accepting-branch padding. -/
private lemma a2_normalize (L : Language Bool) (C c : ℕ)
    (h : ∃ (K r : ℕ) (N : FinNDTM Bool),
      N.DecidesInTime L (fun n => K * (n + C * 2 ^ (n + 1) ^ c + 1) ^ r)) :
    L ∈ ⋃ e : ℕ, NTIME fun n => 2 ^ n ^ e := by
  obtain ⟨K, r, N, hN⟩ := h
  obtain ⟨A, e, hA⟩ := a2_envelope C c K r
  refine Set.mem_iUnion.mpr ⟨e, A, N, fun x => ?_⟩
  have ht := hA x.length
  exact ⟨(hN x).1.mono ht,
    (hN x).2.trans (acceptsWithin_iff_of_halts (hN x).1 ht).symm⟩

/-- **Guess the exponential certificate**: the certificate-form `Complexity.NEXP` is
contained in the union of the fixed-exponent `NTIME (2^(n^c))` classes.

**Proof sketch.** The exponential analogue of `Complexity.NP_subset_iUnion_NTIME`.
Given `(C, c, V)` for `L` with `E n = C·2^((n+1)^c)` and `M_V` deciding `V` within
`A·(m+1)^d`: evaluate `E n` in binary (`(n+1)^c + O(log C)` bits; writing `2^((n+1)^c)`
is a `1` followed by `(n+1)^c` zeros, produced by a counter in time polynomial in
`(n+1)^c`); guess exactly `E n` bits (`δ₀`/`δ₁` write `false`/`true` on each
nondeterministic write step, deterministic countdown bookkeeping interleaved, phase
boundaries identical across branches); assemble
`x ++ u`; run the relocated, captured `M_V`; emit the verdict. Every branch is total
and the phases cost `O(E n)` guessing steps at `O((n+1)^c)`-bit countdown decrements,
plus `A·(n + E n + 1)^d` relocated verifier steps with polynomial bookkeeping — in all
at most `2^(n^e)` for a fixed `e` (say `e = c + d + 2`) once `n` exceeds a fixed
threshold, with the finitely many inputs of smaller lengths absorbed into `NTIME`'s
constant (their maximal halting time is a number; the truncation argument of
`Complexity.NTIME.mono` keeps the acceptance equivalence at the padded budget). Land
`L` in the exponent-`e` component.

**A2 completion.** `a2DebitTM` copies a binary word onto a fixed-width
counter, decrements with deterministic borrow/rewind steps, and emits once
per successful debit. `a2_countdown` proves the exact count and complete
round budget, including underflow and zero width. `a2_exp_scheduler`
composes it with the proved binary evaluator by actual captured-phase
configuration equalities. `b2_unary_first` supplies length-only first halts
and hence a branch-independent emission mask; `a2_compile` instantiates
the unchanged B2 host with exact witness extraction and coverage, native
startup and assembly, guarded captured verification, and all-branch totality.
The inherited `b2_tables_coincide` gives definitional table coincidence
outside guessing. `a2_envelope` and `a2_normalize` finish all-length budget
absorption. No admitted library contract or out-of-scope target is cited. -/
theorem NEXP_subset_iUnion_NTIME : NEXP ⊆ ⋃ c : ℕ, NTIME fun n => 2 ^ n ^ c := by
  rintro L ⟨C, c, V, hV, hcert⟩
  obtain ⟨A, d, M, hM⟩ := mem_P_iff.mp hV
  apply a2_normalize L C c
  exact a2_compile L C c V hcert M A d hM

/-- **The `NTIME` form of `NEXP`** [AB09, §2.6.2 reconciled with Exercise 2.27]:
`NEXP = ⋃ c, NTIME (2^(n^c))`. [AB09] *defines* `NEXP` by the right-hand side;
`Complexity.NEXP` is Exercise 2.27's certificate form, and this equality discharges
the reconciliation obligation recorded at its definition.

**Proof sketch.** Antisymmetry: `Complexity.NEXP_subset_iUnion_NTIME` one way;
`Set.iUnion_subset` with `Complexity.ntime_expPow_subset_NEXP` at every exponent the
other. -/
theorem NEXP_eq_iUnion_NTIME : NEXP = ⋃ c : ℕ, NTIME fun n => 2 ^ n ^ c := by
  sorry

/-- **Padding scales collapses up** [AB09, Theorem 2.22, contrapositive form]: if
`P = NP` then `EXP = NEXP`.

**Proof sketch.** `EXP ⊆ NEXP` is `Complexity.EXP_subset_NEXP`. Conversely let
`L ∈ NEXP` with `(C, c, V)` and `E n = C·2^((n+1)^c)`; the padded language is
`L_pad = {Turing.pairEncode x (List.replicate (E |x|) true) : x ∈ L}`
([AB09]'s `⟨x, 1^(2^(|x|^c))⟩`, rendered with the audited self-delimiting pairing;
`|Turing.pairEncode x pad| = 2|x| + 2 + E |x|`). **`L_pad ∈ NP`**, through the (⇐)
direction of the bounded paired interface `Complexity.mem_NP_iff_exists_length_le` —
this is the route of [AB09, Exercise 2.27], no nondeterministic machines: parameters
`C' = 1`, `c' = 1` (the `NEXP` certificate `u` of `x` has `|u| = E |x| ≤ |x'|` for the
padded input `x'`), and verifier
`V' = {Turing.pairEncode x' u : x' = Turing.pairEncode x (List.replicate (E |x|) true)
for some x, |u| = E |x|, and x ++ u ∈ V}`. Deciding `V'` in time polynomial in
`|x'| + |u|`: parse the outer pair (`Turing.pairDecode` — self-delimiting, outermost
first; a parsing-machine obligation), parse `x'` into `(x, pad)`, evaluate `E |x|` in
binary — **before any validity assumption** its bit length is at most
`(|x|+1)^c + bits(C) + 1`, polynomial in the actual input length since the parsed
`x` is a substring of the input (`E n = 0` when `C = 0`); the logarithmic-in-`|x'|`
estimate holds only *after* the padding-length check and must not be used to budget
the evaluation itself (round-1 audit, finding 1) — check `pad` is all-`true` of
exactly that length and `|u|` equals it exactly (rejecting otherwise — malformed
`x'` lies in neither `L_pad` nor any `V'`-pair, keeping the equivalence for all
inputs; both exact checks are needed, the bounded outer witness condition replaces
neither), assemble `x ++ u` (length
`≤ |x'|`), and run `V`'s polynomial decider relocated-and-captured (the shared
obligations). By `P = NP`, `L_pad ∈ P`; let `M_pad` decide it within `A·(m+1)^d`.
**`L ∈ EXP`**: on `x`, evaluate `E |x|` and write the pad (`E |x|` symbols —
exponential time, which `EXP` affords), assemble `y = Turing.pairEncode x pad` by an
emission machine, run the relocated, captured `M_pad` on `y`, and forward the verdict.
Total time is polynomial in `|y| = 2|x| + 2 + E |x|`, hence at most `2^(n^e)` for a
fixed `e` beyond a fixed threshold, small lengths absorbed into `DTIME`'s constant:
`L ∈ EXP`. -/
theorem EXP_eq_NEXP_of_P_eq_NP (h : P = NP) : EXP = NEXP := by
  sorry

/-- **Theorem 2.22** [AB09]: if `EXP ≠ NEXP` then `P ≠ NP`.

**Proof sketch.** Contraposition of `Complexity.EXP_eq_NEXP_of_P_eq_NP`. -/
theorem P_ne_NP_of_EXP_ne_NEXP (h : EXP ≠ NEXP) : P ≠ NP := by
  sorry

end Complexity
