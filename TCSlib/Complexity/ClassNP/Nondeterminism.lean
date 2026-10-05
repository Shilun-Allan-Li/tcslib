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

/-- Three concrete tape slots for the standalone copying phase. -/
private def copyTapes {α : Type} (left right clock : α) (i : Fin 3) : α :=
  if i = 0 then left else if i = 1 then right else clock

/-- A fixed copying phase, supplied with a unary split countdown on its third
tape. It copies the prefix to tape zero and the suffix to tape one, in a single
left-to-right pass, and never emits physical output. Split recovery and production
of the countdown are separate startup obligations. -/
private def choiceCopy : FinTM Bool where
  k := 3
  State := Bool
  tm :=
    { q₀ := true
      tr := fun phase inp work => match inp with
        | none => ⟨0, fun _ => (none, 0), none, none⟩
        | some bit =>
          if phase = true ∧ (work 2).isSome then
            ⟨1, copyTapes (some (some bit), 1) (none, 0) (none, 1),
              none, some true⟩
          else
            ⟨1, copyTapes (none, 0) (some (some bit), 1) (none, 0),
              none, some false⟩ }

/-- Configuration of the copying phase: completed prefix and suffix buffers,
with the countdown head equal to the number of prefix bits already copied. -/
private def choiceCopyCfg {y : List Bool} (n : ℕ) (phase : Bool)
    (left right : List Bool) (p : Fin (y.length + 2)) :
    Cfg 3 Bool Bool y where
  state := some phase
  inputPos := p
  workTapes := copyTapes (bufferTape left) (bufferTape right)
    (bufferTape (List.replicate n true))
  workTapePos := copyTapes (left.length : ℤ) (right.length : ℤ)
    (left.length : ℤ)
  output := []

/-- While the unary countdown is nonempty, one native copying step appends the
current input bit only to the prefix buffer and advances the countdown once. -/
private lemma choiceCopy_prefix_step {y : List Bool} (n : ℕ)
    (left right : List Bool) (p : Fin (y.length + 2)) (bit : Bool)
    (hlen : left.length < n)
    (hin : (choiceCopyCfg n true left right p).inputSymbol = some bit) :
    choiceCopy.tm.step (choiceCopyCfg n true left right p) =
      choiceCopyCfg n true (left ++ [bit]) right (moveInputPos p 1) := by
  have hc : (choiceCopyCfg n true left right p).workTapeSymbols 2 = some true := by
    simp [choiceCopyCfg, copyTapes, Cfg.workTapeSymbols, hlen]
  unfold MultiTapeTM.step
  change (choiceCopy.tm.tr true _ _).apply _ = _
  rw [hin]
  dsimp only [choiceCopy]
  rw [hc]
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [choiceCopyCfg])
  · funext i
    fin_cases i <;> simp [choiceCopyCfg, copyTapes, bufferTape_append]
  · funext i
    fin_cases i <;> simp [choiceCopyCfg, copyTapes]

/-- Once the countdown is exhausted, one native copying step appends the current
input bit only to the choice buffer, leaving the source-input buffer unchanged. -/
private lemma choiceCopy_suffix_step {y : List Bool} (n : ℕ) (phase : Bool)
    (left right : List Bool) (p : Fin (y.length + 2)) (bit : Bool)
    (hlen : left.length = n)
    (hin : (choiceCopyCfg n phase left right p).inputSymbol = some bit) :
    choiceCopy.tm.step (choiceCopyCfg n phase left right p) =
      choiceCopyCfg n false left (right ++ [bit]) (moveInputPos p 1) := by
  have hc : (choiceCopyCfg n phase left right p).workTapeSymbols 2 = none := by
    simp [choiceCopyCfg, copyTapes, Cfg.workTapeSymbols, hlen]
  unfold MultiTapeTM.step
  change (choiceCopy.tm.tr phase _ _).apply _ = _
  rw [hin]
  dsimp only [choiceCopy]
  rw [hc]
  simp only [Option.isSome_none, Bool.false_eq_true, and_false, if_false]
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [choiceCopyCfg])
  · funext i
    fin_cases i <;> simp [choiceCopyCfg, copyTapes, bufferTape_append]
  · funext i
    fin_cases i <;> simp [choiceCopyCfg, copyTapes]

/-- Starting with the unary prefix length and blank data buffers, copying the
first `t ≤ |x|` input symbols takes exactly `t` native transitions.

**Proof sketch.** Induct on `t`. The native input head reads the next bit of
`x`, and the unary countdown still has a bit. Apply the prefix-copy step and
the list-prefix append identity; the native head advances without clamping
because the next position is still within the input window. -/
private lemma choiceCopy_prefix_run (x u : List Bool) (t : ℕ) (ht : t ≤ x.length) :
    choiceCopy.tm.runFrom
      (choiceCopyCfg (y := x ++ u) x.length true [] [] 1) t =
        choiceCopyCfg x.length true (x.take t) []
          ⟨t + 1, by simp only [List.length_append]; omega⟩ := by
  induction t with
  | zero => simp [MultiTapeTM.runFrom_zero, List.take_zero]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hp : (x.take t).length = t := List.length_take_of_le (by omega)
    have hin : (choiceCopyCfg (y := x ++ u) x.length true (x.take t) []
        ⟨t + 1, by simp only [List.length_append]; omega⟩).inputSymbol = some x[t] := by
      rw [inputSymbolInner t (by simp only [choiceCopyCfg, Nat.add_comm])
        (by simp only [List.length_append]; omega)]
      rw [List.getElem_append_left (by omega)]
    rw [choiceCopy_prefix_step _ _ _ _ _ (by rw [hp]; omega) hin,
      ← List.take_succ_eq_append_getElem (by omega)]
    congr 1
    apply Fin.ext
    rw [show (1 : SignType) = .pos from rfl,
      moveInputPos_pos_of_ne_right _ (by simp only [List.length_append]; omega)]

/-- After copying all of `x`, each additional suffix bit costs one native
transition. The copied source input and its completed countdown remain unchanged.
In particular, empty prefixes and empty suffixes are included.

**Proof sketch.** The prefix-run lemma supplies the initial suffix configuration.
Induct on the number of suffix bits: the countdown stays at its right blank,
and the input read lies in the suffix of the concatenation. The suffix-copy
step appends precisely that next bit and advances the native input head. -/
private lemma choiceCopy_suffix_run (x u : List Bool) (t : ℕ) (ht : t ≤ u.length) :
    ∃ phase : Bool, choiceCopy.tm.runFrom
      (choiceCopyCfg (y := x ++ u) x.length true [] [] 1) (x.length + t) =
        choiceCopyCfg x.length phase x (u.take t)
          ⟨x.length + t + 1, by simp only [List.length_append]; omega⟩ := by
  induction t with
  | zero =>
    refine ⟨true, ?_⟩
    simpa only [Nat.add_zero, List.take_zero, List.take_length] using
      choiceCopy_prefix_run x u x.length (le_refl _)
  | succ t ih =>
    obtain ⟨phase, hr⟩ := ih (by omega)
    refine ⟨false, ?_⟩
    conv_lhs => rw [Nat.add_succ x.length t, MultiTapeTM.runFrom_succ_eq_step', hr]
    have hin : (choiceCopyCfg (y := x ++ u) x.length phase x (u.take t)
        ⟨x.length + t + 1, by simp only [List.length_append]; omega⟩).inputSymbol =
        some u[t] := by
      rw [inputSymbolInner (x.length + t)
        (by simp only [choiceCopyCfg, Nat.add_comm])
        (by simp only [List.length_append]; omega)]
      rw [List.getElem_append_right (by omega)]
      simp
    rw [choiceCopy_suffix_step _ _ _ _ _ _ rfl hin,
      ← List.take_succ_eq_append_getElem (by omega)]
    congr 1
    apply Fin.ext
    rw [show (1 : SignType) = .pos from rfl,
      moveInputPos_pos_of_ne_right _ (by simp only [List.length_append]; omega)]
    change x.length + t + 1 + 1 = x.length + (t + 1) + 1
    omega

/-- The entire copying pass takes `|x++u|+1` transitions, including its final
boundary check. Both data buffers are exact, their heads are at their right
blanks, the countdown is preserved, and physical output is empty. This contract
still requires the unary split length to be present initially.

**Proof sketch.** Instantiate the suffix-run lemma at the complete suffix length.
The physical input head then reads the right blank. The next transition halts
without writing, moving work heads, or emitting, preserving the two full buffers. -/
private lemma choiceCopy_timed (x u : List Bool) :
    let result := choiceCopy.tm.runFrom
      (choiceCopyCfg (y := x ++ u) x.length true [] [] 1) ((x ++ u).length + 1)
    result.state = none ∧
      result.workTapes = copyTapes (bufferTape x) (bufferTape u)
        (bufferTape (List.replicate x.length true)) ∧
      result.workTapePos = copyTapes (x.length : ℤ) (u.length : ℤ) (x.length : ℤ) ∧
      result.output = [] := by
  obtain ⟨phase, hr⟩ := choiceCopy_suffix_run x u u.length (le_refl _)
  simp only [List.take_length] at hr
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step']
  have hr' : choiceCopy.tm.runFrom
      (choiceCopyCfg (y := x ++ u) x.length true [] [] 1) (x ++ u).length =
        choiceCopyCfg x.length phase x u
          ⟨x.length + u.length + 1, by simp only [List.length_append]; omega⟩ := by
    simpa only [List.length_append] using hr
  rw [hr']
  have hin : (choiceCopyCfg (y := x ++ u) x.length phase x u
      ⟨x.length + u.length + 1, by simp only [List.length_append]; omega⟩).inputSymbol =
      none := by
    have h := inputSymbol_at (choiceCopyCfg (y := x ++ u) x.length phase x u
      ⟨x.length + u.length + 1, by simp only [List.length_append]; omega⟩)
      (x ++ u).length (le_refl _) (by simp [choiceCopyCfg])
    simpa using h
  unfold MultiTapeTM.step
  change ((choiceCopy.tm.tr phase _ _).apply _).state = none ∧ _
  rw [hin]
  simp [choiceCopy, choiceCopyCfg]

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
absorb). -/
theorem ntime_expPow_subset_NEXP (c : ℕ) : NTIME (fun n => 2 ^ n ^ c) ⊆ NEXP := by
  sorry

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
`L` in the exponent-`e` component. -/
theorem NEXP_subset_iUnion_NTIME : NEXP ⊆ ⋃ c : ℕ, NTIME fun n => 2 ^ n ^ c := by
  sorry

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
