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
with `Complexity.succ_pow_le`), landing `L` in the degree-`e` component. -/
theorem NP_subset_iUnion_NTIME : NP ⊆ ⋃ c : ℕ, NTIME fun n => n ^ c + 1 := by
  sorry

/-- **Theorem 2.6** [AB09]: `NP = ⋃ c, NTIME (n^c + 1)` — the verifier-certificate
definition and the nondeterministic-machine definition of `NP` coincide (with the
`+ 1` padding of the union recorded in the deviations list).

**Proof sketch.** Antisymmetry: `Complexity.NP_subset_iUnion_NTIME` one way;
`Set.iUnion_subset` with `Complexity.ntime_poly_subset_NP` at every degree the
other. -/
theorem NP_eq_iUnion_NTIME : NP = ⋃ c : ℕ, NTIME fun n => n ^ c + 1 := by
  sorry

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
