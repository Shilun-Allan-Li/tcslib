/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.RecordTable
import TCSlib.Complexity.TuringMachine.Build.StepClock

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the windowed runner (host H3)

The **windowed runner** runs a fixed binary machine on the configuration record of a windowed
configuration (`Build/CfgRecord.lean`), round by round: test the record for a halted state,
else apply one step of the machine, else report that the step leaves the window. It is host H3
of the registry (`machine-library-design.md` §14), on B6's window route (§16b item 3). Its
named consumers are `Complexity.space_hierarchy` (through `Turing.exists_configWindowRunnerTM`,
`SpaceComplexity/WindowClock.lean`), and later the windowed simulations of Savitch's theorem
and of `NL = coNL`.

**Status: statement gate passed 2026-10-14** (round 1, 0/0/5;
`audits/b6-hosts-statements-findings.md`). The specification `Turing.windowRun` and all its
lemmas are proved. **Fill update (B6-F2):** the loop is proved; the runner is proved modulo
`Turing.exists_stepClockTMVia`.

## Design

* **A pure specification first.** `Turing.windowRun M s upd N c τ` is the semantic windowed
  run: at most `N` rounds, three exits (`Turing.WindowExit`). The machine contracts are stated
  against it, and its lemmas carry the arithmetic: the forward halting direction, the full
  characterization of the exits, the tag invariant (no output word is buffered), the
  independence of a stop from the clock, and the sanity pair on the last transition.
* **The tag is generic**: any `T` with `upd : T → Option Bool → T` and `upd τ none = τ`, the
  record step's own hypothesis. The output summary's `Fin 3` instance is `Turing.summaryTag`
  (`SpaceComplexity/ConfigGraph.lean`).
* **Clock and loop are separate.** `Turing.exists_windowLoopTM` is the unclocked round loop.
  `Turing.exists_windowRunnerTM` is that loop under the step clock of `Build/StepClock.lean`,
  with the clock word supplied by the consumer. The configuration-count form, which builds its
  own clock, is in `SpaceComplexity/WindowClock.lean`, so that this module imports nothing
  from `SpaceComplexity`.
* The contracts are existential modules, in the style of `Turing.exists_recordStepTM`; the
  named witnesses come at fill time.

## Main definitions

* `Turing.WindowExit` — the three exits: halted, left the window, clock exhausted.
* `Turing.windowRun` — the semantic windowed run.

## Main results

* `Turing.windowRun_halted_of_run`, `Turing.windowRun_spec`, `Turing.windowRun_tag`,
  `Turing.windowRun_stop_unique` — the specification's lemmas (proved).
* `Turing.windowRun_exhausted_of_live`, `Turing.windowRun_halts_on_last_transition` — the
  sanity pair: the surplus round is needed, and it suffices (proved).
* `Turing.exists_windowLoopTM`, `Turing.exists_windowRunnerTM` — the round loop and the
  step-clocked runner (**B6-F2:** proved; the runner modulo the step clock).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4: configurations; §4.1.3, Theorem 4.8,
  whose proof the book assigns to Exercise 4.1: the diagonalizer simulates within the space
  bound and stops by a configuration count. The record, window and clock constructions here
  are the repository's refinement of that argument.)
-/

namespace Turing

/-! ### The specification -/

/-- **The three exits of a windowed run**: the simulated machine halted inside the window;
its next step leaves the window; or the clock ran out. -/
inductive WindowExit where
  /-- the simulated machine has halted -/
  | halted
  /-- the next simulated step leaves the window -/
  | left
  /-- the clock is exhausted -/
  | exhausted
deriving DecidableEq

open Classical in
/-- **The semantic windowed run** (host H3's specification). `windowRun M s upd N c τ` runs
at most `N` rounds of the fixed machine `M` from `c` with tag `τ`. Each round first tests
the configuration: if it is halted, the run stops with exit `halted`; otherwise, if the next
configuration lies in the radius-`s` window, it steps and updates the tag by `upd` with the
step's emission; otherwise it stops with exit `left`, unchanged. After `N` rounds without a
stop it reports `exhausted` with the configuration reached. A halt on the `N`-th transition is
therefore recognized only with an `N + 1`-st round: the strict surplus of the RD-3 gate's
check 4. [AB09, §4.1.3, Theorem 4.8 with Exercise 4.1, and §4.1.1, Claim 4.4: the
diagonalizer simulates within the space bound and stops by a configuration count] -/
noncomputable def windowRun {k : ℕ} {Q T : Type} {x : List Bool} (M : MultiTapeTM k Bool Q)
    (s : ℕ) (upd : T → Option Bool → T) :
    ℕ → Cfg k Bool Q x → T → WindowExit × Cfg k Bool Q x × T
  | 0, c, τ => (.exhausted, c, τ)
  | N + 1, c, τ =>
    if c.state = none then (.halted, c, τ)
    else if (M.step c).InWindow s then
      windowRun M s upd N (M.step c) (upd τ (M.outputSymbol c))
    else (.left, c, τ)

/-- **A run inside the window halts in the windowed run.** Let the tag `σ` of output words be
compatible with `upd` (`σ (u ++ b) = upd (σ u) b`). If `M` from `c` has halted by time `t`,
every configuration up to `t` lies in the window, and `t < N`, then `N` rounds from `c` with
tag `σ c.output` stop with exit `halted`, at the configuration of time `t`, with its output's
tag. This is the direction `Complexity.space_hierarchy`'s contradiction uses. [AB09,
Theorem 4.8 with Exercise 4.1]

**Proof sketch.** Induct on `N`. A halted `c` stops at once, and the run from it is frozen. A
live `c` has `t ≥ 1`, its successor is in the window (time `1`), and the induction hypothesis
applies to the successor at `t - 1`; the tag update is `σ` of the appended output
(`Turing.MultiTapeTM.step_output`). -/
theorem windowRun_halted_of_run {k : ℕ} {Q T : Type} {x : List Bool}
    (M : MultiTapeTM k Bool Q) (s : ℕ) (upd : T → Option Bool → T) (σ : List Bool → T)
    (hσ : ∀ u b, σ (u ++ b.toList) = upd (σ u) b) :
    ∀ (N t : ℕ) (c : Cfg k Bool Q x), t < N → (M.runFrom c t).state = none →
      (∀ u ≤ t, (M.runFrom c u).InWindow s) →
      windowRun M s upd N c (σ c.output) =
        (.halted, M.runFrom c t, σ (M.runFrom c t).output) := by
  intro N
  induction N with
  | zero => intro t c ht; omega
  | succ N ih =>
    intro t c ht hhalt hwin
    by_cases hc : c.state = none
    · rw [MultiTapeTM.runFrom_of_halt c hc]
      simp only [windowRun, if_pos hc]
    · cases t with
      | zero => exact absurd (by simpa using hhalt) hc
      | succ t =>
        have hrun : M.runFrom c (t + 1) = M.runFrom (M.step c) t :=
          MultiTapeTM.runFrom_succ_eq_step
        have hstep : (M.step c).InWindow s := by
          simpa [MultiTapeTM.runFrom_succ_eq_step] using hwin 1 (by omega)
        have key := ih t (M.step c) (by omega) (by rw [← hrun]; exact hhalt)
          (fun u hu => by
            have h := hwin (u + 1) (by omega)
            rwa [MultiTapeTM.runFrom_succ_eq_step] at h)
        rw [hrun]
        simp only [windowRun, if_neg hc, if_pos hstep]
        rw [← hσ, ← MultiTapeTM.step_output]
        exact key

/-- **What a windowed run reports** (the full characterization of the three exits). From a
windowed `c`, `N` rounds stop at the configuration of some time `r ≤ N` of `M`'s run, with
every configuration up to `r` in the window and every one before `r` live, and:
* exit `halted` means `r < N` and the configuration at `r` is halted;
* exit `left` means `r < N`, the configuration at `r` is live, and the one at `r + 1` is
  outside the window;
* exit `exhausted` means `r = N`.

**Proof sketch.** Induct on `N`, following the three branches of a round; a step shifts every
time index by one (`Turing.MultiTapeTM.runFrom_succ_eq_step`). -/
theorem windowRun_spec {k : ℕ} {Q T : Type} {x : List Bool}
    (M : MultiTapeTM k Bool Q) (s : ℕ) (upd : T → Option Bool → T) :
    ∀ (N : ℕ) (c : Cfg k Bool Q x) (τ : T), c.InWindow s →
      ∃ r ≤ N, (windowRun M s upd N c τ).2.1 = M.runFrom c r ∧
        (∀ u ≤ r, (M.runFrom c u).InWindow s) ∧
        (∀ u < r, (M.runFrom c u).state ≠ none) ∧
        ((windowRun M s upd N c τ).1 = .halted → r < N ∧ (M.runFrom c r).state = none) ∧
        ((windowRun M s upd N c τ).1 = .left → r < N ∧ (M.runFrom c r).state ≠ none ∧
          ¬(M.runFrom c (r + 1)).InWindow s) ∧
        ((windowRun M s upd N c τ).1 = .exhausted → r = N) := by
  intro N
  induction N with
  | zero =>
    intro c τ hc
    refine ⟨0, le_rfl, by simp [windowRun], ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [show u = 0 by omega, MultiTapeTM.runFrom_zero]
      exact hc
    · intro u hu
      omega
    · simp [windowRun]
    · simp [windowRun]
    · intro _
      rfl
  | succ N ih =>
    intro c τ hc
    by_cases hst : c.state = none
    · refine ⟨0, by omega, by simp [windowRun, hst], ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rw [show u = 0 by omega, MultiTapeTM.runFrom_zero]
        exact hc
      · intro u hu
        omega
      · intro _
        exact ⟨by omega, by simpa using hst⟩
      · simp [windowRun, hst]
      · simp [windowRun, hst]
    · by_cases hw : (M.step c).InWindow s
      · have heq : windowRun M s upd (N + 1) c τ =
            windowRun M s upd N (M.step c) (upd τ (M.outputSymbol c)) := by
          simp only [windowRun, if_neg hst, if_pos hw]
        obtain ⟨r, hr, h1, h2, h3, h4, h5, h6⟩ := ih (M.step c) (upd τ (M.outputSymbol c)) hw
        rw [heq]
        refine ⟨r + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [h1, MultiTapeTM.runFrom_succ_eq_step]
        · intro u hu
          cases u with
          | zero => simpa using hc
          | succ u =>
            rw [MultiTapeTM.runFrom_succ_eq_step]
            exact h2 u (by omega)
        · intro u hu
          cases u with
          | zero => simpa using hst
          | succ u =>
            rw [MultiTapeTM.runFrom_succ_eq_step]
            exact h3 u (by omega)
        · intro h
          obtain ⟨a, b⟩ := h4 h
          exact ⟨by omega, by rw [MultiTapeTM.runFrom_succ_eq_step]; exact b⟩
        · intro h
          obtain ⟨a, b, e⟩ := h5 h
          refine ⟨by omega, by rw [MultiTapeTM.runFrom_succ_eq_step]; exact b, ?_⟩
          rw [MultiTapeTM.runFrom_succ_eq_step]
          exact e
        · intro h
          have := h6 h
          omega
      · refine ⟨0, by omega, by simp [windowRun, hst, hw], ?_, ?_, ?_, ?_, ?_⟩
        · intro u hu
          rw [show u = 0 by omega, MultiTapeTM.runFrom_zero]
          exact hc
        · intro u hu
          omega
        · simp [windowRun, hst, hw]
        · intro _
          refine ⟨by omega, by simpa using hst, ?_⟩
          simpa [MultiTapeTM.runFrom_succ_eq_step] using hw
        · simp [windowRun, hst, hw]

/-- **The tag tracks the output.** If the tag `σ` of output words is compatible with `upd`
and the run starts with the tag of `c`'s output, the reported tag is the tag of the reported
configuration's output, at every exit. No output word is buffered (design §12.8a, W1).

**Proof sketch.** Induct on `N`; at a step the new tag is `σ` of the appended output. -/
theorem windowRun_tag {k : ℕ} {Q T : Type} {x : List Bool}
    (M : MultiTapeTM k Bool Q) (s : ℕ) (upd : T → Option Bool → T) (σ : List Bool → T)
    (hσ : ∀ u b, σ (u ++ b.toList) = upd (σ u) b) :
    ∀ (N : ℕ) (c : Cfg k Bool Q x),
      (windowRun M s upd N c (σ c.output)).2.2 =
        σ (windowRun M s upd N c (σ c.output)).2.1.output := by
  intro N
  induction N with
  | zero => intro c; simp [windowRun]
  | succ N ih =>
    intro c
    by_cases hst : c.state = none
    · simp [windowRun, hst]
    · by_cases hw : (M.step c).InWindow s
      · have heq : windowRun M s upd (N + 1) c (σ c.output) =
            windowRun M s upd N (M.step c) (σ (M.step c).output) := by
          simp only [windowRun, if_neg hst, if_pos hw]
          rw [← hσ, ← MultiTapeTM.step_output]
        rw [heq]
        exact ih (M.step c)
      · simp [windowRun, hst, hw]

/-- **A stop does not depend on the clock.** If two windowed runs from the same start stop
(exit `halted` or `left`), they report the same result, whatever their round budgets.

**Proof sketch.** Induct on the first budget; both runs take the same branch of every round
until one stops. -/
theorem windowRun_stop_unique {k : ℕ} {Q T : Type} {x : List Bool}
    (M : MultiTapeTM k Bool Q) (s : ℕ) (upd : T → Option Bool → T) :
    ∀ (N N' : ℕ) (c : Cfg k Bool Q x) (τ : T),
      (windowRun M s upd N c τ).1 ≠ .exhausted → (windowRun M s upd N' c τ).1 ≠ .exhausted →
      windowRun M s upd N c τ = windowRun M s upd N' c τ := by
  intro N
  induction N with
  | zero => intro N' c τ h; simp [windowRun] at h
  | succ N ih =>
    intro N' c τ h h'
    cases N' with
    | zero => simp [windowRun] at h'
    | succ N' =>
      by_cases hst : c.state = none
      · simp only [windowRun, if_pos hst]
      · by_cases hw : (M.step c).InWindow s
        · simp only [windowRun, if_neg hst, if_pos hw] at h h' ⊢
          exact ih N' _ _ h h'
        · simp only [windowRun, if_neg hst, if_neg hw]

/-- **Sanity: without the surplus round the clock runs out.** If the first `N`
configurations are live and the first `N + 1` lie in the window, then `N` rounds report
`exhausted` with the configuration of time `N`, **even when that configuration is halted**.
So a halt on the last permitted transition needs one more round: the reason the clock value
must strictly exceed the configuration count (the RD-3 gate's check 4, "the extra halt-test
round").

**Proof sketch.** Induct on `N`; every round steps. -/
theorem windowRun_exhausted_of_live {k : ℕ} {Q T : Type} {x : List Bool}
    (M : MultiTapeTM k Bool Q) (s : ℕ) (upd : T → Option Bool → T) :
    ∀ (N : ℕ) (c : Cfg k Bool Q x) (τ : T), (∀ u < N, (M.runFrom c u).state ≠ none) →
      (∀ u ≤ N, (M.runFrom c u).InWindow s) →
      (windowRun M s upd N c τ).1 = .exhausted ∧
        (windowRun M s upd N c τ).2.1 = M.runFrom c N := by
  intro N
  induction N with
  | zero => intro c τ _ _; simp [windowRun]
  | succ N ih =>
    intro c τ hlive hwin
    have hst : c.state ≠ none := by simpa using hlive 0 (by omega)
    have hw : (M.step c).InWindow s := by
      simpa [MultiTapeTM.runFrom_succ_eq_step] using hwin 1 (by omega)
    have heq : windowRun M s upd (N + 1) c τ =
        windowRun M s upd N (M.step c) (upd τ (M.outputSymbol c)) := by
      simp only [windowRun, if_neg hst, if_pos hw]
    rw [heq, MultiTapeTM.runFrom_succ_eq_step]
    refine ih (M.step c) _ (fun u hu => ?_) (fun u hu => ?_)
    · rw [← MultiTapeTM.runFrom_succ_eq_step]
      exact hlive (u + 1) (by omega)
    · rw [← MultiTapeTM.runFrom_succ_eq_step]
      exact hwin (u + 1) (by omega)

/-- **Sanity: a halt on the final transition that emits the deciding bit** (the RD-3 gate's
suggested obligation for H3). If `M` from `c` halts at time `t + 1` by a transition that
emits `b`, and the run stays in the window, then `t + 2` rounds (the minimal surplus) report
exit `halted` at the halted configuration with the tag of the output **including `b`**.

**Proof sketch.** `Turing.windowRun_halted_of_run` at time `t + 1`, and the last step appends
`b` to the output (`Turing.MultiTapeTM.step_output`). -/
theorem windowRun_halts_on_last_transition {k : ℕ} {Q T : Type} {x : List Bool}
    (M : MultiTapeTM k Bool Q) (s : ℕ) (upd : T → Option Bool → T) (σ : List Bool → T)
    (hσ : ∀ u b, σ (u ++ b.toList) = upd (σ u) b) (t : ℕ) (c : Cfg k Bool Q x) (b : Bool)
    (hhalt : (M.runFrom c (t + 1)).state = none)
    (hemit : M.outputSymbol (M.runFrom c t) = some b)
    (hwin : ∀ u ≤ t + 1, (M.runFrom c u).InWindow s) :
    windowRun M s upd (t + 2) c (σ c.output) =
      (.halted, M.runFrom c (t + 1), σ ((M.runFrom c t).output ++ [b])) := by
  rw [windowRun_halted_of_run M s upd σ hσ (t + 2) (t + 1) c (by omega) hhalt hwin,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, hemit]
  rfl

/-! ### The machines -/

/-! ### Windowed-runner fill (B6-F2): the loop's phase host -/

/-- The loop's four phases: the round anchor, the halted-state test, the record
step, and the stationary stops. -/
private inductive wl_Phase where
  /-- the round anchor: one stationary dispatch step into the test -/
  | anchor
  /-- the halted-state test, `Turing.exists_recordTestTM` on tape `0` -/
  | test
  /-- the record step, `Turing.exists_recordStepTM` on the whole bank -/
  | step
  /-- the three stationary stops -/
  | stop
  deriving DecidableEq, Fintype

/-- The phase controls: the anchor's one state, the test row's and the step row's
controls, and the stops, indexed by the exit they report. -/
private def wl_Ctrl (Pt Ps : Type) : wl_Phase → Type
  | .anchor => Unit
  | .test => Pt
  | .step => Ps
  | .stop => WindowExit

/-- The phase controls are finite. `Turing.WindowExit` has no public `Fintype`
instance, so its three values are listed here, locally. -/
private instance wl_Ctrl_fintype (Pt Ps : Type) [Fintype Pt] [Fintype Ps] :
    (i : wl_Phase) → Fintype (wl_Ctrl Pt Ps i)
  | .anchor => inferInstanceAs (Fintype Unit)
  | .test => inferInstanceAs (Fintype Pt)
  | .step => inferInstanceAs (Fintype Ps)
  | .stop => show Fintype WindowExit from
    ⟨{.halted, .left, .exhausted}, fun e => by cases e <;> simp⟩

/-- The phase controls have decidable equality. -/
private instance wl_Ctrl_decidableEq (Pt Ps : Type) [DecidableEq Pt] [DecidableEq Ps] :
    (i : wl_Phase) → DecidableEq (wl_Ctrl Pt Ps i)
  | .anchor => inferInstanceAs (DecidableEq Unit)
  | .test => inferInstanceAs (DecidableEq Pt)
  | .step => inferInstanceAs (DecidableEq Ps)
  | .stop => inferInstanceAs (DecidableEq WindowExit)

/-- The record tape `0` as a one-tape bank, for the test row's R1 embedding. -/
private def wl_recordTape (K : ℕ) : Fin 1 ↪ Fin (K + 1) :=
  ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

/-- The phase machines: a stationary anchor (always redirected), the test row on
tape `0` by R1, the step row on the whole bank, and stationary stops. -/
private def wl_rows {K : ℕ} {Q T Pt Ps : Type} (Rt : MultiTapeTM 1 (RecSym Q T) Pt)
    (Rs : MultiTapeTM (K + 1) (RecSym Q T) Ps) :
    (i : wl_Phase) → MultiTapeTM (K + 1) (RecSym Q T) (wl_Ctrl Pt Ps i)
  | .anchor => ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, some ()⟩⟩
  | .test => embedEmitTM (wl_recordTape K) Rt
  | .step => Rs
  | .stop => ⟨WindowExit.exhausted, fun e _ _ => ⟨0, fun _ => (none, 0), none, some e⟩⟩

/-- The redirect table: the anchor enters the test; the test's `yes` (halted)
stops with `halted` and its `no` enters the step; the step's `yes` returns to the anchor and its
`no` (the next configuration leaves the window) stops with `left`. Each redirect is one
stationary dispatch step (`Turing.phaseHostTM`), so every round has positive duration. -/
private def wl_red {Pt Ps : Type} [DecidableEq Pt] [DecidableEq Ps] (te ty tn : Pt)
    (se sy sn : Ps) : (i : wl_Phase) → wl_Ctrl Pt Ps i → Option (Σ i, wl_Ctrl Pt Ps i)
  | .anchor, _ => some ⟨.test, te⟩
  | .test, q =>
    if q = ty then some ⟨.stop, (WindowExit.halted : WindowExit)⟩
    else if q = tn then some ⟨.step, se⟩ else none
  | .step, q =>
    if q = sy then some ⟨.anchor, ()⟩
    else if q = sn then some ⟨.stop, (WindowExit.left : WindowExit)⟩ else none
  | .stop, _ => none

/-- **H3's round loop**: the phase host over the two record rows, entered at the
anchor. -/
private def wl_loopTM {K : ℕ} {Q T Pt Ps : Type} [DecidableEq Pt] [DecidableEq Ps]
    (Rt : MultiTapeTM 1 (RecSym Q T) Pt) (Rs : MultiTapeTM (K + 1) (RecSym Q T) Ps)
    (te ty tn : Pt) (se sy sn : Ps) : MultiTapeTM (K + 1) (RecSym Q T) (Σ i, wl_Ctrl Pt Ps i) :=
  phaseHostTM (wl_rows Rt Rs) ⟨.anchor, ()⟩ (wl_red te ty tn se sy sn)

/-- Change only the control type and control value of a configuration. -/
private def wl_at {k : ℕ} {Γ P Q : Type} {x : List Γ}
    (d : Cfg k Γ P x) (q : Q) : Cfg k Γ Q x :=
  ⟨some q, d.inputPos, d.workTapes, d.workTapePos, d.output⟩

/-- The record interval is replaced, with its frame and all heads kept. -/
private def wl_patch {K : ℕ} {Γ P : Type} {x : List Γ}
    (d : Cfg (K + 1) Γ P x) (q : P) (fs : List (List Γ)) : Cfg (K + 1) Γ P x :=
  { d with
    state := some q
    workTapes := fun j p =>
      if j = 0 ∧ d.workTapePos 0 ≤ p ∧
          p < d.workTapePos 0 + ((joinFields fs).length : ℤ)
        then fieldsTape fs (p - d.workTapePos 0) else d.workTapes j p }

/-- Patching a record already present changes only the control. -/
private theorem wl_patch_self {K : ℕ} {Γ P : Type} {x : List Γ}
    (d : Cfg (K + 1) Γ P x) (q : P) (fs : List (List Γ)) (hr : RecordAt d 0 fs) :
    wl_patch d q fs = wl_at d q := by
  apply Cfg.ext <;> try rfl
  funext j p
  dsimp only [wl_patch, wl_at]
  split_ifs with h
  · rcases h with ⟨rfl, hlo, hhi⟩
    have hh := hr (p - d.workTapePos 0) (by omega) (by omega)
    simpa only [add_sub_cancel] using hh.symm
  · rfl

/-- Successive patches of equal-width records collapse to the last patch. -/
private theorem wl_patch_patch {K : ℕ} {Γ P : Type} {x : List Γ}
    (d : Cfg (K + 1) Γ P x) (q q' : P) (fs gs : List (List Γ))
    (hlen : (joinFields fs).length = (joinFields gs).length) :
    wl_patch (wl_patch d q fs) q' gs = wl_patch d q' gs := by
  apply Cfg.ext <;> try rfl
  funext j p
  simp only [wl_patch, hlen]
  split_ifs <;> rfl

/-- A replacement of the same width keeps the two blank delimiters, so the new record
is again at the same head. Proof sketch: use the patch in the interior, the old record at
the two delimiters, and the definition of the public field layout there. -/
private theorem wl_patch_record {K : ℕ} {Γ P : Type} {x : List Γ}
    (d : Cfg (K + 1) Γ P x) (q : P) (fs gs : List (List Γ))
    (hr : RecordAt d 0 fs) (hlen : (joinFields fs).length = (joinFields gs).length) :
    RecordAt (wl_patch d q gs) 0 gs := by
  intro p hlo hhi
  change (if (0 : Fin (K + 1)) = 0 ∧ d.workTapePos 0 ≤ d.workTapePos 0 + p ∧
      d.workTapePos 0 + p < d.workTapePos 0 + ((joinFields gs).length : ℤ)
    then fieldsTape gs (d.workTapePos 0 + p - d.workTapePos 0)
    else d.workTapes 0 (d.workTapePos 0 + p)) = fieldsTape gs p
  by_cases hin : 0 ≤ p ∧ p < ((joinFields gs).length : ℤ)
  · rw [if_pos (by omega)]
    congr 1
    omega
  · rw [if_neg (by omega), hr p hlo (by omega)]
    have hp : p = -1 ∨ p = ((joinFields gs).length : ℤ) := by omega
    rcases hp with rfl | rfl
    · simp [fieldsTape]
    · simp [fieldsTape, hlen]

/-- A non-stop phase and its final stationary dispatch form a segment avoiding all
stop controls. Proof sketch: apply the public phase-host theorem; before dispatch every
state still has the non-stop phase tag, and the dispatch keeps the final heads. -/
private theorem wl_phase_segment {K : ℕ} {Q T Pt Ps : Type}
    [DecidableEq Pt] [DecidableEq Ps]
    (Rt : MultiTapeTM 1 (RecSym Q T) Pt) (Rs : MultiTapeTM (K + 1) (RecSym Q T) Ps)
    (te ty tn : Pt) (se sy sn : Ps) (i : wl_Phase) (hi : i ≠ .stop)
    {x : List (RecSym Q T)} (a b : Cfg (K + 1) (RecSym Q T) (wl_Ctrl Pt Ps i) x)
    (t : ℕ) (h : (wl_rows Rt Rs i).runFrom a t = b) (v : wl_Ctrl Pt Ps i)
    (hv : b.state = some v) (q : Σ i, wl_Ctrl Pt Ps i)
    (hred : wl_red te ty tn se sy sn i v = some q)
    (hguard : ∀ u < t, ∀ z, ((wl_rows Rt Rs i).runFrom a u).state = some z →
      wl_red te ty tn se sy sn i z = none)
    (B : (Fin (K + 1) → ℤ) → Prop)
    (hb : ∀ u ≤ t, B ((wl_rows Rt Rs i).runFrom a u).workTapePos) :
    Segment (wl_loopTM Rt Rs te ty tn se sy sn)
      {z | ∃ e : WindowExit, z = some ⟨.stop, e⟩} B
      (a.mapState (Sigma.mk i)) (b.mapState (fun _ => q)) (t + 1) := by
  obtain ⟨hpre, hend⟩ := phaseHostTM_run (wl_rows Rt Rs) ⟨.anchor, ()⟩
    (wl_red te ty tn se sy sn) i a b t h v hv q hred hguard
  refine ⟨hend, ?_, ?_⟩
  · intro u hu
    change ¬∃ e : WindowExit,
      ((wl_loopTM Rt Rs te ty tn se sy sn).runFrom _ u).state = some ⟨.stop, e⟩
    rw [show (wl_loopTM Rt Rs te ty tn se sy sn).runFrom _ u =
      ((wl_rows Rt Rs i).runFrom a u).mapState (Sigma.mk i) from hpre u (by omega)]
    rintro ⟨e, he⟩
    change Option.map (fun z : wl_Ctrl Pt Ps i => (⟨i, z⟩ : Σ i, wl_Ctrl Pt Ps i)) _ =
      some (⟨.stop, e⟩ : Σ i, wl_Ctrl Pt Ps i) at he
    obtain ⟨z, _, hz⟩ := Option.map_eq_some_iff.mp he
    exact hi (Sigma.mk.inj hz).1
  · intro u hu
    by_cases ht : u ≤ t
    · change B ((wl_loopTM Rt Rs te ty tn se sy sn).runFrom _ u).workTapePos
      rw [show (wl_loopTM Rt Rs te ty tn se sy sn).runFrom _ u =
        ((wl_rows Rt Rs i).runFrom a u).mapState (Sigma.mk i) from hpre u ht]
      exact hb u ht
    · have he : u = t + 1 := by omega
      subst u
      change B ((wl_loopTM Rt Rs te ty tn se sy sn).runFrom _ (t + 1)).workTapePos
      rw [show (wl_loopTM Rt Rs te ty tn se sy sn).runFrom _ (t + 1) =
        b.mapState (fun _ => q) from hend]
      have := hb t le_rfl
      rwa [h] at this

/-- The loop is stationary at any stop, including its unused exhausted stop. -/
private theorem wl_stop_fixed {K : ℕ} {Q T Pt Ps : Type}
    [DecidableEq Pt] [DecidableEq Ps]
    (Rt : MultiTapeTM 1 (RecSym Q T) Pt) (Rs : MultiTapeTM (K + 1) (RecSym Q T) Ps)
    (te ty tn : Pt) (se sy sn : Ps) {x : List (RecSym Q T)}
    (d : Cfg (K + 1) (RecSym Q T) (Σ i, wl_Ctrl Pt Ps i) x) (e : WindowExit)
    (hd : d.state = some ⟨.stop, e⟩) (t : ℕ) :
    (wl_loopTM Rt Rs te ty tn se sy sn).runFrom d t = d := by
  have hs : (wl_loopTM Rt Rs te ty tn se sy sn).step d = d := by
    simp only [MultiTapeTM.step, hd, wl_loopTM, phaseHostTM, wl_red, wl_rows]
    apply Cfg.ext <;> simp [Action.mapState, Action.apply, hd]
  exact Function.iterate_fixed hs t

open Classical in
/-- One positive window round, with a fixed envelope and exact restored endpoint.

Proof sketch: concatenate the anchor dispatch, the R1-embedded halted-state test, and
(only for a live source) the record step, using the public phase-host theorem and segment
composition. The row contracts supply their first verdicts and head bounds. Every dispatch
is stationary; the anchor makes the total positive even when either row takes zero steps. -/
private theorem wl_round {k K : ℕ} {Q T Pt Ps : Type}
    [DecidableEq Pt] [DecidableEq Ps]
    (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (Rt : MultiTapeTM 1 (RecSym Q T) Pt) (Rs : MultiTapeTM (K + 1) (RecSym Q T) Ps)
    (te ty tn : Pt) (se sy sn : Ps) (Ct Cs : ℕ) (hyn : ty ≠ tn) (hsyn : sy ≠ sn)
    {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T)
    (d : Cfg (K + 1) (RecSym Q T) (Σ i, wl_Ctrl Pt Ps i)
      (x.map (RecSym.digitEmb Q T))) (hd : d.state = some ⟨.anchor, ()⟩)
    (htest : ∃ t ≤ Ct * ((joinFields (cfgRecord s c τ)).length + 1),
      (∀ u < t, (Rt.runFrom ((wl_at d te).select (wl_recordTape K)) u).state ≠ some ty ∧
        (Rt.runFrom ((wl_at d te).select (wl_recordTape K)) u).state ≠ some tn) ∧
      (∀ u ≤ t, ∀ j : Fin 1,
        |(Rt.runFrom ((wl_at d te).select (wl_recordTape K)) u).workTapePos j -
          d.workTapePos 0| ≤ ((Ct * ((joinFields (cfgRecord s c τ)).length + 1) : ℕ) : ℤ)) ∧
      Rt.runFrom ((wl_at d te).select (wl_recordTape K)) t =
        { (wl_at d te).select (wl_recordTape K) with
          state := some (if c.state.isNone then ty else tn) })
    (hstep : ∃ t ≤ Cs * ((joinFields (cfgRecord s c τ)).length + x.length + 1),
      (∀ u < t, (Rs.runFrom (wl_at d se) u).state ≠ some sy ∧
        (Rs.runFrom (wl_at d se) u).state ≠ some sn) ∧
      (∀ u ≤ t, ∀ j : Fin (K + 1),
        |(Rs.runFrom (wl_at d se) u).workTapePos j - d.workTapePos j| ≤
          ((Cs * ((joinFields (cfgRecord s c τ)).length + 1) : ℕ) : ℤ)) ∧
      ((M.step c).InWindow s → Rs.runFrom (wl_at d se) t =
        { wl_at d se with
          state := some sy
          workTapes := fun j p =>
            if j = 0 ∧ d.workTapePos j ≤ p ∧
                p < d.workTapePos j + ((joinFields (cfgRecord s c τ)).length : ℤ)
              then fieldsTape (cfgRecord s (M.step c) (upd τ (M.outputSymbol c)))
                (p - d.workTapePos j)
              else d.workTapes j p }) ∧
      (¬(M.step c).InWindow s → Rs.runFrom (wl_at d se) t = wl_at d sn)) :
    ∃ t, 1 ≤ t ∧ t ≤ (Ct + Cs + 3) * (recordLength k x.length s + x.length + 1) ∧
      Segment (wl_loopTM Rt Rs te ty tn se sy sn)
        {z | ∃ e : WindowExit, z = some ⟨.stop, e⟩}
        (fun p => ∀ j, |p j - d.workTapePos j| ≤
          (((Ct + Cs + 3) * (recordLength k x.length s + 1) : ℕ) : ℤ))
        d (if c.state = none then wl_at d ⟨.stop, WindowExit.halted⟩
          else if (M.step c).InWindow s then
            wl_patch d ⟨.anchor, ()⟩ (cfgRecord s (M.step c) (upd τ (M.outputSymbol c)))
          else wl_at d ⟨.stop, WindowExit.left⟩) t := by
  classical
  let B := fun p : Fin (K + 1) → ℤ => ∀ j, |p j - d.workTapePos j| ≤
    (((Ct + Cs + 3) * (recordLength k x.length s + 1) : ℕ) : ℤ)
  have hB : B d.workTapePos := by
    intro j
    simp only [sub_self, abs_zero]
    exact_mod_cast Nat.zero_le ((Ct + Cs + 3) * (recordLength k x.length s + 1))
  have hanchor := wl_phase_segment Rt Rs te ty tn se sy sn .anchor (by decide)
    (wl_at d ()) (wl_at d ()) 0 rfl () rfl ⟨.test, te⟩ rfl
    (fun u hu => by omega) B (fun u hu => by
      have : u = 0 := by omega
      subst u
      exact hB)
  have ha : (wl_at d ()).mapState (Sigma.mk wl_Phase.anchor) = d := by
    apply Cfg.ext <;> simp [wl_at, Cfg.mapState, hd]
  rw [ha] at hanchor
  obtain ⟨tt, htt, htcut, htenv, htrun⟩ := htest
  let a := wl_at d te
  let v := if c.state.isNone then ty else tn
  have hemb (u : ℕ) : (wl_rows Rt Rs .test).runFrom a u =
      embedEmitCfg (wl_recordTape K) a.workTapes a.workTapePos a.output
        (Rt.runFrom (a.select (wl_recordTape K)) u) := by
    change (embedEmitTM (wl_recordTape K) Rt).runFrom a u = _
    conv_lhs => rw [← embedEmitCfg_select (wl_recordTape K) a]
    exact embedEmitTM_runFrom (wl_recordTape K) Rt _ _ _ _ u
  have hte : (wl_rows Rt Rs .test).runFrom a tt = wl_at d v := by
    rw [hemb, htrun]
    apply embedEmitCfg_eq
    · rfl
    · rfl
    · exact List.append_nil _
    · intro j
      exact ⟨rfl, rfl⟩
    · intro j _
      exact ⟨rfl, rfl⟩
  have htg : ∀ u < tt, ∀ z, ((wl_rows Rt Rs .test).runFrom a u).state = some z →
      wl_red te ty tn se sy sn .test z = none := by
    intro u hu z hz
    rw [hemb] at hz
    change (Rt.runFrom (a.select (wl_recordTape K)) u).state = some z at hz
    have hc := htcut u hu
    have hy : z ≠ ty := fun h => hc.1 (hz.trans (congrArg some h))
    have hn : z ≠ tn := fun h => hc.2 (hz.trans (congrArg some h))
    simp only [wl_red, if_neg hy, if_neg hn]
  have htb : ∀ u ≤ tt, B ((wl_rows Rt Rs .test).runFrom a u).workTapePos := by
    intro u hu j
    rw [hemb]
    by_cases hj : j = 0
    · subst j
      rw [show (0 : Fin (K + 1)) = wl_recordTape K 0 from rfl,
        embedEmitCfg_selected_pos]
      exact (htenv u hu 0).trans (by
        rw [joinFields_cfgRecord_length]
        exact_mod_cast Nat.mul_le_mul_right (recordLength k x.length s + 1)
          (show Ct ≤ Ct + Cs + 3 by omega))
    · have hj' : j ∉ Set.range (wl_recordTape K) := by
        rintro ⟨z, hz⟩
        exact hj hz.symm
      rw [(embedEmitCfg_unselected (wl_recordTape K) _ _ _ _ j hj').2]
      exact hB j
  by_cases hc : c.state = none
  · have hv : v = ty := by simp [v, hc]
    have ht := wl_phase_segment Rt Rs te ty tn se sy sn .test (by decide)
      a (wl_at d v) tt hte v rfl ⟨.stop, WindowExit.halted⟩
      (by simp [wl_red, hv]) htg B htb
    have hs := hanchor.trans ht
    refine ⟨1 + (tt + 1), by omega, ?_, ?_⟩
    · rw [joinFields_cfgRecord_length] at htt
      nlinarith
    · simpa only [if_pos hc] using hs
  · have hv : v = tn := by cases hs : c.state <;> simp_all [v]
    have ht := wl_phase_segment Rt Rs te ty tn se sy sn .test (by decide)
      a (wl_at d v) tt hte v rfl ⟨.step, se⟩
      (by simp [wl_red, hv, Ne.symm hyn]) htg B htb
    have hfirst := hanchor.trans ht
    obtain ⟨ts, hts, hscut, hsenv, hsy, hsn⟩ := hstep
    have hsg : ∀ u < ts, ∀ z, ((wl_rows Rt Rs .step).runFrom (wl_at d se) u).state =
        some z → wl_red te ty tn se sy sn .step z = none := by
      intro u hu z hz
      have hy : z ≠ sy := fun h => (hscut u hu).1 (hz.trans (congrArg some h))
      have hn : z ≠ sn := fun h => (hscut u hu).2 (hz.trans (congrArg some h))
      simp only [wl_red, if_neg hy, if_neg hn]
    have hsb : ∀ u ≤ ts, B ((wl_rows Rt Rs .step).runFrom (wl_at d se) u).workTapePos := by
      intro u hu j
      exact (hsenv u hu j).trans (by
        rw [joinFields_cfgRecord_length]
        exact_mod_cast Nat.mul_le_mul_right (recordLength k x.length s + 1)
          (show Cs ≤ Ct + Cs + 3 by omega))
    have htime : 1 + (tt + 1) + (ts + 1) ≤
        (Ct + Cs + 3) * (recordLength k x.length s + x.length + 1) := by
      rw [joinFields_cfgRecord_length] at htt hts
      nlinarith
    by_cases hw : (M.step c).InWindow s
    · let b := Rs.runFrom (wl_at d se) ts
      have hbs : b.state = some sy := by rw [show b = _ from hsy hw]
      have hs := wl_phase_segment Rt Rs te ty tn se sy sn .step (by decide)
        (wl_at d se) b ts rfl sy hbs ⟨.anchor, ()⟩
        (by simp [wl_red]) hsg B hsb
      have hend : b.mapState (fun _ => (⟨.anchor, ()⟩ : Σ i, wl_Ctrl Pt Ps i)) =
          wl_patch d ⟨.anchor, ()⟩ (cfgRecord s (M.step c) (upd τ (M.outputSymbol c))) := by
        rw [show b = _ from hsy hw]
        apply Cfg.ext <;> try rfl
        funext j p
        dsimp only [Cfg.mapState, wl_at, wl_patch]
        rw [joinFields_cfgRecord_length, joinFields_cfgRecord_length]
        by_cases hj : j = 0
        · subst j
          rfl
        · simp only [hj, false_and, ↓reduceIte]
      refine ⟨_, by omega, htime, ?_⟩
      simp only [if_neg hc, if_pos hw]
      exact ⟨(hfirst.trans hs).1.trans hend, (hfirst.trans hs).2⟩
    · have hs := wl_phase_segment Rt Rs te ty tn se sy sn .step (by decide)
        (wl_at d se) (wl_at d sn) ts (hsn hw) sn rfl ⟨.stop, WindowExit.left⟩
        (by simp [wl_red, Ne.symm hsyn]) hsg B hsb
      exact ⟨_, by omega, htime, by simpa only [if_neg hc, if_neg hw] using hfirst.trans hs⟩

/-- **H3's loop: the unclocked windowed round loop.** For a fixed binary machine `M` and a tag
update `upd` that ignores silent steps, there is a module over the record alphabet with an
entry (the round anchor) and three distinct live stop states `stop e` with the following
contract. Start it at its entry with the record of a windowed configuration `c` with tag `τ`
at the head of tape `0`, its other tapes blank, and the native input `x` as digits.
* At every time, every work head stays within `C` times the record length plus one of its
  entry position, and the output is unchanged.
* For every `N`, at some time `t ≤ C · N · (record length + |x| + 1)`, with no stop state
  before `t`, the module is exactly as `N` rounds of `Turing.windowRun` say: if those rounds
  stop (exit `halted` or `left`) it is in `stop e` with the stopping record, and if they do
  not it is back at its entry with the record of the configuration after `N` steps, at a time
  `t ≥ N`. Every other tape, every head, the input position and the output are restored.

So the loop stops exactly when the semantic run does, and a run that never stops keeps the
loop live forever, inside its envelope. [AB09, Theorem 4.8 with Exercise 4.1; the loop is
the repository's refinement]

**Proof sketch.** One phase host (`Turing.phaseHostTM`) with three phases. The test phase is
`Turing.exists_recordTestTM` at the predicate "halted", embedded by R1 on tape `0`: `yes` goes
to `stop halted`, `no` to the step phase. The step phase is `Turing.exists_recordStepTM` at
`(M, upd)` on the bank `0, …, K`: `yes` returns to the entry, `no` goes to `stop left`. The stop
states are stationary. The entry first makes one stationary anchor step into the test phase,
so every round takes at least one step: the record rows bound their exit times only from
above (a test of a constant predicate may answer at once, and a record step of a stationary
source with an identity tag update may take no step), and the anchor step is absorbed into
`C`. Each round costs at most `C · (L + |x| + 1)`, and both rows restore every head and scratch
tape, so the envelope holds at all times and does not grow with the number of rounds. The record
length is `Turing.recordLength` (`Turing.joinFields_cfgRecord_length`). The `N`-round
statement is an induction on `N` along `Turing.windowRun`, concatenating rounds by
`Turing.MultiTapeTM.runFrom_add`.

**Fill appendix (B6-F2).** The four phase tags include the explicit anchor. The private
`wl_round` uses the two public rows, R1 reconstruction, and `Segment.trans`; it proves
positive duration even for zero-time rows. Same-width record patches compose without
changing delimiters or heads. The every-`N` induction keeps the common head envelope,
and a cofinal endpoint or a stationary stop covers each physical time. Output-prefix
monotonicity and equal endpoint outputs give silence. -/
theorem exists_windowLoopTM (M : FinTM Bool) {T : Type} [Fintype T] [DecidableEq T]
    (upd : T → Option Bool → T) (hupd : ∀ τ, upd τ none = τ) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (L : MultiTapeTM (K + 1) (RecSym M.State T) P) (entry : P) (stop : WindowExit → P)
      (C : ℕ),
      (∀ e, stop e ≠ entry) ∧ Function.Injective stop ∧
      ∀ {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : T), c.InWindow s →
      ∀ d : Cfg (K + 1) (RecSym M.State T) P (x.map (RecSym.digitEmb M.State T)),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        (∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) →
        (∀ u (j : Fin (K + 1)), |(L.runFrom d u).workTapePos j - d.workTapePos j| ≤
          ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
        (∀ u, (L.runFrom d u).output = d.output) ∧
        ∀ N : ℕ, ∃ t, t ≤ C * N * (recordLength M.k x.length s + x.length + 1) ∧
          ((windowRun M.tm s upd N c τ).1 = .exhausted → N ≤ t) ∧
          (∀ u < t, ∀ e, (L.runFrom d u).state ≠ some (stop e)) ∧
          L.runFrom d t =
            { d with
              state := some (if (windowRun M.tm s upd N c τ).1 = .exhausted then entry
                else stop (windowRun M.tm s upd N c τ).1)
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos 0 ≤ q ∧
                    q < d.workTapePos 0 + (recordLength M.k x.length s : ℤ)
                  then fieldsTape (cfgRecord s (windowRun M.tm s upd N c τ).2.1
                    (windowRun M.tm s upd N c τ).2.2) (q - d.workTapePos 0)
                else d.workTapes j q } := by
  classical
  obtain ⟨Pt, hPt, dPt, Rt, te, ty, tn, Ct, hyn, htest⟩ :=
    exists_recordTestTM (k := M.k) (Q := M.State) (T := T) (fun q _ => q.isNone)
  obtain ⟨K, Ps, hPs, dPs, Rs, se, sy, sn, Cs, hsyn, hstep⟩ := exists_recordStepTM M.tm upd hupd
  letI := hPt
  letI := dPt
  letI := hPs
  letI := dPs
  let C := Ct + Cs + 3
  let L := wl_loopTM Rt Rs te ty tn se sy sn
  let stop : WindowExit → Σ i, wl_Ctrl Pt Ps i := fun e => ⟨.stop, e⟩
  have rounds {x : List Bool} (s : ℕ) (N : ℕ) (c : Cfg M.k Bool M.State x) (τ : T)
      (hc : c.InWindow s)
      (d : Cfg (K + 1) (RecSym M.State T) (Σ i, wl_Ctrl Pt Ps i)
        (x.map (RecSym.digitEmb M.State T)))
      (hd : d.state = some ⟨.anchor, ()⟩) (hr : RecordAt d 0 (cfgRecord s c τ))
      (hb : ∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) :
      ∃ t, t ≤ C * N * (recordLength M.k x.length s + x.length + 1) ∧
        ((windowRun M.tm s upd N c τ).1 = .exhausted → N ≤ t) ∧
        Segment L {z | ∃ e, z = some (stop e)}
          (fun p => ∀ j, |p j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ))
          d (wl_patch d
            (if (windowRun M.tm s upd N c τ).1 = .exhausted then ⟨.anchor, ()⟩
              else stop (windowRun M.tm s upd N c τ).1)
            (cfgRecord s (windowRun M.tm s upd N c τ).2.1
              (windowRun M.tm s upd N c τ).2.2)) t := by
    induction N generalizing c τ d with
    | zero =>
      refine ⟨0, by simp, fun _ => Nat.zero_le _, ?_⟩
      simp only [windowRun, ite_true]
      rw [wl_patch_self d _ _ hr]
      have he : wl_at d (⟨.anchor, ()⟩ : Σ i, wl_Ctrl Pt Ps i) = d := by
        apply Cfg.ext <;> simp [wl_at, hd]
      rw [he]
      exact Segment.zero (fun j => by simp)
    | succ N ih =>
      have htest' := htest s c τ ((wl_at d te).select (wl_recordTape K)) rfl
        (show RecordAt ((wl_at d te).select (wl_recordTape K)) 0 (cfgRecord s c τ)
          from hr)
      have hstep' := hstep s c τ hc (wl_at d se) rfl hr hb
      obtain ⟨tr, hpos, htr, hround⟩ := wl_round M.tm upd Rt Rs te ty tn se sy sn Ct Cs
        hyn hsyn s c τ d hd htest' hstep'
      have hbound : tr ≤ C * (N + 1) *
          (recordLength M.k x.length s + x.length + 1) := by
        dsimp only [C]
        nlinarith
      by_cases hhalt : c.state = none
      · refine ⟨tr, hbound, ?_, ?_⟩
        · simp [windowRun, hhalt]
        · simp only [windowRun, if_pos hhalt]
          rw [if_neg (by decide), wl_patch_self d _ _ hr]
          simpa only [if_pos hhalt] using hround
      · by_cases hwin : (M.tm.step c).InWindow s
        · let d' := wl_patch d ⟨.anchor, ()⟩
            (cfgRecord s (M.tm.step c) (upd τ (M.tm.outputSymbol c)))
          have hr' : RecordAt d' 0
              (cfgRecord s (M.tm.step c) (upd τ (M.tm.outputSymbol c))) :=
            wl_patch_record d _ _ _ hr (by simp only [joinFields_cfgRecord_length])
          have hb' : ∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d'.workTapes j p = none := by
            intro j hj p
            simpa [d', wl_patch, hj] using hb j hj p
          obtain ⟨tnext, htnext, hprogress, hnext⟩ :=
            ih (M.tm.step c) (upd τ (M.tm.outputSymbol c)) hwin d' rfl hr' hb'
          have hround' : Segment L {z | ∃ e, z = some (stop e)}
              (fun p => ∀ j, |p j - d.workTapePos j| ≤
                ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) d d' tr := by
            simpa only [if_neg hhalt, if_pos hwin] using hround
          have hboth := hround'.trans hnext
          have hpatch := wl_patch_patch d ⟨.anchor, ()⟩
            (if (windowRun M.tm s upd N (M.tm.step c) (upd τ (M.tm.outputSymbol c))).1 =
                .exhausted then ⟨.anchor, ()⟩ else stop
                (windowRun M.tm s upd N (M.tm.step c) (upd τ (M.tm.outputSymbol c))).1)
            (cfgRecord s (M.tm.step c) (upd τ (M.tm.outputSymbol c)))
            (cfgRecord s
              (windowRun M.tm s upd N (M.tm.step c) (upd τ (M.tm.outputSymbol c))).2.1
              (windowRun M.tm s upd N (M.tm.step c) (upd τ (M.tm.outputSymbol c))).2.2)
            (by simp only [joinFields_cfgRecord_length])
          refine ⟨tr + tnext, ?_, ?_, ?_⟩
          · change tr ≤ C * (recordLength M.k x.length s + x.length + 1) at htr
            nlinarith
          · simp only [windowRun, if_neg hhalt, if_pos hwin]
            intro he
            have := hprogress he
            omega
          · simp only [windowRun, if_neg hhalt, if_pos hwin]
            change Segment L _ _ d _ _ at hboth
            dsimp only [d'] at hboth
            rw [hpatch] at hboth
            exact hboth
        · refine ⟨tr, hbound, ?_, ?_⟩
          · simp [windowRun, hhalt, hwin]
          · simp only [windowRun, if_neg hhalt, if_neg hwin]
            rw [if_neg (by decide), wl_patch_self d _ _ hr]
            simpa only [if_neg hhalt, if_neg hwin] using hround
  refine ⟨K, Σ i, wl_Ctrl Pt Ps i, inferInstance, inferInstance, L,
    ⟨.anchor, ()⟩, stop, C, ?_, ?_, ?_⟩
  · intro e h
    cases h
  · intro a b h
    cases h
    rfl
  intro x s c τ hc d hd hrec hblank
  have hall (u : ℕ) :
      (∀ j, |(L.runFrom d u).workTapePos j - d.workTapePos j| ≤
        ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
      (L.runFrom d u).output = d.output := by
    obtain ⟨t, _, hp, hs⟩ := rounds s (u + 1) c τ hc d hd hrec hblank
    have hout : (L.runFrom d t).output = d.output := by rw [hs.1]; rfl
    by_cases hut : u ≤ t
    · refine ⟨hs.2.2 u hut, ?_⟩
      have lo := L.output_prefix d (Nat.zero_le u)
      have hi := L.output_prefix d hut
      rw [hout] at hi
      exact List.IsPrefix.eq_of_length_le hi (List.IsPrefix.length_le lo)
    · have he : (windowRun M.tm s upd (u + 1) c τ).1 ≠ .exhausted := by
        intro he
        have := hp he
        omega
      have hstate : (L.runFrom d t).state =
          some (stop (windowRun M.tm s upd (u + 1) c τ).1) := by
        rw [hs.1]
        simp only [wl_patch, if_neg he]
      have hfix := wl_stop_fixed Rt Rs te ty tn se sy sn (L.runFrom d t)
        (windowRun M.tm s upd (u + 1) c τ).1 hstate (u - t)
      have hu : L.runFrom d u = L.runFrom d t := by
        rw [show u = t + (u - t) from by omega, MultiTapeTM.runFrom_add]
        exact hfix
      rw [hu]
      exact ⟨hs.2.2 t le_rfl, hout⟩
  refine ⟨fun u j => (hall u).1 j, fun u => (hall u).2, ?_⟩
  intro N
  obtain ⟨t, ht, hp, hs⟩ := rounds s N c τ hc d hd hrec hblank
  refine ⟨t, ht, hp, ?_, ?_⟩
  · intro u hu e he
    exact hs.2.1 u hu ⟨e, he⟩
  · convert hs.1 using 1
    simp only [wl_patch, joinFields_cfgRecord_length]

/-! ### Windowed-runner fill (B6-F2): the clocked runner -/

/-- The runner's two phases: the step clock over the loop, and the exhausted
exit. -/
private def wr_Ctrl (Q : Type) : Bool → Type
  | true => Q
  | false => Unit

/-- The runner's phase controls are finite. -/
private instance wr_Ctrl_fintype (Q : Type) [Fintype Q] : (b : Bool) → Fintype (wr_Ctrl Q b)
  | true => inferInstanceAs (Fintype Q)
  | false => inferInstanceAs (Fintype Unit)

/-- The runner's phase controls have decidable equality. -/
private instance wr_Ctrl_decidableEq (Q : Type) [DecidableEq Q] :
    (b : Bool) → DecidableEq (wr_Ctrl Q b)
  | true => inferInstanceAs (DecidableEq Q)
  | false => inferInstanceAs (DecidableEq Unit)

/-- **H3, the windowed runner**: the step clock `H` over the loop, whose every
`timeout r` dispatches in one stationary step to the exhausted exit (hence the `+ 3`). -/
private def wr_runnerTM {k : ℕ} {Γ Q S : Type} [DecidableEq Q] [Fintype S]
    (H : MultiTapeTM k Γ Q) (timeout : Option S → Q) : MultiTapeTM k Γ (Σ b, wr_Ctrl Q b) :=
  phaseHostTM (fun b => match b with
      | true => H
      | false => ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, some ()⟩⟩)
    ⟨true, H.q₀⟩
    (fun b q => match b, q with
      | true, q => if ∃ r, q = timeout r then some ⟨false, ()⟩ else none
      | false, _ => none)

/-- The runner's exits: `halted` and `left` are the clock's `finish` at the loop's
two stops; `exhausted` is the dispatch target. -/
private def wr_exit {P Q : Type} (finish : Option P → Q) (stop : WindowExit → P) :
    WindowExit → Σ b, wr_Ctrl Q b
  | .halted => ⟨true, finish (some (stop .halted))⟩
  | .left => ⟨true, finish (some (stop .left))⟩
  | .exhausted => ⟨false, ()⟩

/-- **A runner configuration in the clock's layout**: a host
configuration at the clock state `q` is the clock layout (`Turing.clockCfg`) of its loop part
(the first `K + 1` tapes and heads, the input head and the output, at the loop state `p`) and
its last tape, tagged into the clock phase. This is how the runner's start meets
`Turing.exists_stepClockTMVia`'s precondition.

**Proof sketch.** Field by field; split the tape index by `Fin.lastCases`. -/
private theorem wr_clockCfg_eta {K : ℕ} {Γ P Q : Type} {x : List Γ}
    (d : Cfg (K + 1 + 1) Γ (Σ b, wr_Ctrl Q b) x) (q : Q) (p : P)
    (hd : d.state = some ⟨true, q⟩) :
    d = (clockCfg (some q)
          (⟨some p, d.inputPos, fun j => d.workTapes j.castSucc,
            fun j => d.workTapePos j.castSucc, d.output⟩ : Cfg (K + 1) Γ P x)
          (d.workTapes (Fin.last (K + 1))) (d.workTapePos (Fin.last (K + 1)))).mapState
        (fun q => (⟨true, q⟩ : Σ b, wr_Ctrl Q b)) := by
  apply Cfg.ext
  · simp [Cfg.mapState, clockCfg, hd]
  · rfl
  · funext j
    induction j using Fin.lastCases <;> simp [Cfg.mapState, clockCfg]
  · funext j
    induction j using Fin.lastCases <;> simp [Cfg.mapState, clockCfg]
  · rfl

/-- Before any timeout, the runner follows the clock with its phase tag.
Proof sketch: the phase table agrees with the clock on every non-timeout state, so the
public state-transport theorem gives the prefix without another simulation induction. -/
private theorem wr_prefix {k : ℕ} {Γ Q S : Type} [DecidableEq Q] [Fintype S]
    (H : MultiTapeTM k Γ Q) (timeout : Option S → Q) {x : List Γ}
    (a : Cfg k Γ Q x) (t : ℕ)
    (hcut : ∀ u < t, ∀ r, (H.runFrom a u).state ≠ some (timeout r)) :
    ∀ u ≤ t, (wr_runnerTM H timeout).runFrom (a.mapState (Sigma.mk true)) u =
      (H.runFrom a u).mapState (Sigma.mk true) := by
  intro u hu
  refine MultiTapeTM.runFrom_mapState_of_agreeOn H (wr_runnerTM H timeout)
    ⟨(fun q : Q => (⟨true, q⟩ : Σ b, wr_Ctrl Q b)),
      fun _ _ h => eq_of_heq (Sigma.mk.inj h).2⟩
    (fun q => ∀ r, q ≠ timeout r) ?_ a u ?_
  · intro q hq inp work
    have hnot : ¬∃ r, q = timeout r := by simpa using hq
    simp only [wr_runnerTM, phaseHostTM, Function.Embedding.coeFn_mk, if_neg hnot]
  · intro v hv q hq r he
    exact hcut v (by omega) r (hq.trans (congrArg some he))

/-- At a timeout the runner makes exactly one stationary dispatch to exhaustion. -/
private theorem wr_timeout_dispatch {k : ℕ} {Γ Q S : Type}
    [DecidableEq Q] [Fintype S] (H : MultiTapeTM k Γ Q) (timeout : Option S → Q)
    {x : List Γ} (a : Cfg k Γ Q x) (t : ℕ) (r : Option S)
    (hs : (H.runFrom a t).state = some (timeout r))
    (hcut : ∀ u < t, ∀ r, (H.runFrom a u).state ≠ some (timeout r)) :
    (wr_runnerTM H timeout).runFrom (a.mapState (Sigma.mk true)) (t + 1) =
      (H.runFrom a t).mapState (fun _ => ⟨false, ()⟩) := by
  unfold wr_runnerTM
  refine (phaseHostTM_run (Ph := wr_Ctrl Q) _ _ _ true a (H.runFrom a t) t rfl (timeout r) hs
    ⟨false, ()⟩ ?_ ?_).2
  · simp only [if_pos (show ∃ v, timeout r = timeout v from ⟨r, rfl⟩)]
  · intro u hu q hq
    have hn : ¬∃ r, q = timeout r := by
      rintro ⟨r, rfl⟩
      exact hcut u hu r hq
    exact if_neg hn

/-- A common head radius bounds the total visited work space: the public
`Turing.MultiTapeTM.spaceUsed_le_of_abs_le`, at this module's universe. -/
private theorem wr_space {k : ℕ} {Γ P : Type} (R : MultiTapeTM k Γ P)
    {x : List Γ} (d : Cfg k Γ P x) (t radius : ℕ)
    (henv : ∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (radius : ℤ)) :
    R.spaceUsed d t ≤ k * (2 * radius + 1) :=
  MultiTapeTM.spaceUsed_le_of_abs_le R d t radius henv

/-- **H3, the windowed runner** (the loop under the step clock, with the clock word supplied
by the consumer). For a fixed binary machine `M` and a tag update `upd` that ignores silent
steps, there is a module over the record alphabet with an entry and three distinct exits
`exit e`, as follows. Start it at its entry with the record of a windowed configuration `c`
with tag `τ` at the head of tape `0`, a delimited digit word `w` of value `d` at the head of
the last tape, the other tapes blank, and the native input `x` as digits. Then it reaches an
exit `exit out` at a time `t ≤ 5d + 2|w| + 3`, and no exit earlier; up to `t` every head stays
within `C` times the record length plus `|w| + 1` of its entry position, the output is
unchanged, and the space used is at most the number of tapes times twice that radius plus
one. Moreover:
* **halt and window exit are certified**: if `N` rounds of `Turing.windowRun` stop, and
  `C · N · (record length + |x| + 1) ≤ d`, then `out` is their exit;
* **and determined**: if `out` is `halted` or `left`, it is the exit of a stopping
  `Turing.windowRun`, whose record is on tape `0`; the clock interval holds some digit word of
  width `|w|`; every other cell, every head and the input position are restored;
* `out = exhausted` is the clock's timeout, with no further claim on the tapes.

[AB09, Theorem 4.8 with Exercise 4.1; the runner is the repository's refinement]

**Proof sketch.** `Turing.exists_stepClockTMVia` at `e := RecSym.digitEmb`, body the loop of
`Turing.exists_windowLoopTM`, and stop states the loop's two stop states `stop halted` and
`stop left`; the clock's `inj` of the loop's entry is the runner's entry, and its `finish` at
the two stop states are the exits `halted` and `left` (all other `finish` values are
unreachable). Every `timeout r` dispatches in one step to the exit `exhausted`, hence the `+ 3`.
The loop's stop time after `N` stopping rounds is at most
`C · N · (L + |x| + 1)`; if it is at most `d` the clock finishes there, and otherwise it times
out. By the clock's frame clause the body heads, the input head and the output follow the
loop's, which the loop's all-times envelope and silence bound, and the counter head stays in
`[cp - 1, cp + |w|]`.

**Fill appendix (B6-F2).** The prescribed layout lemma supplies the clock start. At a first
physical stop, the loop endpoint for `N = r + 1` rules out both a premature halt and an
exhausted semantic result, so the stop has the claimed record. The finish case uses
`windowRun_stop_unique`; in the timeout case any certified semantic stop would contradict
the clock precondition. State transport supplies the clock prefix, and `phaseHostTM_run`
supplies its timeout dispatch. One common frame calculation gives both cases' head bounds
and silence; the public per-tape interval bound gives total space. -/
theorem exists_windowRunnerTM (M : FinTM Bool) {T : Type} [Fintype T] [DecidableEq T]
    (upd : T → Option Bool → T) (hupd : ∀ τ, upd τ none = τ) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 2) (RecSym M.State T) P) (entry : P) (exit : WindowExit → P)
      (C : ℕ),
      (∀ e, exit e ≠ entry) ∧ Function.Injective exit ∧
      ∀ {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : T), c.InWindow s →
      ∀ (w : List Bool)
        (d : Cfg (K + 2) (RecSym M.State T) P (x.map (RecSym.digitEmb M.State T))),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
          d.workTapes (Fin.last (K + 1)) (d.workTapePos (Fin.last (K + 1)) + p) =
            FinTM.bufferTape (w.map (RecSym.digitEmb M.State T)) p) →
        (∀ j : Fin (K + 2), j ≠ 0 → j ≠ Fin.last (K + 1) → ∀ p, d.workTapes j p = none) →
        ∃ (t : ℕ) (out : WindowExit),
          t ≤ 5 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 3 ∧
          (R.runFrom d t).state = some (exit out) ∧
          (∀ u < t, ∀ e, (R.runFrom d u).state ≠ some (exit e)) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 2), |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + w.length + 1) : ℕ) : ℤ)) ∧
          (∀ u ≤ t, (R.runFrom d u).output = d.output) ∧
          R.spaceUsed d t ≤ (K + 2) * (2 * C * (recordLength M.k x.length s + w.length + 1) + 1) ∧
          (∀ N, (windowRun M.tm s upd N c τ).1 ≠ .exhausted →
            C * N * (recordLength M.k x.length s + x.length + 1) ≤
              Nat.ofDigits 2 (w.map Bool.toNat) →
            out = (windowRun M.tm s upd N c τ).1) ∧
          (out ≠ .exhausted → ∃ N, (windowRun M.tm s upd N c τ).1 = out ∧
            ∃ w' : List Bool, w'.length = w.length ∧
            R.runFrom d t =
              { d with
                state := some (exit out)
                workTapes := fun j q =>
                  if j = 0 ∧ d.workTapePos 0 ≤ q ∧
                      q < d.workTapePos 0 + (recordLength M.k x.length s : ℤ)
                    then fieldsTape (cfgRecord s (windowRun M.tm s upd N c τ).2.1
                      (windowRun M.tm s upd N c τ).2.2) (q - d.workTapePos 0)
                  else if j = Fin.last (K + 1) then
                    wordPatch (d.workTapes j) (d.workTapePos j)
                      (w'.map (RecSym.digitEmb M.State T)) q
                  else d.workTapes j q }) := by
  classical
  obtain ⟨K, P, hP, dP, L, entry, stop, CL, hne, hstop, hloop⟩ := exists_windowLoopTM M upd hupd
  letI := hP
  letI := dP
  obtain ⟨Q, hQ, dQ, H, inj, finish, timeout, hfin, hto, hft, hif, hclock⟩ :=
    exists_stepClockTMVia (RecSym.digitEmb M.State T) L
      (fun p => decide (p = stop .halted ∨ p = stop .left))
  letI := hQ
  letI := dQ
  refine ⟨K, Σ b, wr_Ctrl Q b, inferInstance, inferInstance, wr_runnerTM H timeout,
    ⟨true, inj entry⟩, wr_exit finish stop, CL + 1, ?_, ?_, ?_⟩
  · intro e h
    cases e with
    | halted => exact (hif entry _).1 (eq_of_heq (Sigma.mk.inj h).2).symm
    | left => exact (hif entry _).1 (eq_of_heq (Sigma.mk.inj h).2).symm
    | exhausted => exact absurd (Sigma.mk.inj h).1 (by decide)
  · intro a b h
    cases a <;> cases b <;> first
      | rfl
      | exact absurd (Sigma.mk.inj h).1 (by decide)
      | exact absurd (hstop (Option.some.inj (hfin (eq_of_heq (Sigma.mk.inj h).2)))) (by decide)
  -- The clock is used only through its frozen contract; every timeout is intercepted.
  intro x s c τ hc w d hd hrec hclk hblank
  let d' : Cfg (K + 1) (RecSym M.State T) P (x.map (RecSym.digitEmb M.State T)) :=
    ⟨some entry, d.inputPos, fun j => d.workTapes j.castSucc,
      fun j => d.workTapePos j.castSucc, d.output⟩
  let a := clockCfg (some (inj entry)) d'
    (d.workTapes (Fin.last (K + 1))) (d.workTapePos (Fin.last (K + 1)))
  let R := wr_runnerTM H timeout
  let stopAt := fun p => decide (p = stop .halted ∨ p = stop .left)
  let budget := Nat.ofDigits 2 (w.map Bool.toNat)
  let radius := (CL + 1) * (recordLength M.k x.length s + w.length + 1)
  have hdeta : d = a.mapState (Sigma.mk true) := wr_clockCfg_eta d (inj entry) entry hd
  have hblank' : ∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d'.workTapes j p = none := by
    intro j hj p
    exact hblank j.castSucc (fun he => hj (Fin.castSucc_injective _ he))
      (Fin.castSucc_ne_last j) p
  obtain ⟨henv, hsil, hevery⟩ := hloop s c τ hc d' rfl hrec hblank'
  obtain ⟨hfinish, htimeout⟩ := hclock d' entry rfl w
    (d.workTapes (Fin.last (K + 1))) (d.workTapePos (Fin.last (K + 1))) hclk
  have stopped (u : ℕ) (e : WindowExit) (he : e ≠ .exhausted)
      (hs : (L.runFrom d' u).state = some (stop e)) : (L.runFrom d' u).Stopped stopAt := by
    refine Or.inr ⟨stop e, hs, ?_⟩
    cases e with
    | halted => exact decide_eq_true (Or.inl rfl)
    | left => exact decide_eq_true (Or.inr rfl)
    | exhausted => exact False.elim (he rfl)
  -- A first physical stop is one of the semantic stops. A later live endpoint excludes
  -- a physical halt, and the cofinal exhausted endpoints exclude a spurious early stop.
  have first (r : ℕ) (hs : (L.runFrom d' r).Stopped stopAt)
      (hmin : ∀ u < r, ¬(L.runFrom d' u).Stopped stopAt) :
      (windowRun M.tm s upd (r + 1) c τ).1 ≠ .exhausted ∧
      L.runFrom d' r =
        { d' with
          state := some (stop (windowRun M.tm s upd (r + 1) c τ).1)
          workTapes := fun j q =>
            if j = 0 ∧ d'.workTapePos 0 ≤ q ∧
                q < d'.workTapePos 0 + (recordLength M.k x.length s : ℤ)
              then fieldsTape (cfgRecord s (windowRun M.tm s upd (r + 1) c τ).2.1
                (windowRun M.tm s upd (r + 1) c τ).2.2) (q - d'.workTapePos 0)
              else d'.workTapes j q } := by
    obtain ⟨t, _, hp, hcut, hend⟩ := hevery (r + 1)
    have ht : t ≤ r := by
      by_contra hn
      have hr : r < t := by omega
      rcases hs with hs | ⟨p, hsp, hsp'⟩
      · exact (L.runFrom_state_ne_none_of_le d' t (by rw [hend]; simp) r hr.le) hs
      · have hh : p = stop .halted ∨ p = stop .left := of_decide_eq_true hsp'
        rcases hh with rfl | rfl
        · exact hcut r hr .halted hsp
        · exact hcut r hr .left hsp
    have he : (windowRun M.tm s upd (r + 1) c τ).1 ≠ .exhausted := by
      intro he
      have := hp he
      omega
    have hst : (L.runFrom d' t).state = some (stop (windowRun M.tm s upd (r + 1) c τ).1) := by
      rw [hend]
      simp only [if_neg he]
    have htr : t = r := by
      by_contra hn
      exact hmin t (by omega) (stopped t _ he hst)
    refine ⟨he, ?_⟩
    rw [← htr, hend]
    simp only [if_neg he, htr]
  -- Transfer a clock frame to the runner. The body has the loop's fixed radius; the
  -- counter uses its delimited interval. This one calculation serves both clock exits.
  have bounds (tt : ℕ)
      (hp : ∀ u ≤ tt, R.runFrom d u = (H.runFrom a u).mapState (Sigma.mk true))
      (hf : ∀ u ≤ tt, ∃ v : ℕ,
        (∀ j : Fin (K + 1), (H.runFrom a u).workTapePos j.castSucc =
          (L.runFrom d' v).workTapePos j) ∧
        (H.runFrom a u).output = (L.runFrom d' v).output ∧
        (H.runFrom a u).workTapePos (Fin.last (K + 1)) ∈
          Finset.Icc (d.workTapePos (Fin.last (K + 1)) - 1)
            (d.workTapePos (Fin.last (K + 1)) + (w.length : ℤ))) :
      (∀ u ≤ tt, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (radius : ℤ)) ∧
      (∀ u ≤ tt, (R.runFrom d u).output = d.output) := by
    constructor
    · intro u hu j
      obtain ⟨v, hj, _, hc⟩ := hf u hu
      rw [hp u hu]
      induction j using Fin.lastCases with
      | last =>
        have hc' := Finset.mem_Icc.mp hc
        change |(H.runFrom a u).workTapePos (Fin.last (K + 1)) -
          d.workTapePos (Fin.last (K + 1))| ≤ (radius : ℤ)
        rw [abs_le]
        have hrad : 1 ≤ radius ∧ w.length ≤ radius := by dsimp [radius]; constructor <;> nlinarith
        constructor <;> omega
      | cast j =>
        change |(H.runFrom a u).workTapePos j.castSucc - d.workTapePos j.castSucc| ≤ _
        rw [hj j]
        exact (henv v j).trans (by
          exact_mod_cast (show CL * (recordLength M.k x.length s + 1) ≤ radius by
            dsimp [radius]
            nlinarith))
    · intro u hu
      obtain ⟨v, _, ho, _⟩ := hf u hu
      rw [hp u hu]
      exact ho.trans (hsil v)
  have avoid (b : Cfg (K + 2) (RecSym M.State T) Q
      (x.map (RecSym.digitEmb M.State T))) (hf : ∀ r, b.state ≠ some (finish r)) :
      ∀ e, (b.mapState (Sigma.mk true)).state ≠ some (wr_exit finish stop e) := by
    intro e he
    cases hb : b.state with
    | none => simp [Cfg.mapState, hb] at he
    | some q =>
      have he' : (⟨true, q⟩ : Σ b, wr_Ctrl Q b) = wr_exit finish stop e := by
        simpa [Cfg.mapState, hb] using he
      cases e with
      | exhausted => exact Bool.noConfusion (congrArg Sigma.fst he')
      | halted => exact hf _ (hb.trans (congrArg some (eq_of_heq (Sigma.mk.inj he').2)))
      | left => exact hf _ (hb.trans (congrArg some (eq_of_heq (Sigma.mk.inj he').2)))
  by_cases hex : ∃ r ≤ budget, (L.runFrom d' r).Stopped stopAt
  · let r := Nat.find hex
    have hr : r ≤ budget := (Nat.find_spec hex).1
    have hs : (L.runFrom d' r).Stopped stopAt := (Nat.find_spec hex).2
    have hmin : ∀ u < r, ¬(L.runFrom d' u).Stopped stopAt := by
      intro u hu hsu
      exact Nat.find_min hex hu ⟨by omega, hsu⟩
    obtain ⟨hneout, hrecord⟩ := first r hs hmin
    let out := (windowRun M.tm s upd (r + 1) c τ).1
    obtain ⟨tt, htt, w', hw', hrun, hcut, hframe⟩ := hfinish r hr hs hmin
    have hp (u : ℕ) (hu : u ≤ tt) : R.runFrom d u =
        (H.runFrom a u).mapState (Sigma.mk true) := by
      rw [hdeta]
      exact wr_prefix H timeout a tt (fun u hu r => (hcut u hu r).2) u hu
    obtain ⟨he, ho⟩ := bounds tt hp (fun u hu => by
      obtain ⟨v, _, hv, _, hvout, hcounter⟩ := hframe u hu
      exact ⟨v, fun j => (hv j).2, hvout, hcounter⟩)
    have houtstate : wr_exit finish stop out = ⟨true, finish (some (stop out))⟩ := by
      cases h : out with
      | halted => rfl
      | left => rfl
      | exhausted => exact False.elim (hneout h)
    refine ⟨tt, out, by dsimp only [budget] at hr; omega, ?_, ?_, he, ho, ?_, ?_, ?_⟩
    · rw [hp tt le_rfl, hrun, hrecord]
      change some (⟨true, finish (some (stop out))⟩ : Σ b, wr_Ctrl Q b) =
        some (wr_exit finish stop out)
      exact congrArg some houtstate.symm
    · intro u hu e
      rw [hp u hu.le]
      exact avoid _ (fun r => (hcut u hu r).1) e
    · have hspace := wr_space R d tt radius he
      convert hspace using 1
      dsimp only [radius]
      ring
    · intro N hN _
      exact congrArg Prod.fst (windowRun_stop_unique M.tm s upd (r + 1) N c τ hneout hN)
    · intro _
      refine ⟨r + 1, rfl, w', hw', ?_⟩
      let z := { d with
        state := some (wr_exit finish stop out)
        workTapes := fun j q =>
          if j = 0 ∧ d.workTapePos 0 ≤ q ∧
              q < d.workTapePos 0 + (recordLength M.k x.length s : ℤ)
            then fieldsTape (cfgRecord s (windowRun M.tm s upd (r + 1) c τ).2.1
              (windowRun M.tm s upd (r + 1) c τ).2.2) (q - d.workTapePos 0)
            else if j = Fin.last (K + 1) then
              wordPatch (d.workTapes j) (d.workTapePos j)
                (w'.map (RecSym.digitEmb M.State T)) q
            else d.workTapes j q }
      have hz := wr_clockCfg_eta z (finish (some (stop out))) (stop out)
        (by change some (wr_exit finish stop out) = _; rw [houtstate])
      have hbody : L.runFrom d' r =
          (⟨some (stop out), z.inputPos, fun j => z.workTapes j.castSucc,
            fun j => z.workTapePos j.castSucc, z.output⟩ :
              Cfg (K + 1) (RecSym M.State T) P (x.map (RecSym.digitEmb M.State T))) := by
        rw [hrecord]
        apply Cfg.ext <;> try rfl
        funext j q
        dsimp only [z, d']
        simp only [Fin.castSucc_eq_zero_iff, Fin.castSucc_ne_last, Fin.castSucc_zero, if_false]
      have hcounter : z.workTapes (Fin.last (K + 1)) =
          wordPatch (d.workTapes (Fin.last (K + 1))) (d.workTapePos (Fin.last (K + 1)))
            (w'.map (RecSym.digitEmb M.State T)) := by
        funext q
        dsimp only [z]
        rw [if_neg (by simp)]
        simp only [ite_true]
      change R.runFrom d tt = z
      rw [hp tt le_rfl, hrun]
      calc
        _ = (clockCfg (some (finish (some (stop out))))
            (⟨some (stop out), z.inputPos, fun j => z.workTapes j.castSucc,
              fun j => z.workTapePos j.castSucc, z.output⟩ :
                Cfg (K + 1) (RecSym M.State T) P (x.map (RecSym.digitEmb M.State T)))
            (z.workTapes (Fin.last (K + 1))) (z.workTapePos (Fin.last (K + 1)))).mapState
              (Sigma.mk true) := by rw [hbody, hcounter]
        _ = z := hz.symm
  · have hn : ∀ u ≤ budget, ¬(L.runFrom d' u).Stopped stopAt := by
      intro u hu hs
      exact hex ⟨u, hu, hs⟩
    obtain ⟨tt, htt, w', _, hrun, hcut, hframe⟩ := htimeout hn
    have hp (u : ℕ) (hu : u ≤ tt) : R.runFrom d u =
        (H.runFrom a u).mapState (Sigma.mk true) := by
      rw [hdeta]
      exact wr_prefix H timeout a tt (fun u hu r => (hcut u hu r).2) u hu
    have hdispatch : R.runFrom d (tt + 1) =
        (H.runFrom a tt).mapState (fun _ => (⟨false, ()⟩ : Σ b, wr_Ctrl Q b)) := by
      rw [hdeta]
      exact wr_timeout_dispatch H timeout a tt (L.runFrom d' budget).state
        (by rw [hrun]; rfl) (fun u hu r => (hcut u hu r).2)
    obtain ⟨he, ho⟩ := bounds tt hp (fun u hu => by
      obtain ⟨v, _, hv, _, hvout, hcounter⟩ := hframe u hu
      exact ⟨v, fun j => (hv j).2, hvout, hcounter⟩)
    have he' : ∀ u ≤ tt + 1, ∀ j,
        |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (radius : ℤ) := by
      intro u hu j
      by_cases hu' : u ≤ tt
      · exact he u hu' j
      · have : u = tt + 1 := by omega
        subst u
        rw [hdispatch]
        have h := he tt le_rfl j
        rwa [hp tt le_rfl] at h
    refine ⟨tt + 1, .exhausted, by omega, ?_, ?_, he', ?_, ?_, ?_, by simp⟩
    · rw [hdispatch, hrun]
      rfl
    · intro u hu e
      rw [hp u (by omega)]
      apply avoid
      intro q
      by_cases hu' : u < tt
      · exact (hcut u hu' q).1
      · have : u = tt := by omega
        subst u
        rw [hrun]
        change some (timeout _) ≠ some (finish q)
        exact fun h => hft q _ (Option.some.inj h).symm
    · intro u hu
      by_cases hu' : u ≤ tt
      · exact ho u hu'
      · have : u = tt + 1 := by omega
        subst u
        rw [hdispatch]
        have h := ho tt le_rfl
        rwa [hp tt le_rfl] at h
    · have hspace := wr_space R d (tt + 1) radius he'
      convert hspace using 1
      dsimp only [radius]
      ring
    · intro N hN htime
      obtain ⟨t, ht, _, _, hend⟩ := hevery N
      have hbudget : t ≤ budget := by
        have hmul : CL * N * (recordLength M.k x.length s + x.length + 1) ≤
            (CL + 1) * N * (recordLength M.k x.length s + x.length + 1) := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_right N (Nat.le_succ CL)
        exact ht.trans (hmul.trans htime)
      exact False.elim (hn t hbudget (stopped t _ hN (by
        rw [hend]
        simp only [if_neg hN])))


end Turing
