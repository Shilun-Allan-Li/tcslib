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
lemmas are proved; the two machine contracts are sorried with their proof sketches.

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
  step-clocked runner (sorried).

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
`Turing.MultiTapeTM.runFrom_add`. -/
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
  sorry

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
`[cp - 1, cp + |w|]`. -/
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
  sorry

end Turing
