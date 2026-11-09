/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Run embedding for loop bodies

Generic machine-construction infrastructure shared by loop-body assemblies
(first customer: `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`):

* **safe runs** — a run segment that never visits an avoided (anchor) state
  strictly before its endpoint, closed under prepending a step and under
  concatenation: the shape of the `Turing.FinTM.exists_emitLoopTM` startup
  and round obligations;
* **output-prefix commutation** — the transition table never reads the
  output tape and the output is append-only, so prepending a fixed output
  prefix commutes with running the machine, and outputs only ever extend;
* **the tape-padding, state-injecting embedding** — a clean-call module over
  `m ≤ k` tapes runs inside a `k`-tape host on its first `m` work tapes with
  its states injected into the host's state type, step for step
  (`embed_step`/`embed_run`), while the padding tapes stay blank;
* **control steps** — a transition that only changes control (and possibly
  moves the input head) replaces just those configuration components. These
  two lemmas are private helpers of
  `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`, not exports of this
  module.

## Main definitions

* `Turing.SafeRun`, `Turing.padAction`, `Turing.embedCfg`.

## Main results

* `Turing.runFrom_output_prefix`, `Turing.runFrom_output_extends`,
  `Turing.embed_run`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the machine model these
  constructions assemble.)
-/

namespace Turing

open MultiTapeTM

variable {k m : ℕ} {B SS : Type} {x : List Bool}

/-! ### Safe runs

A run segment together with the promise that no strictly earlier
configuration sits at the avoided (anchor) state: the shape of the
`exists_emitLoopTM` startup and round obligations, closed under
single-step prepending and concatenation. -/

/-- A run from `c` to `c'` in exactly `t` steps that never visits the state
`avoid` strictly before `t`. -/
def SafeRun (H : MultiTapeTM k Bool B) (avoid : B)
    (c : Cfg k Bool B x) (t : ℕ) (c' : Cfg k Bool B x) : Prop :=
  H.runFrom c t = c' ∧ ∀ t' < t, (H.runFrom c t').state ≠ some avoid

/-- Safe runs are segments with one forbidden control state and a trivial head invariant. -/
private theorem safeRun_iff_segment {H : MultiTapeTM k Bool B} {avoid : B}
    {c c' : Cfg k Bool B x} {t : ℕ} :
    SafeRun H avoid c t c' ↔ Segment H {some avoid} (fun _ => True) c c' t := by
  simp only [SafeRun, segment_iff, Set.mem_singleton_iff, implies_true, and_true]

/-- The empty run is safe. -/
theorem SafeRun.zero {H : MultiTapeTM k Bool B} {avoid : B}
    {c : Cfg k Bool B x} : SafeRun H avoid c 0 c := by
  exact safeRun_iff_segment.mpr (Segment.zero True.intro)

/-- Prepend one non-avoided step to a safe run. -/
theorem SafeRun.cons {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t : ℕ} (hstep : H.step c = c₁)
    (hc : c.state ≠ some avoid) (h : SafeRun H avoid c₁ t c') :
    SafeRun H avoid c (t + 1) c' := by
  apply safeRun_iff_segment.mpr
  simpa only [Nat.add_comm 1 t] using
    (Segment.cons hstep (by simpa only [Set.mem_singleton_iff] using hc)
      True.intro (safeRun_iff_segment.mp h))

/-- Concatenate safe runs. -/
theorem SafeRun.trans {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t₁ t₂ : ℕ} (h₁ : SafeRun H avoid c t₁ c₁)
    (h₂ : SafeRun H avoid c₁ t₂ c') : SafeRun H avoid c (t₁ + t₂) c' := by
  exact safeRun_iff_segment.mpr
    (Segment.trans (safeRun_iff_segment.mp h₁) (safeRun_iff_segment.mp h₂))

/-! ### Output-prefix commutation

The transition table never reads the output tape and the output is
append-only, so prepending a fixed prefix to the output commutes with
running the machine. -/

/-- One step commutes with an output prefix. -/
theorem step_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) :
    H.step { c with output := pre ++ c.output } =
      { H.step c with output := pre ++ (H.step c).output } := by
  exact MultiTapeTM.step_output_prepend H c pre

/-- A run commutes with an output prefix. -/
theorem runFrom_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) (t : ℕ) :
    H.runFrom { c with output := pre ++ c.output } t =
      { H.runFrom c t with output := pre ++ (H.runFrom c t).output } := by
  exact MultiTapeTM.runFrom_output_prepend H c pre t

/-- The output tape is append-only along a run. -/
theorem runFrom_output_extends (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (t : ℕ) :
    ∃ o, (H.runFrom c t).output = c.output ++ o := by
  obtain ⟨o, ho⟩ := MultiTapeTM.output_prefix H c (Nat.zero_le t)
  exact ⟨o, by simpa only [MultiTapeTM.runFrom_zero] using ho.symm⟩

/-! ### Halted runs are stationary -/

/-- A halted configuration never changes. -/
theorem runFrom_of_halted (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} (h : c.state = none) (t : ℕ) : H.runFrom c t = c := by
  exact MultiTapeTM.runFrom_of_halt (tm := H) c h

/-- Every configuration strictly before a live endpoint is live. -/
theorem state_isSome_of_runFrom (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} {t : ℕ} {qf : B}
    (hf : (H.runFrom c t).state = some qf) {j : ℕ} (hj : j ≤ t) :
    ∃ q, (H.runFrom c j).state = some q := by
  have hl := MultiTapeTM.runFrom_state_ne_none_of_le H c t
    (by rw [hf]; exact Option.some_ne_none _) j hj
  cases hq : (H.runFrom c j).state with
  | some q => exact ⟨q, rfl⟩
  | none => exact False.elim (hl hq)

/-! ### Tape-padding, state-injecting embedding

A clean-call module over `m ≤ k` tapes runs inside the `k`-tape body on its
first `m` work tapes, with its states injected into the body's state type;
the extra tapes stay blank and their heads stay at the origin. -/

/-- Pad a module action to the host: act on the first `m` tapes, leave the
rest alone, and map the successor state. -/
def padAction (hmk : m ≤ k) (f : Option SS → Option B)
    (a : Action m Bool SS) : Action k Bool B where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < m then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := f a.state

/-- Embed a module configuration into the host. -/
def embedCfg (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) : Cfg k Bool B x where
  state := c.state.map inject
  inputPos := c.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < m then c.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i =>
    if h : (i : ℕ) < m then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- Embedding a canonical seam gives a canonical seam with the padded word
assignment. -/
theorem embedCfg_ofWords (hmk : m ≤ k) (inject : SS → B) (q : SS)
    (w : Fin m → List Bool) :
    embedCfg hmk inject (Cfg.ofWords (input := x) q w) =
      Cfg.ofWords (inject q)
        (fun i => if h : (i : ℕ) < m then w ⟨i, h⟩ else []) := by
  unfold embedCfg Cfg.ofWords
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : (i : ℕ) < m <;> simp [h]
  · funext i
    by_cases h : (i : ℕ) < m <;> simp [h]

/-- Applying a padded action to an embedded configuration embeds the applied
module configuration. -/
theorem padAction_apply (hmk : m ≤ k) (inject : SS → B)
    (a : Action m Bool SS) (c : Cfg m Bool SS x) (b : B) :
    (padAction hmk (Option.map inject) a).apply
        { embedCfg hmk inject c with state := some b } =
      embedCfg hmk inject (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : (i : ℕ) < m
    · simp only [Action.apply, padAction, embedCfg, dif_pos h]
    · simp only [Action.apply, padAction, embedCfg, dif_neg h]
  · funext i
    by_cases h : (i : ℕ) < m
    · simp only [Action.apply, padAction, embedCfg, dif_pos h]
    · simp only [Action.apply, padAction, embedCfg, dif_neg h]
      rfl

/-- The embedded configuration reads the module's work symbols on the first
`m` tapes. -/
theorem embedCfg_workTapeSymbols (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (b : B) :
    (fun i => ({ embedCfg hmk inject c with state := some b } :
        Cfg k Bool B x).workTapeSymbols (Fin.castLE hmk i)) =
      c.workTapeSymbols := by
  funext i
  have h : ((Fin.castLE hmk i : Fin k) : ℕ) < m := i.isLt
  simp only [Cfg.workTapeSymbols, embedCfg, dif_pos h]
  congr 1 <;> exact congrArg _ (Fin.eta i i.isLt) <;> rfl

/-- Embedding commutes with replacing the output. -/
theorem embedCfg_output (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (o : List Bool) :
    embedCfg hmk inject { c with output := o } =
      { embedCfg hmk inject c with output := o } := rfl

/-- A one-step run is a step. -/
theorem runFrom_one (H : MultiTapeTM k Bool B) (c : Cfg k Bool B x) :
    H.runFrom c 1 = H.step c := by
  simp [MultiTapeTM.runFrom]

/-- One host step at a state behaving like the module's state `q` tracks one
module step.
**Proof sketch.** Both steps dispatch their transition tables on live states;
the embedded configuration reads the same input symbol and, through
`embedCfg_workTapeSymbols`, the same work symbols, so the host's action is
the padded module action, and `padAction_apply` pushes it through the
embedding. -/
theorem embed_step (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
    (H : MultiTapeTM k Bool B) (inject : SS → B)
    (c : Cfg m Bool SS x) (q : SS) (hq : c.state = some q) (b : B)
    (htr : ∀ inp work, H.tr b inp work =
      padAction hmk (Option.map inject)
        (M.tr q inp (fun i => work (Fin.castLE hmk i)))) :
    H.step { embedCfg hmk inject c with state := some b } =
      embedCfg hmk inject (M.step c) := by
  have hIS : ({ embedCfg hmk inject c with state := some b } :
      Cfg k Bool B x).inputSymbol = c.inputSymbol := rfl
  have hstepL : H.step { embedCfg hmk inject c with state := some b } =
      (H.tr b ({ embedCfg hmk inject c with state := some b } :
          Cfg k Bool B x).inputSymbol
        ({ embedCfg hmk inject c with state := some b } :
          Cfg k Bool B x).workTapeSymbols).apply
        { embedCfg hmk inject c with state := some b } := rfl
  have hstepR : M.step c = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hq]
  rw [hstepL, hstepR, htr, hIS, embedCfg_workTapeSymbols]
  exact padAction_apply hmk inject _ c b

/-- A module run strictly inside the avoided exit embeds step-for-step into
the host, provided the host's transition at every injected live state is the
padded module transition.
**Proof sketch.** Induction on the run length: every strictly earlier
configuration is live and off the exit by hypothesis, so `embed_step`
transports each step. -/
theorem embed_run (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
    (H : MultiTapeTM k Bool B) (inject : SS → B) (ex : SS)
    (htr : ∀ q : SS, q ≠ ex → ∀ inp work,
      H.tr (inject q) inp work =
        padAction hmk (Option.map inject)
          (M.tr q inp (fun i => work (Fin.castLE hmk i))))
    (c : Cfg m Bool SS x) (t : ℕ)
    (hstate : ∀ j < t, ∃ q, (M.runFrom c j).state = some q ∧ q ≠ ex) :
    H.runFrom (embedCfg hmk inject c) t = embedCfg hmk inject (M.runFrom c t) := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    obtain ⟨q, hq, hqex⟩ := hstate 0 (by omega)
    simp only [runFrom_zero] at hq
    have hstep : H.step (embedCfg hmk inject c) = embedCfg hmk inject (M.step c) := by
      have hc : { embedCfg hmk inject c with state := some (inject q) } =
          embedCfg hmk inject c := by
        simp [embedCfg, hq]
      rw [← hc]
      exact embed_step hmk M H inject c q hq (inject q) (htr q hqex)
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, hstep]
    exact ih (M.step c) (fun j hj => by
      have := hstate (j + 1) (by omega)
      simpa [runFrom, Function.iterate_succ_apply] using this)


end Turing
