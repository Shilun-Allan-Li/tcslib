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
# The emit-iteration body

The host machine behind `Complexity.polyTimeComputable_emitIter` (in
`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): one finite machine that, on
input `w`, concatenates the chunks `e (g^[i] w)` for `i = 0, …, R |w|`, in
polynomial time, given machines for the step `g` and the chunk `e` and a
polynomial length envelope for the orbit of `g`.

It is an instance of `Turing.FinTM.exists_emitLoopTM`.  The body machine's
startup copies the native input onto work tape zero (the loop's round state)
and rewinds both heads to the canonical seam; each round is two clean calls
on the tape-resident state word — an emit-mode call
(`Turing.FinTM.exists_emitCallTM`) forwarding the chunk `e s` to the physical
output, then an install-mode call (`Turing.FinTM.exists_installCallTM`)
replacing the word by `g s` — glued by two control states.  The clean-call
modules run on the body's first tapes through a tape-padding, state-injecting
embedding (`padAction`/`embedCfg` below); the round assembly commutes the
already-emitted chunk past the install call with an output-prefix lemma.

## Main definitions

None — the body machine, its embedding, and the phase configurations are
private to this file.

## Main results

* `Turing.FinTM.exists_emitIterTM` — the finite machine computing the
  concatenated chunks of a polynomially clocked iteration, within a
  polynomial budget in the `C·(n+1)^c` normal form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; §7.3–§7.4: the folklore
  "simulate the machine on each block" loop this host implements.)
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
private def SafeRun (H : MultiTapeTM k Bool B) (avoid : B)
    (c : Cfg k Bool B x) (t : ℕ) (c' : Cfg k Bool B x) : Prop :=
  H.runFrom c t = c' ∧ ∀ t' < t, (H.runFrom c t').state ≠ some avoid

private theorem SafeRun.zero {H : MultiTapeTM k Bool B} {avoid : B}
    {c : Cfg k Bool B x} : SafeRun H avoid c 0 c :=
  ⟨rfl, fun t' ht' => absurd ht' (by omega)⟩

/-- Prepend one non-avoided step to a safe run. -/
private theorem SafeRun.cons {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t : ℕ} (hstep : H.step c = c₁)
    (hc : c.state ≠ some avoid) (h : SafeRun H avoid c₁ t c') :
    SafeRun H avoid c (t + 1) c' := by
  have hone : H.runFrom c 1 = c₁ := by
    simp [runFrom, hstep]
  refine ⟨?_, ?_⟩
  · rw [show t + 1 = 1 + t by omega, runFrom_add, hone]
    exact h.1
  · intro t' ht'
    cases t' with
    | zero => simpa using hc
    | succ u =>
      rw [show u + 1 = 1 + u by omega, runFrom_add, hone]
      exact h.2 u (by omega)

/-- Concatenate safe runs. -/
private theorem SafeRun.trans {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t₁ t₂ : ℕ} (h₁ : SafeRun H avoid c t₁ c₁)
    (h₂ : SafeRun H avoid c₁ t₂ c') : SafeRun H avoid c (t₁ + t₂) c' := by
  refine ⟨?_, ?_⟩
  · rw [runFrom_add, h₁.1]
    exact h₂.1
  · intro t' ht'
    by_cases hlt : t' < t₁
    · exact h₁.2 t' hlt
    · obtain ⟨u, rfl⟩ : ∃ u, t' = t₁ + u := ⟨t' - t₁, by omega⟩
      rw [runFrom_add, h₁.1]
      exact h₂.2 u (by omega)

/-! ### Output-prefix commutation

The transition table never reads the output tape and the output is
append-only, so prepending a fixed prefix to the output commutes with
running the machine. -/

/-- One step commutes with an output prefix. -/
private theorem step_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) :
    H.step { c with output := pre ++ c.output } =
      { H.step c with output := pre ++ (H.step c).output } := by
  obtain ⟨st, pos, tapes, tpos, out⟩ := c
  cases st with
  | none => rfl
  | some q =>
    have hws : (⟨some q, pos, tapes, tpos, pre ++ out⟩ : Cfg k Bool B x).workTapeSymbols =
        (⟨some q, pos, tapes, tpos, out⟩ : Cfg k Bool B x).workTapeSymbols := rfl
    simp [MultiTapeTM.step, Action.apply, Cfg.inputSymbol, hws, List.append_assoc]

/-- A run commutes with an output prefix. -/
private theorem runFrom_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) (t : ℕ) :
    H.runFrom { c with output := pre ++ c.output } t =
      { H.runFrom c t with output := pre ++ (H.runFrom c t).output } := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, step_output_prefix]
    exact ih (H.step c)

/-- The output tape is append-only along a run. -/
private theorem runFrom_output_extends (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (t : ℕ) :
    ∃ o, (H.runFrom c t).output = c.output ++ o := by
  induction t generalizing c with
  | zero => exact ⟨[], by simp⟩
  | succ t ih =>
    rw [runFrom_succ_eq_step]
    obtain ⟨o, ho⟩ := ih (H.step c)
    unfold MultiTapeTM.step at ho ⊢
    cases hq : c.state with
    | none =>
      rw [hq] at ho
      exact ⟨o, ho⟩
    | some q =>
      rw [hq] at ho
      refine ⟨(H.tr q c.inputSymbol c.workTapeSymbols).output.toList ++ o, ?_⟩
      rw [ho]
      simp [Action.apply]

/-! ### Halted runs are stationary -/

private theorem runFrom_of_halted (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} (h : c.state = none) (t : ℕ) : H.runFrom c t = c := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [runFrom_add, ih]
    simp [runFrom, step_of_halt h]

/-- Every configuration strictly before a live endpoint is live. -/
private theorem state_isSome_of_runFrom (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} {t : ℕ} {qf : B}
    (hf : (H.runFrom c t).state = some qf) {j : ℕ} (hj : j ≤ t) :
    ∃ q, (H.runFrom c j).state = some q := by
  cases hq : (H.runFrom c j).state with
  | some q => exact ⟨q, rfl⟩
  | none =>
    exfalso
    have hstat : H.runFrom c t = H.runFrom c j := by
      obtain ⟨u, rfl⟩ : ∃ u, t = j + u := ⟨t - j, by omega⟩
      rw [runFrom_add, runFrom_of_halted H hq]
    rw [hstat, hq] at hf
    exact Option.noConfusion hf

/-! ### Tape-padding, state-injecting embedding

A clean-call module over `m ≤ k` tapes runs inside the `k`-tape body on its
first `m` work tapes, with its states injected into the body's state type;
the extra tapes stay blank and their heads stay at the origin. -/

/-- Pad a module action to the host: act on the first `m` tapes, leave the
rest alone, and map the successor state. -/
private def padAction (hmk : m ≤ k) (f : Option SS → Option B)
    (a : Action m Bool SS) : Action k Bool B where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < m then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := f a.state

/-- Embed a module configuration into the host. -/
private def embedCfg (hmk : m ≤ k) (inject : SS → B)
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
private theorem embedCfg_ofWords (hmk : m ≤ k) (inject : SS → B) (q : SS)
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
private theorem padAction_apply (hmk : m ≤ k) (inject : SS → B)
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
private theorem embedCfg_workTapeSymbols (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (b : B) :
    (fun i => ({ embedCfg hmk inject c with state := some b } :
        Cfg k Bool B x).workTapeSymbols (Fin.castLE hmk i)) =
      c.workTapeSymbols := by
  funext i
  have h : ((Fin.castLE hmk i : Fin k) : ℕ) < m := i.isLt
  simp only [Cfg.workTapeSymbols, embedCfg, dif_pos h]
  congr 1 <;> exact congrArg _ (Fin.eta i i.isLt) <;> rfl

/-- Embedding commutes with replacing the output. -/
private theorem embedCfg_output (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (o : List Bool) :
    embedCfg hmk inject { c with output := o } =
      { embedCfg hmk inject c with output := o } := rfl

/-- A one-step run is a step. -/
private theorem runFrom_one (H : MultiTapeTM k Bool B) (c : Cfg k Bool B x) :
    H.runFrom c 1 = H.step c := by
  simp [MultiTapeTM.runFrom]

/-- One host step at a state behaving like the module's state `q` tracks one
module step.
**Proof sketch.** Both steps dispatch their transition tables on live states;
the embedded configuration reads the same input symbol and, through
`embedCfg_workTapeSymbols`, the same work symbols, so the host's action is
the padded module action, and `padAction_apply` pushes it through the
embedding. -/
private theorem embed_step (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
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
private theorem embed_run (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
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

/-! ### The body machine

Startup copies the native input onto work tape zero and rewinds both heads;
a round is the emit-mode call (whose first action the anchor itself performs,
so an entry state equal to the exit state still runs), a control handoff, the
install-mode call (likewise inlined into `gStart`), and a control return to
the anchor. -/

/-- Control states of the emit-iteration body. -/
private inductive BodyState (SE SG : Type) where
  | copy
  | rwTape
  | rwInput0
  | rwInput
  | anchor
  | callE (q : SE)
  | gStart
  | callG (q : SG)
  deriving DecidableEq

private instance {SE SG : Type} [Fintype SE] [Fintype SG] :
    Fintype (BodyState SE SG) := derive_fintype% _

/-- The emit-iteration body: copy the input onto tape zero, then alternate
the two clean-call modules under the anchored round discipline. -/
private def emitIterBody (Em Gm : FinTM Bool) (hek : 0 < Em.k)
    (ee ex : Em.State) (ge gx : Gm.State) : FinTM Bool where
  k := max Em.k Gm.k
  State := BodyState Em.State Gm.State
  tm := {
    q₀ := .copy
    tr := fun q inp work => match q with
      | .copy => match inp with
        | some s => ⟨.pos,
            fun i => if (i : ℕ) = 0 then (some (some s), 1) else (none, 0),
            none, some .copy⟩
        | none => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0),
            none, some .rwTape⟩
      | .rwTape =>
        match work ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left _ _)⟩ with
        | some _ => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0),
            none, some .rwTape⟩
        | none => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, 1) else (none, 0),
            none, some .rwInput0⟩
      | .rwInput0 => FinTM.controlAction .neg (some .rwInput)
      | .rwInput => match inp with
        | some _ => FinTM.controlAction .neg (some .rwInput)
        | none => FinTM.controlAction .pos (some .anchor)
      | .anchor =>
        padAction (Nat.le_max_left _ _) (Option.map .callE)
          (Em.tm.tr ee inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i)))
      | .callE q =>
        if q = ex then FinTM.controlAction 0 (some .gStart)
        else
          padAction (Nat.le_max_left _ _) (Option.map .callE)
            (Em.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i)))
      | .gStart =>
        padAction (Nat.le_max_right _ _) (Option.map .callG)
          (Gm.tm.tr ge inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i)))
      | .callG q =>
        if q = gx then FinTM.controlAction 0 (some .anchor)
        else
          padAction (Nat.le_max_right _ _) (Option.map .callG)
            (Gm.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i))) }

/-- A pure control transition replaces only the state. -/
private theorem control_step {H : MultiTapeTM k Bool B} {q r : B}
    (h : ∀ inp work, H.tr q inp work = FinTM.controlAction 0 (some r))
    {c : Cfg k Bool B x} (hc : c.state = some q) :
    H.step c = { c with state := some r } := by
  have hs : H.step c = (H.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hc]
  rw [hs, h]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_ <;>
    simp [FinTM.controlAction, Action.apply]

section Body

variable (Em Gm : FinTM Bool) (ee ex : Em.State) (ge gx : Gm.State)

/-- Embedding an `Em`-seam into the body gives a body seam: tape zero's word
survives and the padding tapes are blank on both sides. -/
private theorem embed_ofWords_left (hek : 0 < Em.k) (s : List Bool) :
    embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
        (Cfg.ofWords (input := x) ee (stateWord Em.k s)) =
      Cfg.ofWords (BodyState.callE ee) (stateWord (max Em.k Gm.k) s) := by
  rw [embedCfg_ofWords]
  congr 1
  funext i
  by_cases h : (i : ℕ) < Em.k
  · simp [stateWord, h]
  · have h0 : ¬ (i : ℕ) = 0 := fun hz => h (hz ▸ hek)
    simp [stateWord, h, h0]

/-- Embedding a `Gm`-seam into the body gives a body seam, provided `Gm` has
a genuine tape (otherwise tape zero's word would be lost). -/
private theorem embed_ofWords_right (hgk : 0 < Gm.k) (s : List Bool) :
    embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
        (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) =
      Cfg.ofWords (BodyState.callG ge) (stateWord (max Em.k Gm.k) s) := by
  rw [embedCfg_ofWords]
  congr 1
  funext i
  by_cases h : (i : ℕ) < Gm.k
  · simp [stateWord, h]
  · have h0 : ¬ (i : ℕ) = 0 := fun hz => h (hz ▸ hgk)
    simp [stateWord, h, h0]

/-- **The round segment.** From the anchor seam carrying `s`, the body runs
the emit-mode module (emitting `es`), hands control to the install-mode
module (installing `gs`), and returns to the anchor seam, in positive time,
without visiting the anchor strictly inside.
**Proof sketch.** The anchor itself fires the emit module's first action, so
an entry state equal to the exit state still runs; `embed_run` transports the
rest of the emit run, landing at the handoff state with the chunk emitted and
the word preserved.  One control step enters `gStart`, which fires the
install module's first action; the install run is transported likewise, with
the already-emitted chunk commuted past it by `runFrom_output_prefix` (the
install module's own output stays empty along the run, by the append-only
output).  One final control step re-enters the anchor carrying the stepped
word.  The anchor-exclusion clause reads the visited state off the
appropriate phase equality: an injected call state, or a control state,
never the anchor. -/
private theorem body_round (hek : 0 < Em.k) (hgk : 0 < Gm.k) (s es gs : List Bool)
    (tE : ℕ) (htE : 0 < tE)
    (hEfirst : ∀ t', 0 < t' → t' < tE →
      (Em.tm.runFrom (Cfg.ofWords (input := x) ee (stateWord Em.k s)) t').state ≠
        some ex)
    (hErun : Em.tm.runFrom (Cfg.ofWords (input := x) ee (stateWord Em.k s)) tE =
      { Cfg.ofWords ex (stateWord Em.k s) with output := es })
    (tG : ℕ) (htG : 0 < tG)
    (hGfirst : ∀ t', 0 < t' → t' < tG →
      (Gm.tm.runFrom (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) t').state ≠
        some gx)
    (hGrun : Gm.tm.runFrom (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) tG =
      Cfg.ofWords gx (stateWord Gm.k gs)) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.runFrom
        (Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) s))
        (tE + 1 + tG + 1) =
      { Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) gs)
          with output := es } ∧
    ∀ t', 0 < t' → t' < tE + 1 + tG + 1 →
      ((emitIterBody Em Gm hek ee ex ge gx).tm.runFrom
        (Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) s))
          t').state ≠ some .anchor := by
  set H := (emitIterBody Em Gm hek ee ex ge gx).tm with hH
  set c₀ : Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
    Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) s) with hc₀
  set subc₀ : Cfg Em.k Bool Em.State x := Cfg.ofWords ee (stateWord Em.k s) with hsubc₀
  set subg₀ : Cfg Gm.k Bool Gm.State x := Cfg.ofWords ge (stateWord Gm.k s) with hsubg₀
  have htrE : ∀ q : Em.State, q ≠ ex → ∀ inp work,
      H.tr (.callE q) inp work =
        padAction (Nat.le_max_left Em.k Gm.k) (Option.map .callE)
          (Em.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i))) := by
    intro q hq inp work
    simp [hH, emitIterBody, hq]
  have htrG : ∀ q : Gm.State, q ≠ gx → ∀ inp work,
      H.tr (.callG q) inp work =
        padAction (Nat.le_max_right Em.k Gm.k) (Option.map .callG)
          (Gm.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i))) := by
    intro q hq inp work
    simp [hH, emitIterBody, hq]
  -- the first module step, fired from the anchor
  have hstep₁ : H.step c₀ =
      embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
        (Em.tm.step subc₀) := by
    have h := embed_step (Nat.le_max_left Em.k Gm.k) Em.tm H
      (BodyState.callE (SG := Gm.State)) subc₀ ee rfl .anchor (fun inp work => rfl)
    have hcfg : ({ embedCfg (Nat.le_max_left Em.k Gm.k)
        (BodyState.callE (SG := Gm.State)) subc₀ with
        state := some .anchor } : Cfg (max Em.k Gm.k) Bool _ x) = c₀ := by
      rw [hsubc₀, embed_ofWords_left Em Gm ee hek]
      rfl
    rw [← hcfg]
    exact h
  -- the module chain after the first step
  have hEsome : ∀ j ≤ tE, ∃ q, (Em.tm.runFrom subc₀ j).state = some q := by
    intro j hj
    exact state_isSome_of_runFrom Em.tm (by rw [hErun]; rfl) hj
  have hone : Em.tm.runFrom subc₀ 1 = Em.tm.step subc₀ := by
    simp [MultiTapeTM.runFrom]
  have hEchain : ∀ u ≤ tE - 1,
      H.runFrom c₀ (1 + u) =
        embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
          (Em.tm.runFrom subc₀ (1 + u)) := by
    intro u hu
    rw [runFrom_add, runFrom_one, hstep₁]
    rw [embed_run (Nat.le_max_left Em.k Gm.k) Em.tm H
      (BodyState.callE (SG := Gm.State)) ex htrE (Em.tm.step subc₀) u ?hstates]
    · rw [runFrom_add, hone]
    case hstates =>
      intro j hj
      have hj1 : 1 + j ≤ tE := by omega
      obtain ⟨q, hq⟩ := hEsome (1 + j) hj1
      rw [runFrom_add, hone] at hq
      refine ⟨q, hq, ?_⟩
      intro hqex
      subst hqex
      have := hEfirst (1 + j) (by omega) (by omega)
      rw [runFrom_add, hone] at this
      exact this hq
  -- checkpoint A: after tE steps, at the handoff state with the chunk emitted
  have hA : H.runFrom c₀ tE =
      { Cfg.ofWords (BodyState.callE ex) (stateWord (max Em.k Gm.k) s)
          with output := es } := by
    have h := hEchain (tE - 1) le_rfl
    rw [show 1 + (tE - 1) = tE from by omega] at h
    rw [h, hErun]
    rw [embedCfg_output, embed_ofWords_left Em Gm ex hek]
  -- checkpoint B: the control handoff
  have hB : H.runFrom c₀ (tE + 1) =
      { Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s)
          with output := es } := by
    rw [runFrom_add, hA, runFrom_one, control_step (q := BodyState.callE ex) ?_ rfl]
    · rfl
    · intro inp work
      simp [hH, emitIterBody]
  -- the install chain, lifted along the emitted prefix
  have hstep₂ : H.step (Cfg.ofWords (BodyState.gStart (SE := Em.State) (SG := Gm.State))
        (stateWord (max Em.k Gm.k) s)) =
      embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
        (Gm.tm.step subg₀) := by
    have h := embed_step (Nat.le_max_right Em.k Gm.k) Gm.tm H
      (BodyState.callG (SE := Em.State)) subg₀ ge rfl
      (BodyState.gStart (SE := Em.State) (SG := Gm.State)) (fun inp work => rfl)
    have hcfg : ({ embedCfg (Nat.le_max_right Em.k Gm.k)
        (BodyState.callG (SE := Em.State)) subg₀ with
        state := some (BodyState.gStart (SE := Em.State) (SG := Gm.State)) } :
          Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) =
        Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s) := by
      rw [hsubg₀, embed_ofWords_right Em Gm ge hgk]
      rfl
    rw [← hcfg]
    exact h
  have hGsome : ∀ j ≤ tG, ∃ q, (Gm.tm.runFrom subg₀ j).state = some q := by
    intro j hj
    exact state_isSome_of_runFrom Gm.tm (by rw [hGrun]; rfl) hj
  have honeG : Gm.tm.runFrom subg₀ 1 = Gm.tm.step subg₀ := by
    simp [MultiTapeTM.runFrom]
  have hGchain : ∀ u ≤ tG - 1,
      H.runFrom (Cfg.ofWords (BodyState.gStart (SE := Em.State) (SG := Gm.State)) (stateWord (max Em.k Gm.k) s)) (1 + u) =
        embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
          (Gm.tm.runFrom subg₀ (1 + u)) := by
    intro u hu
    rw [runFrom_add, runFrom_one, hstep₂]
    rw [embed_run (Nat.le_max_right Em.k Gm.k) Gm.tm H
      (BodyState.callG (SE := Em.State)) gx htrG (Gm.tm.step subg₀) u ?hstatesG]
    · rw [runFrom_add, honeG]
    case hstatesG =>
      intro j hj
      have hj1 : 1 + j ≤ tG := by omega
      obtain ⟨q, hq⟩ := hGsome (1 + j) hj1
      rw [runFrom_add, honeG] at hq
      refine ⟨q, hq, ?_⟩
      intro hqex
      subst hqex
      have := hGfirst (1 + j) (by omega) (by omega)
      rw [runFrom_add, honeG] at this
      exact this hq
  have hGout : ∀ u ≤ tG, 1 ≤ u →
      H.runFrom c₀ (tE + 1 + u) =
        { embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
            (Gm.tm.runFrom subg₀ u) with output := es } := by
    intro u hu h1u
    rw [show tE + 1 + u = (tE + 1) + u from rfl, runFrom_add, hB]
    have hpre : ({ Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s)
        with output := es } : Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) =
        { (Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s) :
            Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) with
          output := es ++ (Cfg.ofWords (input := x)
            (BodyState.gStart (SE := Em.State) (SG := Gm.State))
            (stateWord (max Em.k Gm.k) s)).output } := by
      simp [Cfg.ofWords]
    have hsubout : (Gm.tm.runFrom subg₀ u).output = [] := by
      obtain ⟨o2, h2⟩ := runFrom_output_extends Gm.tm (Gm.tm.runFrom subg₀ u) (tG - u)
      rw [← runFrom_add, show u + (tG - u) = tG from by omega, hGrun] at h2
      have : ([] : List Bool) = (Gm.tm.runFrom subg₀ u).output ++ o2 := h2
      exact (List.append_eq_nil_iff.mp this.symm).1
    rw [hpre, runFrom_output_prefix]
    obtain ⟨u', rfl⟩ : ∃ u', u = 1 + u' := ⟨u - 1, by omega⟩
    rw [hGchain u' (by omega)]
    rw [show (embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
      (Gm.tm.runFrom subg₀ (1 + u'))).output = [] from hsubout, List.append_nil]
  -- checkpoint C and the final control return
  have hC : H.runFrom c₀ (tE + 1 + tG) =
      { Cfg.ofWords (BodyState.callG gx) (stateWord (max Em.k Gm.k) gs)
          with output := es } := by
    rw [hGout tG le_rfl (by omega), hGrun, embed_ofWords_right Em Gm gx hgk]
  constructor
  · rw [show tE + 1 + tG + 1 = (tE + 1 + tG) + 1 from rfl, runFrom_add, hC,
      runFrom_one, control_step (q := BodyState.callG gx) ?_ rfl]
    · rfl
    · intro inp work
      simp [hH, emitIterBody]
  · intro t' ht'0 ht'
    rcases lt_trichotomy t' (tE + 1) with hlt | heq | hgt
    · rcases Nat.lt_or_ge t' tE with hltE | hgeE
      · obtain ⟨u, rfl⟩ : ∃ u, t' = 1 + u := ⟨t' - 1, by omega⟩
        rw [hEchain u (by omega)]
        obtain ⟨q, hq⟩ := hEsome (1 + u) (by omega)
        simp [embedCfg, hq]
      · have he : t' = tE := by omega
        subst he
        rw [hA]
        simp [Cfg.ofWords]
    · subst heq
      rw [hB]
      simp [Cfg.ofWords]
    · obtain ⟨u, rfl⟩ : ∃ u, t' = tE + 1 + u := ⟨t' - (tE + 1), by omega⟩
      rw [hGout u (by omega) (by omega)]
      obtain ⟨q, hq⟩ := hGsome u (by omega)
      simp [embedCfg, hq]

/-- **The startup segment.** From its initial configuration the body copies
the input onto tape zero, rewinds both heads, and enters the anchor seam
carrying the input, within `3·|x| + 4` steps and without visiting the anchor
earlier. -/
private theorem body_start (hek : 0 < Em.k) :
    SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
      ((emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x) (3 * x.length + 4)
      (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
  sorry

end Body

end Turing
