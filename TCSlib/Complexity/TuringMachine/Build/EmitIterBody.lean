/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed

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

/-- A moving control transition replaces the state and moves the input head. -/
private theorem control_step' {H : MultiTapeTM k Bool B} {q r : B} {mv : SignType}
    (h : ∀ inp work, H.tr q inp work = FinTM.controlAction mv (some r))
    {c : Cfg k Bool B x} (hc : c.state = some q) :
    H.step c = { c with
      state := some r
      inputPos := moveInputPos c.inputPos mv } := by
  have hs : H.step c = (H.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hc]
  rw [hs, h]
  refine Cfg.ext rfl rfl ?_ ?_ ?_ <;>
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

/-! #### The startup copier -/

/-- The copy-phase configuration: the first `i` input symbols already written
on tape zero, both heads past them. -/
private def copyCfg (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩,
    fun j => if (j : ℕ) = 0 then FinTM.bufferTape (x.take i) else fun _ => none,
    fun j => if (j : ℕ) = 0 then (i : ℤ) else 0, []⟩

/-- A rewind-phase configuration: the whole input on tape zero, the input
head at `p`, the tape-zero head at `z`. -/
private def fullCfg (x : List Bool) (st : BodyState Em.State Gm.State)
    (p : ℕ) (hp : p < x.length + 2) (z : ℤ) :
    Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
  ⟨some st, ⟨p, hp⟩,
    fun j => if (j : ℕ) = 0 then FinTM.bufferTape x else fun _ => none,
    fun j => if (j : ℕ) = 0 then z else 0, []⟩

/-- The body's initial configuration is the empty copy configuration. -/
private theorem initCfg_eq_copyCfg (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x =
      copyCfg Em Gm x 0 (Nat.zero_le _) := by
  refine Cfg.ext rfl (Fin.ext (by simp [copyCfg])) ?_ ?_ rfl
  · funext j
    by_cases hj : (j : ℕ) = 0 <;>
      simp [copyCfg, emitIterBody, hj, MultiTapeTM.initCfg, Cfg.init]
  · funext j
    by_cases hj : (j : ℕ) = 0 <;>
      simp [copyCfg, emitIterBody, hj, MultiTapeTM.initCfg, Cfg.init]

/-- One copy step: read the next input symbol, write it, advance both heads.
**Proof sketch.** The input symbol under the head is the `i`-th input bit;
the applied action writes it at tape-zero cell `i` (`bufferTape_append`
extends the copied prefix) and moves both heads right. -/
private theorem copy_step (hek : 0 < Em.k) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x i (le_of_lt hi)) =
      copyCfg Em Gm x (i + 1) hi := by
  have hinp : (copyCfg Em Gm x i (le_of_lt hi)).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [copyCfg]; omega) hi
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x i (le_of_lt hi)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .copy
        (copyCfg Em Gm x i (le_of_lt hi)).inputSymbol
        (copyCfg Em Gm x i (le_of_lt hi)).workTapeSymbols).apply
        (copyCfg Em Gm x i (le_of_lt hi)) := rfl
  rw [h1, hinp]
  have htake : x.take (i + 1) = x.take i ++ [x[i]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hi]
    rfl
  have hlen : ((x.take i).length : ℤ) = (i : ℤ) := by
    simp [List.length_take, Nat.min_eq_left (le_of_lt hi)]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    rfl
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, hj, if_pos]
      rw [htake, FinTM.bufferTape_append, hlen]
    · simp [emitIterBody, Action.apply, copyCfg, hj]
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, hj, if_pos]
      simp only [SignType.coe_one]
      omega
    · simp [emitIterBody, Action.apply, copyCfg, hj]

/-- The copy phase ends at the right input boundary and starts the tape
rewind.
**Proof sketch.** At the right boundary the input read is blank, so the
copy state's other branch fires: the input head stays, tape zero (now
holding the whole input, `List.take_length`) steps left. -/
private theorem copy_end (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x x.length le_rfl) =
      fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((x.length : ℤ) - 1) := by
  have hinp : (copyCfg Em Gm x x.length le_rfl).inputSymbol = none := by
    have h := FinTM.inputSymbol_at (copyCfg Em Gm x x.length le_rfl) x.length le_rfl
      (by simp [copyCfg])
    simpa using h
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x x.length le_rfl) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .copy
        (copyCfg Em Gm x x.length le_rfl).inputSymbol
        (copyCfg Em Gm x x.length le_rfl).workTapeSymbols).apply
        (copyCfg Em Gm x x.length le_rfl) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, fullCfg, hj, if_pos]
      rw [List.take_length]
    · simp [emitIterBody, Action.apply, copyCfg, fullCfg, hj]
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, fullCfg, hj, if_pos,
        SignType.neg_eq_neg_one, SignType.coe_neg_one]
      omega
    · simp [emitIterBody, Action.apply, copyCfg, fullCfg, hj]

/-- One tape-rewind step over a written cell.
**Proof sketch.** The tape-zero read at cell `j` is the `j`-th copied bit,
so the rewind state keeps moving left; only the head position changes. -/
private theorem rwTape_some (hek : 0 < Em.k) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) =
      fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((j : ℤ) - 1) := by
  have hw : (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols
      ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left Em.k Gm.k)⟩ = some x[j] := by
    simp only [fullCfg, Cfg.workTapeSymbols]
    simp [List.getElem?_eq_getElem hj]
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).inputSymbol
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols).apply
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) := rfl
  have htr : (emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).inputSymbol
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols =
      ⟨0, fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0), none, some .rwTape⟩ := by
    simp only [emitIterBody]
    rw [hw]
  rw [h1, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;> simp [Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp only [Action.apply, fullCfg, hi, if_pos, SignType.neg_eq_neg_one,
        SignType.coe_neg_one]
      omega
    · simp [Action.apply, fullCfg, hi]

/-- The tape rewind reaches the left blank and turns the head back to the
origin.
**Proof sketch.** Cell `-1` is blank (`bufferTape_left`), so the rewind
state's blank branch fires: the head steps right to the origin and control
moves to the input rewind. -/
private theorem rwTape_none (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) =
      fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0 := by
  have hw : (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols
      ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left Em.k Gm.k)⟩ = none := by
    simp only [fullCfg, Cfg.workTapeSymbols]
    simp
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).inputSymbol
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols).apply
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) := rfl
  have htr : (emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).inputSymbol
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols =
      ⟨0, fun i => if (i : ℕ) = 0 then (none, 1) else (none, 0), none, some .rwInput0⟩ := by
    simp only [emitIterBody]
    rw [hw]
  rw [h1, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;> simp [Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp only [Action.apply, fullCfg, hi, if_pos, SignType.coe_one]
      omega
    · simp [Action.apply, fullCfg, hi]

/-- The input rewind's unconditional first move. -/
private theorem rwIn0_step (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0) =
      fullCfg Em Gm x .rwInput x.length (by omega) 0 := by
  rw [control_step' (mv := .neg) (r := BodyState.rwInput) (fun _ _ => rfl) rfl]
  refine Cfg.ext rfl ?_ rfl rfl rfl
  show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) .neg = _
  rw [moveInputPos_neg_of_ne_left _ (by
    intro h
    have := congrArg Fin.val h
    simp at this)]
  rfl

/-- One input-rewind step over an input symbol.
**Proof sketch.** At interior position `p ≥ 1` the input read is the
`(p-1)`-st bit, so the rewind keeps moving left
(`moveInputPos_neg_of_ne_left`); nothing else changes. -/
private theorem rwInput_some (hek : 0 < Em.k) (x : List Bool) (p : ℕ)
    (hp1 : 1 ≤ p) (hpn : p ≤ x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput p (by omega) 0) =
      fullCfg Em Gm x .rwInput (p - 1) (by omega) 0 := by
  have hinp : (fullCfg Em Gm x .rwInput p (by omega) 0).inputSymbol = some x[p - 1] :=
    inputSymbolInner (p - 1) (by simp only [fullCfg]; omega) (by omega)
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwInput p (by omega) 0) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwInput
        (fullCfg Em Gm x .rwInput p (by omega) 0).inputSymbol
        (fullCfg Em Gm x .rwInput p (by omega) 0).workTapeSymbols).apply
        (fullCfg Em Gm x .rwInput p (by omega) 0) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨p, by omega⟩ : Fin (x.length + 2)) .neg = _
    rw [moveInputPos_neg_of_ne_left _ (by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega)]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, hi]

/-- The input rewind reaches the left boundary and enters the anchor seam.
**Proof sketch.** At position zero the input read is blank, so the final
branch fires: the head steps right to the canonical position one and control
enters the anchor; the resulting configuration is literally the
`Cfg.ofWords` seam carrying the copied input on tape zero. -/
private theorem rwInput_zero (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput 0 (by omega) 0) =
      Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x) := by
  have hinp : (fullCfg Em Gm x .rwInput 0 (by omega) 0).inputSymbol = none := by
    simp only [fullCfg, Cfg.inputSymbol]
    rw [dif_pos (by apply Fin.ext; simp)]
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwInput 0 (by omega) 0) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwInput
        (fullCfg Em Gm x .rwInput 0 (by omega) 0).inputSymbol
        (fullCfg Em Gm x .rwInput 0 (by omega) 0).workTapeSymbols).apply
        (fullCfg Em Gm x .rwInput 0 (by omega) 0) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨0, by omega⟩ : Fin (x.length + 2)) .pos = _
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Fin.ext
    simp [Cfg.ofWords]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords,
        stateWord, hi]
    · simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords,
        stateWord, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords, hi]

/-- **The startup segment.** From its initial configuration the body copies
the input onto tape zero, rewinds both heads, and enters the anchor seam
carrying the input, within `3·|x| + 4` steps and without visiting the anchor
earlier.
**Proof sketch.** Chain the safe runs of the four phases: `|x|` copy steps,
the boundary turnaround, `|x| + 1` tape-rewind steps, the unconditional
input-rewind entry, and `|x| + 1` input-rewind steps, each phase by
induction on its counter; every visited state is a copier state, never the
anchor. -/
private theorem body_start (hek : 0 < Em.k) :
    SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
      ((emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x) (3 * x.length + 4)
      (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
  have hcopy : ∀ i (hi : i ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (copyCfg Em Gm x 0 (Nat.zero_le _)) i (copyCfg Em Gm x i hi) := by
    intro i
    induction i with
    | zero => intro _; exact SafeRun.zero
    | succ i ih =>
      intro hi
      exact SafeRun.trans (ih (by omega))
        (SafeRun.cons (copy_step Em Gm ee ex ge gx hek x i (by omega))
          (by simp [copyCfg]) SafeRun.zero)
  have hrwt : ∀ j (hj : j ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((j : ℤ) - 1)) (j + 1)
        (fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by omega]
      exact SafeRun.cons (rwTape_none Em Gm ee ex ge gx hek x) (by simp [fullCfg])
        SafeRun.zero
    | succ j ih =>
      intro hj
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) from by push_cast; ring]
      exact SafeRun.cons (rwTape_some Em Gm ee ex ge gx hek x j (by omega))
        (by simp [fullCfg]) (ih (by omega))
  have hrwi : ∀ p (hp : p ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (fullCfg Em Gm x .rwInput p (by omega) 0) (p + 1)
        (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact SafeRun.cons (rwInput_zero Em Gm ee ex ge gx hek x) (by simp [fullCfg])
        SafeRun.zero
    | succ p ih =>
      intro hp
      exact SafeRun.cons (rwInput_some Em Gm ee ex ge gx hek x (p + 1) (by omega) hp)
        (by simp [fullCfg]) (ih (by omega))
  have hchain := ((((hcopy x.length le_rfl).trans
    (SafeRun.cons (copy_end Em Gm ee ex ge gx hek x) (by simp [copyCfg]) SafeRun.zero)).trans
    (hrwt x.length le_rfl)).trans
    (SafeRun.cons (rwIn0_step Em Gm ee ex ge gx hek x) (by simp [fullCfg]) SafeRun.zero)).trans
    (hrwi x.length le_rfl)
  rw [initCfg_eq_copyCfg]
  rw [show 3 * x.length + 4 =
    x.length + (0 + 1) + (x.length + 1) + (0 + 1) + (x.length + 1) from by omega]
  exact hchain

end Body

/-- **The emit-iteration machine** ([AB09] §7.3–§7.4 folklore: simulate a
machine on polynomially many rounds and concatenate the outcomes).  Given
machines computing the step `g` and the chunk `e` within polynomial budgets,
and a polynomial length envelope for the orbit of `g`, one finite machine
computes the concatenation of the chunks `e (g^[i] w)` for
`i = 0, …, a'·(|w|+1)^k'`, within a polynomial budget in the `C·(n+1)^c`
normal form.

**Proof sketch.** Instantiate `Turing.FinTM.exists_emitLoopTM` at the body
machine `emitIterBody` built from the two clean-call modules
(`exists_emitCallTM` for `e`, `exists_installCallTM` for `g`), the
polynomial-bits fuel machine (`computesFunInTime_polyBits`), the orbit
invariant `∃ i, s = g^[i] w`, and the budget `T` summing the fuel, startup,
and round envelopes; `body_start` and `body_round` discharge the startup and
round obligations, with the call budgets bounded through the orbit envelope
and the one-symbol-per-step output bound.  The loop host's
`c·(T+1)·(R+2)` budget is then absorbed into the polynomial normal form. -/
theorem FinTM.exists_emitIterTM (G E : FinTM Bool) (g e : List Bool → List Bool)
    (CG cG CE cE : ℕ)
    (hG : G.ComputesFunInTime g (fun n => CG * (n + 1) ^ cG))
    (hE : E.ComputesFunInTime e (fun n => CE * (n + 1) ^ cE))
    (a' k' b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ), (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
    ∃ (M : FinTM Bool) (C c : ℕ),
      M.ComputesFunInTime
        (fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
          (fun i => e (g^[i] w)))
        (fun n => C * (n + 1) ^ c) := by
  classical
  obtain ⟨Ce, eentry, eexit, cEcall, hke, hEcall⟩ :=
    FinTM.exists_emitCallTM E e _ hE
  obtain ⟨Cg, gentry, gexit, cGcall, hkg, hGcall⟩ :=
    FinTM.exists_installCallTM G g _ hG
  obtain ⟨F, cF, hF⟩ := FinTM.computesFunInTime_polyBits a' k'
  -- output-length bounds from the one-symbol-per-step discipline
  have hElen : ∀ s : List Bool, (e s).length ≤ CE * (s.length + 1) ^ cE := by
    intro s
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hE s)).2
    simpa only [hout] using E.tm.output_length_le s (CE * (s.length + 1) ^ cE)
  have hGlen : ∀ s : List Bool, (g s).length ≤ CG * (s.length + 1) ^ cG := by
    intro s
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hG s)).2
    simpa only [hout] using G.tm.output_length_le s (CG * (s.length + 1) ^ cG)
  -- the budget
  set L : ℕ → ℕ := fun n => b * (n + 1) ^ l with hL
  set TEb : ℕ → ℕ := fun n => CE * (L n + 1) ^ cE with hTEb
  set TGb : ℕ → ℕ := fun n => CG * (L n + 1) ^ cG with hTGb
  set T : ℕ → ℕ := fun n => cF * (n + 1) ^ (k' + 1) + (3 * n + 4) +
    (cEcall * (2 * TEb n + L n + 1) + cGcall * (2 * TGb n + L n + 1) + 2) with hT
  set body := emitIterBody Ce Cg hke eentry eexit gentry gexit with hbody
  have hF' : F.ComputesFunInTime
      (fun x => Nat.bits (a' * (x.length + 1) ^ k')) T := by
    intro x
    refine (hF x).mono ?_
    simp only [hT]
    omega
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠
        some BodyState.anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords .anchor (stateWord body.k x) := by
    intro x
    obtain ⟨hrun, hsafe⟩ := body_start Ce Cg eentry eexit gentry gexit hke (x := x)
    exact ⟨3 * x.length + 4, by simp only [hT]; omega, hsafe, hrun⟩
  have hround : ∀ (x s : List Bool), (∃ i, s = g^[i] x) →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) .anchor (stateWord body.k s)) t').state ≠
              some BodyState.anchor) ∧
        body.tm.runFrom
          (Cfg.ofWords (input := x) .anchor (stateWord body.k s)) t =
            { Cfg.ofWords .anchor (stateWord body.k (g s)) with output := e s } := by
    rintro x s ⟨i, rfl⟩
    set s := g^[i] x with hs
    have hsL : s.length ≤ L x.length := horbit x i
    obtain ⟨tEc, htEb', htEpos, hEfirst, hErun⟩ := hEcall x s
    obtain ⟨tGc, htGb', htGpos, hGfirst, hGrun⟩ := hGcall x s
    obtain ⟨hrun, hsafe⟩ := body_round Ce Cg eentry eexit gentry gexit hke hkg
      (x := x) s (e s) (g s) tEc htEpos hEfirst hErun tGc htGpos hGfirst hGrun
    refine ⟨tEc + 1 + tGc + 1, by omega, ?_, hsafe, hrun⟩
    have hpow : s.length + 1 ≤ L x.length + 1 := by omega
    have hTEs : CE * (s.length + 1) ^ cE ≤ TEb x.length :=
      Nat.mul_le_mul_left CE (Nat.pow_le_pow_left hpow cE)
    have hTGs : CG * (s.length + 1) ^ cG ≤ TGb x.length :=
      Nat.mul_le_mul_left CG (Nat.pow_le_pow_left hpow cG)
    have hes := hElen s
    have hgs := hGlen s
    have htE2 : tEc ≤ cEcall * (2 * TEb x.length + L x.length + 1) :=
      le_trans htEb' (Nat.mul_le_mul_left cEcall (by omega))
    have htG2 : tGc ≤ cGcall * (2 * TGb x.length + L x.length + 1) :=
      le_trans htGb' (Nat.mul_le_mul_left cGcall (by omega))
    simp only [hT]
    omega
  obtain ⟨M, c, hM⟩ := FinTM.exists_emitLoopTM body F .anchor
    (fun w s => ∃ i, s = g^[i] w) (fun _ s => g s) (fun _ s => e s)
    (fun w => w) (fun n => a' * (n + 1) ^ k') T hF'
    (fun w => ⟨0, rfl⟩)
    (fun w s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact ⟨i + 1, (Function.iterate_succ_apply' g i w).symm⟩)
    hstart hround
  -- polynomial normal form
  set D : ℕ := k' + 1 + l * cE + l * cG + l + 1 with hD
  have honeD : ∀ n : ℕ, 1 ≤ (n + 1) ^ D := fun n => Nat.one_le_pow _ _ (by omega)
  have hTle : ∀ n, T n ≤
      (cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
        cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2) * (n + 1) ^ D := by
    intro n
    have hone : 1 ≤ (n + 1) ^ l := Nat.one_le_pow _ _ (by omega)
    have hLb : L n + 1 ≤ (b + 1) * (n + 1) ^ l := by
      simp only [hL]
      calc b * (n + 1) ^ l + 1 ≤ b * (n + 1) ^ l + (n + 1) ^ l := by omega
        _ = (b + 1) * (n + 1) ^ l := by ring
    have hpowD : ∀ a : ℕ, a ≤ D → (n + 1) ^ a ≤ (n + 1) ^ D :=
      fun a ha => Nat.pow_le_pow_right (by omega) ha
    have hTEbn : TEb n ≤ CE * (b + 1) ^ cE * (n + 1) ^ (l * cE) := by
      simp only [hTEb]
      calc CE * (L n + 1) ^ cE ≤ CE * ((b + 1) * (n + 1) ^ l) ^ cE :=
            Nat.mul_le_mul_left CE (Nat.pow_le_pow_left hLb cE)
        _ = CE * (b + 1) ^ cE * (n + 1) ^ (l * cE) := by
            rw [mul_pow, ← pow_mul]
            ring
    have hTGbn : TGb n ≤ CG * (b + 1) ^ cG * (n + 1) ^ (l * cG) := by
      simp only [hTGb]
      calc CG * (L n + 1) ^ cG ≤ CG * ((b + 1) * (n + 1) ^ l) ^ cG :=
            Nat.mul_le_mul_left CG (Nat.pow_le_pow_left hLb cG)
        _ = CG * (b + 1) ^ cG * (n + 1) ^ (l * cG) := by
            rw [mul_pow, ← pow_mul]
            ring
    have h1 : cF * (n + 1) ^ (k' + 1) ≤ cF * (n + 1) ^ D :=
      Nat.mul_le_mul_left cF (hpowD _ (by omega))
    have h2 : 3 * n + 4 ≤ 4 * (n + 1) ^ D := by
      have : n + 1 ≤ (n + 1) ^ D := le_trans (by omega)
        (Nat.le_self_pow (by omega) (n + 1))
      omega
    have h3 : TEb n ≤ CE * (b + 1) ^ cE * (n + 1) ^ D :=
      le_trans hTEbn (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have h4 : TGb n ≤ CG * (b + 1) ^ cG * (n + 1) ^ D :=
      le_trans hTGbn (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have h5 : L n + 1 ≤ (b + 1) * (n + 1) ^ D :=
      le_trans hLb (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have hE3 : cEcall * (2 * TEb n + L n + 1) ≤
        cEcall * (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left cEcall ?_
      calc 2 * TEb n + L n + 1 ≤
            2 * (CE * (b + 1) ^ cE * (n + 1) ^ D) + (b + 1) * (n + 1) ^ D +
              (n + 1) ^ D := by
            have := honeD n
            omega
        _ = (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D := by ring
    have hG3 : cGcall * (2 * TGb n + L n + 1) ≤
        cGcall * (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left cGcall ?_
      calc 2 * TGb n + L n + 1 ≤
            2 * (CG * (b + 1) ^ cG * (n + 1) ^ D) + (b + 1) * (n + 1) ^ D +
              (n + 1) ^ D := by
            have := honeD n
            omega
        _ = (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D := by ring
    have h6 : 2 ≤ 2 * (n + 1) ^ D := by
      have := honeD n
      omega
    simp only [hT]
    calc cF * (n + 1) ^ (k' + 1) + (3 * n + 4) +
          (cEcall * (2 * TEb n + L n + 1) + cGcall * (2 * TGb n + L n + 1) + 2) ≤
        cF * (n + 1) ^ D + 4 * (n + 1) ^ D +
          (cEcall * (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D +
            cGcall * (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D +
            2 * (n + 1) ^ D) :=
          Nat.add_le_add (Nat.add_le_add h1 h2)
            (Nat.add_le_add (Nat.add_le_add hE3 hG3) h6)
      _ = (cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
            cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2) * (n + 1) ^ D := by ring
  set K₀ : ℕ := cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
    cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2 with hK₀
  refine ⟨M, c * (K₀ + 1) * (a' + 2), D + k', fun w => ?_⟩
  have hMw := hM w
  refine hMw.mono ?_
  set n := w.length
  have hT1 : T n + 1 ≤ (K₀ + 1) * (n + 1) ^ D := by
    have h := hTle n
    have h1 := honeD n
    calc T n + 1 ≤ K₀ * (n + 1) ^ D + (n + 1) ^ D := by omega
      _ = (K₀ + 1) * (n + 1) ^ D := by ring
  have hR2 : a' * (n + 1) ^ k' + 2 ≤ (a' + 2) * (n + 1) ^ k' := by
    have h1 : 1 ≤ (n + 1) ^ k' := Nat.one_le_pow _ _ (by omega)
    calc a' * (n + 1) ^ k' + 2 ≤ a' * (n + 1) ^ k' + 2 * (n + 1) ^ k' := by omega
      _ = (a' + 2) * (n + 1) ^ k' := by ring
  calc c * (T n + 1) * (a' * (n + 1) ^ k' + 2) ≤
        c * ((K₀ + 1) * (n + 1) ^ D) * ((a' + 2) * (n + 1) ^ k') :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hT1) hR2
    _ = c * (K₀ + 1) * (a' + 2) * (n + 1) ^ (D + k') := by
      rw [pow_add]
      ring

end Turing
