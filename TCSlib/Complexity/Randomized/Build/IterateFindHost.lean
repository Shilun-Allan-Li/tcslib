/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clean-module host of the repetition machine

The generic machine layer behind `Complexity.polyTimeComputable_iterateFind`
(`TCSlib.Complexity.Randomized.Build.IterateFind` assembles it; the theorem itself lives in
`TCSlib.Complexity.Randomized.Repetition`, the load-bearing lemma of the Pass–shelat campaign,
foundation decision D11 of `PassShelatChapter2-4Plan.md`). Nothing here mentions the
repetition lemma's data: this file turns polynomial-time string functions into *clean
modules* and glues five of them into one finite loop body with a fresh anchor.

## Construction (DESIGN.md §2.6, steps 2–5)

* **Clean modules.** `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM` deliver callable
  modules with a first-positive-visit exit; a release flag (`stopTM`) turns the first exit
  into a silent halt one step later, and minimal-halt cutting (`call_first_halt`) gives the
  uniform contract `Complexity.IterateFind.Clean`: from the seam at the start state with the
  argument as the sole tape-resident word, a first halt within a polynomial budget of the
  argument length at the seam carrying the result word, with exactly the declared chunk
  emitted (`clean_install`, `clean_emit`).
* **The copier.** A one-tape, two-state machine (`copyTM`) writes the native input on tape 0
  and returns both heads (`copy_clean`): the startup module of the loop body, since a clean
  call sees only its tape-resident argument.
* **The host.** Five modules (copier, startup install, verdict install, step install, payload
  emit) are padded to a common tape bank (`padTM`) and embedded into one finite machine
  (`hostTM`) through the forwarding transformer `Turing.emitAction`; each module's halt
  transfers control to its fixed return state (`hostRet`). The host's own control has three
  fresh states: the loop **anchor** `inl 0` (never a module-internal state, the panel repair
  J2-16/J3-6), the **branch** `inl 1`, which reads the first cell of tape 0 and dispatches on
  it (`host_branch`), and the **halt** state `inl 2` (`host_halt`). The lockstep lemma
  `host_call` (via `Turing.emit_run`) runs one module inside the host and shows that the
  anchor is never visited meanwhile; `guard_add` chains such segments.

The clean-module layer is a private copy of the module-gluing layer of
`TCSlib.Complexity.ClassNP.SAT` (`satStopTM`, `satClean_install`, `satHost_call`, …), a
template only, never a dependency.

## Main definitions

* `Complexity.IterateFind.Clean` — the uniform first-halting clean-module contract.
* `Complexity.IterateFind.copyTM` — the input copier.
* `Complexity.IterateFind.hostTM`, `hostEntry`, `hostRet`, `HostState` — the finite host over
  five modules and its entry/return states.

## Main results

* `Complexity.IterateFind.clean_install`, `clean_emit` — every polynomial-time function has a
  clean install/emit module with a polynomial budget on the argument length.
* `Complexity.IterateFind.copy_clean` — the copier's contract.
* `Complexity.IterateFind.host_call`, `host_clean` — a module call inside the host, with the
  anchor guard; `host_dispatch`, `host_branch`, `host_halt` — the host's control steps;
  `guard_add` — chaining guarded segments.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1: the repeated-adversary machine this host realizes.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded multi-tape machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### Clean modules: first-halting form of the clean-call bridges

Private copy of the module layer of `TCSlib.Complexity.ClassNP.SAT` (`satStopTM`,
`satStop_clean`, `sat_call_first_halt`, `SatClean`, `satClean_install`, `satClean_emit`),
a template only. -/

/-- Convert a first-positive-exit module into a halting source: a release flag, raised after
the first step, makes the module halt silently when it is at `exit` — so an entry equal to
the exit still executes once. -/
private def stopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with
              state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- The release-flag embedding of a module configuration. -/
private def stopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same physical step as
the module and raises the release flag. -/
private lemma stop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (stopTM C entry exit).tm.step (stopCfg b c) = stopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    simp only [MultiTapeTM.step, stopCfg, hs, Option.map_some]
    simp only [stopTM, hq, ↓reduceIte]
    rfl

/-- A live configuration at time `t` forces every earlier configuration to be live. -/
private lemma live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- Stop a clean call one silent step after its certified first positive exit.

**Proof sketch.** Induct on prefixes, keeping the release flag false only at time zero; the
guard prevents early stopping; the final silent halt retains every seam field and every
emitted bit. -/
private lemma stop_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (stopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
      {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hl := live_prefix C.tm c t
    (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords])
  have hp : ∀ v, v ≤ t → (stopTM C entry exit).tm.runFrom (stopCfg false c) v =
      stopCfg (decide (v ≠ 0)) (C.tm.runFrom c v) := by
    intro v
    induction v with
    | zero => intro _; rfl
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        stop_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      rfl
  have hi : Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg) = stopCfg false c := rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _)]
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hflag, show C.tm.runFrom c t = _ from he]
  simp [MultiTapeTM.step, stopTM, stopCfg, Cfg.ofWords, FinTM.controlAction, Action.apply]

/-- A halting run can be cut at its first halt without changing any endpoint field
(`Nat.find` and the absorbing-halt law). -/
private lemma call_first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, fun v hv => Nat.find_min h hv, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hu]

/-- Uniform clean-module contract: from the seam at the start state with the argument as
the sole tape-resident word, a first halt within `B |arg|` at the seam carrying the
replacement word `result arg`, with exactly `emit arg` emitted, over every untouched native
input. -/
def Clean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- Turn a clean-call bridge contract into the uniform first-halting form: the release
wrapper stops one step after the positive exit, and minimal-halt cutting retains the entire
clean configuration. -/
private lemma clean_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    Clean (stopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := stop_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := call_first_halt (stopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [stopTM, Cfg.ofWords] using hend.trans hs

/-- The bridge overhead `c (T + n + |f arg| + 1) + 1` fits one monomial of degree one
higher than the source budget `A (n+1)^d`. -/
private lemma bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- Every polynomial-time word function has a clean first-halting **install** module
(result installed as the tape-resident word, nothing emitted) with a polynomial budget on
the argument length (`Turing.FinTM.exists_installCallTM`, then `clean_stop`). -/
lemma clean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit f (fun _ => [])
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      refine ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, ?_⟩
      exact he)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- Every polynomial-time word function has a clean first-halting **emit** module (argument
preserved, the computed chunk forwarded to the output) with a polynomial budget on the
argument length (`Turing.FinTM.exists_emitCallTM`, then `clean_stop`). -/
lemma clean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit id f
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-! ### Padding a module into the shared tape bank -/

/-- Pad an action to a larger tape count, keeping the extra tapes stationary. -/
private def padAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
  ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
    a.output, a.state⟩

/-- A module padded into a shared bank of `K` tapes; all modules share tape zero. -/
private def padTM (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K) : FinTM Bool where
  k := K
  State := M.State
  tm := { q₀ := M.tm.q₀
          tr := fun q inp work => padAction (M.tm.tr q inp
            (fun i => work ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)) }

/-- Configuration embedding for the shared bank; the padding tapes are blank with heads
at the origin. -/
private def padCfg {k K : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos,
    fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- Padding commutes with applying an action (the inactive tapes neither write nor move). -/
private lemma pad_apply {k K : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (padAction (K := K) a).apply (padCfg c) = padCfg (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply, h]
  · funext i
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply, h]

/-- The padded module runs in lockstep with the module. -/
private lemma pad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (padTM M K hk).tm.runFrom (padCfg c) t = padCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, padCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (padCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [padCfg, Cfg.workTapeSymbols, i.isLt]
    have hstate : (padCfg (K := K) c).state = some q := hs
    simp only [MultiTapeTM.step, hstate, hs]
    change (padAction (M.tm.tr q c.inputSymbol _)).apply _ = _
    rw [hw]
    exact pad_apply _ _

/-- With a positive tape count, padding a seam gives the seam with the same state word. -/
private lemma pad_seam {k K : ℕ} {S : Type} {x : List Bool}
    (hk : 0 < k) (q : S) (w out : List Bool) :
    padCfg (K := K) ({Cfg.ofWords (input := x) q (stateWord k w) with output := out}) =
      {Cfg.ofWords (input := x) q (stateWord K w) with output := out} := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : i.val < k
    · simp [padCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [padCfg, Cfg.ofWords, stateWord, hi, hn, FinTM.bufferTape]
  · funext i
    simp [padCfg, Cfg.ofWords]

/-! ### The input copier -/

/-- The input copier: a one-tape, two-state machine that writes the native input on tape 0
and returns both heads to their seam positions. State `0` copies (read a bit, write it,
advance both heads; at the right blank move both heads left into state `1`); state `1`
walks both heads left while the input head reads a bit, and at the left blank moves both
heads right and halts. -/
def copyTM : FinTM Bool where
  k := 1
  State := Fin 2
  tm := { q₀ := 0
          tr := fun q inp _ =>
            if q = 0 then
              match inp with
              | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
              | none => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
            else
              match inp with
              | some _ => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
              | none => ⟨.pos, fun _ => (none, .pos), none, none⟩ }

/-- Configurations of the copier: control `q`, input head at position `i`, tape 0 holding
`w` from the origin with its head at cell `z`, nothing emitted. -/
private def copyCfg (x : List Bool) (q : Option (Fin 2)) (i : ℕ) (hi : i < x.length + 2)
    (w : List Bool) (z : ℤ) : Cfg 1 Bool (Fin 2) x :=
  ⟨q, ⟨i, hi⟩, fun _ => FinTM.bufferTape w, fun _ => z, []⟩

/-- One copying step: bit `j` is read, written at cell `j`, and both heads advance.

**Proof sketch.** The input head at position `j + 1` reads `x[j]` (`inputSymbolInner`); the
action writes it at cell `j`, which turns `bufferTape (x.take j)` into
`bufferTape (x.take (j + 1))` (`List.take_succ_eq_append_getElem`, `bufferTape_append`), and
both heads move right (`moveInputPos_pos_of_ne_right`). -/
private lemma copy_step (x : List Bool) (j : ℕ) (hj : j < x.length) :
    copyTM.tm.step (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j) =
      copyCfg x (some 0) (j + 1 + 1) (by omega) (x.take (j + 1)) ((j + 1 : ℕ) : ℤ) := by
  have hsym : (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j).inputSymbol = some x[j] :=
    inputSymbolInner j (by simp [copyCfg]; omega) hj
  have hs : (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j).state = some 0 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.pos, fun _ => (some (some x[j]), .pos), none, some 0⟩ :
    Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext i
    simp only [Action.apply, copyCfg]
    rw [List.take_succ_eq_append_getElem hj, FinTM.bufferTape_append, List.length_take,
      Nat.min_eq_left hj.le]
  · funext i
    simp [Action.apply, copyCfg]

/-- At the right blank the copier turns: both heads move left and the control becomes `1`.

**Proof sketch.** At position `|x| + 1` the input symbol is the right blank
(`inputSymbol_at`); the action writes nothing, moves the input head left
(`moveInputPos_neg_val`) and the work head to `|x| - 1`. -/
private lemma copy_turn (x : List Bool) :
    copyTM.tm.step (copyCfg x (some 0) (x.length + 1) (by omega) x x.length) =
      copyCfg x (some 1) x.length (by omega) x (x.length - 1) := by
  have hsym : (copyCfg x (some 0) (x.length + 1) (by omega) x x.length).inputSymbol = none := by
    rw [FinTM.inputSymbol_at _ x.length le_rfl rfl]
    simp
  have hs : (copyCfg x (some 0) (x.length + 1) (by omega) x x.length).state = some 0 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.neg, fun _ => (none, .neg), none, some 1⟩ : Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [FinTM.moveInputPos_neg_val]
    simp
  · funext i
    simp [Action.apply, copyCfg]
  · funext i
    simp [Action.apply, copyCfg, sub_eq_add_neg]

/-- The rewind: from input position `p ≤ |x|` in control `1`, `p` left moves of both heads
reach input position `0`.

**Proof sketch.** Induction on `p`, generalizing the work head: at position `p + 1 ≤ |x|` the
input head reads `x[p]`, so one step moves both heads left without writing, and the
induction hypothesis finishes the remaining `p` steps. -/
private lemma copy_rewind (x : List Bool) (p : ℕ) (hp : p ≤ x.length) (z : ℤ) :
    copyTM.tm.runFrom (copyCfg x (some 1) p (by omega) x z) p =
      copyCfg x (some 1) 0 (by omega) x (z - p) := by
  induction p generalizing z with
  | zero => simp [copyCfg]
  | succ p ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : copyTM.tm.step (copyCfg x (some 1) (p + 1) (by omega) x z) =
        copyCfg x (some 1) p (by omega) x (z - 1) := by
      have hsym : (copyCfg x (some 1) (p + 1) (by omega) x z).inputSymbol = some x[p] :=
        inputSymbolInner p (by simp [copyCfg]; omega) (by omega)
      have hs : (copyCfg x (some 1) (p + 1) (by omega) x z).state = some 1 := rfl
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [hsym]
      show (⟨.neg, fun _ => (none, .neg), none, some 1⟩ : Action 1 Bool (Fin 2)).apply _ = _
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · apply Fin.ext
        simp only [Action.apply, copyCfg]
        rw [FinTM.moveInputPos_neg_val]
        simp
      · funext i
        simp [Action.apply, copyCfg]
      · funext i
        simp [Action.apply, copyCfg, sub_eq_add_neg]
    rw [hstep, ih (by omega)]
    simp only [copyCfg, Nat.cast_succ]
    congr 1
    funext _
    ring

/-- At the left blank the copier moves both heads right and halts. -/
private lemma copy_finish (x : List Bool) (z : ℤ) :
    copyTM.tm.step (copyCfg x (some 1) 0 (by omega) x z) =
      copyCfg x none 1 (by omega) x (z + 1) := by
  have hsym : (copyCfg x (some 1) 0 (by omega) x z).inputSymbol = none := by
    simp [Cfg.inputSymbol, copyCfg]
  have hs : (copyCfg x (some 1) 0 (by omega) x z).state = some 1 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.pos, fun _ => (none, .pos), none, none⟩ : Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
  · funext i
    simp [Action.apply, copyCfg]
  · funext i
    simp [Action.apply, copyCfg]

/-- **The copier's contract.** From the empty seam over native input `x`, the copier halts
after exactly `2|x| + 2` steps at the seam holding `x` on tape 0, never halting earlier.

**Proof sketch.** `|x|` copying steps (`copy_step`), the turn (`copy_turn`), `|x|` rewind
steps (`copy_rewind`), the final right move and halt (`copy_finish`); liveness before the
end from the live configuration at time `2|x| + 1` (`live_prefix`). -/
lemma copy_clean (x : List Bool) :
    (∀ v < 2 * x.length + 2,
      ¬(copyTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 [])) v).Halted) ∧
    copyTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []))
        (2 * x.length + 2) =
      {Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 x) with state := none} := by
  have hi : Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []) =
      copyCfg x (some 0) 1 (by omega) [] 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    simp [Cfg.ofWords, copyCfg, stateWord]
  have hcopy : ∀ j (hj : j ≤ x.length),
      copyTM.tm.runFrom (copyCfg x (some 0) 1 (by omega) [] 0) j =
        copyCfg x (some 0) (j + 1) (by omega) (x.take j) j := by
    intro j
    induction j with
    | zero => intro _; simp [copyCfg]
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), copy_step x j (by omega)]
  have hmid : copyTM.tm.runFrom (copyCfg x (some 0) 1 (by omega) [] 0) (2 * x.length + 1) =
      copyCfg x (some 1) 0 (by omega) x (-1) := by
    rw [show 2 * x.length + 1 = x.length + 1 + x.length by ring, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step', hcopy x.length le_rfl]
    simp only [List.take_length]
    rw [copy_turn, copy_rewind x x.length le_rfl]
    simp only [copyCfg]
    congr 1
    funext _
    ring
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [hi]
    exact live_prefix copyTM.tm _ (2 * x.length + 1) (by rw [hmid]; simp [copyCfg]) v (by omega)
  · rw [hi, MultiTapeTM.runFrom_succ_eq_step', hmid, copy_finish]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext; simp [copyCfg, Cfg.ofWords]
    · funext i
      simp [copyCfg, Cfg.ofWords, stateWord]
    · funext i
      simp [copyCfg, Cfg.ofWords]

/-! ### The finite host -/

/-- The host's states: three fresh control states — `0` the loop anchor, `1` the verdict
branch, `2` the halt state — and the states of the five modules (`0` copier, `1` startup
install `x ↦ ⟨x, x⟩`, `2` verdict install, `3` step install, `4` payload emit). -/
abbrev HostState (M : Fin 5 → FinTM Bool) := Fin 3 ⊕ (Σ i, (M i).State)

/-- The entry state of module `i` inside the host. -/
def hostEntry (M : Fin 5 → FinTM Bool) (i : Fin 5) : HostState M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- Return destinations of the modules: copier → startup install, startup install → anchor,
verdict → branch, step → anchor, payload emit → halt state. -/
def hostRet (M : Fin 5 → FinTM Bool) (i : Fin 5) : HostState M :=
  if i = 0 then hostEntry M 1 else if i = 2 then .inl 1 else if i = 4 then .inl 2 else .inl 0

/-- The finite host of the repetition machine: `K + 1` shared tapes (tape 0 carries the
state word); the anchor dispatches into the verdict module; the branch state reads the
verdict cell of tape 0 and dispatches into the payload module (`true`) or the step module
(`false`); the halt state halts; every module is padded and forwarded through
`Turing.emitAction`, its halt transferring control to its return state. -/
def hostTM (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) :
    FinTM Bool where
  k := K + 1
  State := HostState M
  tm := {
    q₀ := hostEntry M 0
    tr := fun q inp work => match q with
      | .inl c =>
        if c = 0 then FinTM.controlAction 0 (some (hostEntry M 2))
        else if c = 1 then
          FinTM.controlAction 0
            (some (if work 0 = some true then hostEntry M 4 else hostEntry M 3))
        else FinTM.controlAction 0 none
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (hostRet M i)
          ((padTM (M i) (K + 1) (hk i)).tm.tr s inp work) }

/-- Forwarding a padded clean seam produces the host's seam with the supplied output
prefix (positive tape count identifies the tape-zero word). -/
private lemma host_seam (M : Fin 5 → FinTM Bool) (K : ℕ) (i : Fin 5)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : HostState M)) (hostRet M i) pre
      (padCfg (K := K + 1) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : HostState M))).getD (hostRet M i)))
        (stateWord (K + 1) w) with output := pre ++ out} := by
  have h := pad_seam (K := K + 1) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg (K + 1) Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg (K + 1) Bool (M i).State x => c.workTapePos) h

/-- Run one clean module inside the host, forwarding exactly its output: from the host seam
at the module's entry (with any output prefix), the host reaches, at the module's first halt,
the host seam at the module's return state with the result word and the prefix followed by
the module's output, never visiting the anchor meanwhile.

**Proof sketch.** The host seam is the forwarded image (`Turing.emitCfg`) of the padded
module seam (`host_seam`); the module's live run is transferred to the padded machine
(`pad_run`) and then to the host by `Turing.emit_run`, whose agreement hypothesis holds by
definition of `hostTM`; every live prefix configuration has a state in the module's summand,
hence is not the anchor; the halting endpoint is the forwarded image of the module's
terminal seam, i.e. the host seam at the return state (`host_seam` again). -/
lemma host_call (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (i : Fin 5) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ((hostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} v).state
        ≠ some (.inl 0)) ∧
    (hostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} t =
      {Cfg.ofWords (hostRet M i) (stateWord (K + 1) result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → HostState M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (hostRet M i) pre (padCfg (K := K + 1) c) =
      {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} := by
    simpa [emb, c, hostEntry] using
      host_seam M K i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (hostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} v =
        emitCfg emb (hostRet M i) pre (padCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (padTM (M i) (K + 1) (hk i)).tm (hostTM M K hk).tm emb (hostRet M i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [pad_run]
        exact hg u (by omega))]
    rw [pad_run]
  constructor
  · intro v hv
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg, padCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact host_seam M K i hp x result pre out q none

/-- Joining two guarded segments preserves the anchor guard when the intermediate seam is
also outside the anchor. -/
lemma guard_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  intro v hv
  by_cases h : v < a
  · exact ha v h
  · have hva : a ≤ v := by omega
    rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
    exact hb (v - a) (by omega)

/-- Specialize a clean module to one call site in the host. -/
lemma host_clean (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (i : Fin 5) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ((hostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} v).state
          ≠ some (.inl 0)) ∧
      (hostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} t =
        {Cfg.ofWords (hostRet M i) (stateWord (K + 1) (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ := host_call M K hk i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- The anchor dispatches into the verdict module in one stationary step. -/
lemma host_dispatch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w : List Bool) :
    (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) =
      Cfg.ofWords (hostEntry M 2) (stateWord (K + 1) w) := by
  change (FinTM.controlAction 0 (some (hostEntry M 2))).apply _ = _
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- The branch state reads the first cell of tape 0 — the verdict `b` of a verdict word —
and dispatches into the payload module (`true`) or the step module (`false`), stationary. -/
lemma host_branch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
    (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
      Cfg.ofWords (hostEntry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
  have hread : (Cfg.ofWords (input := x) (.inl 1 : HostState M)
      (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
    simp [Cfg.ofWords, Cfg.workTapeSymbols, stateWord, FinTM.bufferTape, hw]
  unfold MultiTapeTM.step
  show (FinTM.controlAction 0 (some (if (Cfg.ofWords (input := x) (.inl 1 : HostState M)
    (stateWord (K + 1) w)).workTapeSymbols 0 = some true
      then hostEntry M 4 else hostEntry M 3))).apply _ = _
  rw [hread, FinTM.controlAction_apply, moveInputPos_zero]
  cases b <;> rfl

/-- The halt state halts without emitting. -/
lemma host_halt (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w o : List Bool) :
    (hostTM M K hk).tm.step
        {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
      {Cfg.ofWords (input := x) (.inl 2 : HostState M) (stateWord (K + 1) w)
        with state := none, output := o} := by
  change (FinTM.controlAction 0 none).apply _ = _
  rw [FinTM.controlAction_apply, moveInputPos_zero]

end Complexity.IterateFind
