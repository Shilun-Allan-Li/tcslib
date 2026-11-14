/-
Copyright (c) 2026 Seyoon Ragavan, TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan, TCSlib contributors
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clean-module host

A host (`machine-library-design.md` §14, row H14) that runs a finite family of *clean modules*
inside one finite machine.

* **Clean modules.** A clean module (`Turing.ModuleHost.Clean`) is a finite machine with at least
  one work tape that, started at the canonical seam with an argument word as its only
  tape-resident word, halts for the first time at a positive time within a budget of the argument
  length, at the seam holding a result word, having emitted exactly a declared chunk. Every
  polynomial-time word function has a clean **install** module (the value installed as the
  tape-resident word, nothing emitted) and a clean **emit** module (the argument kept, the value
  emitted), each with a polynomial budget (`clean_install`, `clean_emit`). They come from the
  clean-call bridges `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM`, whose modules exit
  at their first positive visit of an exit state: a release flag halts such a module one silent
  step after that visit, and cutting the run at its first halt (`first_halt`) gives the uniform
  contract.
* **The host.** `Turing.ModuleHost.hostTM` pads `n` modules to a shared bank of `K` work tapes
  (all modules share tape 0) and embeds them, through the forwarding transformer
  `Turing.emitAction`, into one finite machine whose states are the host's own control states `C`
  and the modules' states (`Turing.ModuleHost.State C M = C ⊕ Σ i, (M i).State`). When module `i`
  halts, control passes to its return state `ret i`; the control states run a table `ctrl`
  supplied by the consumer (`hostTM_step_inl`). `host_call` and `host_clean` run one module inside
  the host: from the host seam at the module's entry state, with any output prefix, the host
  reaches the seam at the module's return state with the module's result word, forwarding exactly
  the module's output, and visits no control state meanwhile; `guard_add` chains such segments.
* **Head envelopes.** A clean module's heads stay within its budget `B |arg|` of the origin at
  every time (`Clean.envelope`), and the host's heads stay within `t` cells of the origin up to
  time `t` of a call (`host_call_envelope`), hence within `B |arg|` during a clean call
  (`host_clean_envelope`). These are the coarse envelopes from the time bounds and the unit head
  moves of `Turing.MultiTapeTM.workTapePos_step_le` (gate 03l round 2, finding 1).

## Origin

Harvested on 2026-11-05 (gate 03l, ruling R-03l-1) from two copies of one private layer: the
module-gluing layer of `TCSlib.Complexity.ClassNP.SAT` on `main` (the streaming emitter behind
`Complexity.SAT_reducible_SAT3` [AB09, Lemma 2.14]: six modules, one control state), and its copy
in pack 03l's `TCSlib.Complexity.Randomized.Build.IterateFindHost` (the repetition machine behind
`Complexity.polyTimeComputable_iterateFind`: five modules, three control states). Both now
instantiate this file; what they vary is a parameter here: the number of modules and their
machines, the control states and their table, the return map and the start state.

## Main definitions

* `Turing.ModuleHost.Clean` — the first-halting clean-module contract (read through `clean_iff`).
* `Turing.ModuleHost.State`, `Turing.ModuleHost.entry` — the host's state type and the entry
  state of a module (`state_eq`, `entry_eq`).
* `Turing.ModuleHost.hostTM` — the host (`hostTM_k`, `hostTM_tm_q₀`, `hostTM_step_inl`).

## Main results

* `Turing.ModuleHost.clean_install`, `clean_emit` — every polynomial-time word function has a
  clean install and a clean emit module with a polynomial budget on the argument length.
* `Turing.ModuleHost.host_call`, `host_clean` — one module call inside the host, with the guard
  that no control state is visited; `guard_add` — chaining guarded segments.
* `Turing.ModuleHost.Clean.envelope`, `host_call_envelope`, `host_clean_envelope` — the head
  envelopes of a clean module and of a host call.
* `Turing.ModuleHost.first_halt`, `live_prefix` — cutting a halting run at its first halt, and
  liveness of the prefix of a live run.
* `Turing.ModuleHost.request_budget` — a polynomial budget on a bounded request fits a common
  power.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded multi-tape machines; §2.2, the class
  FP; Lemma 2.14, the reduction of the first consumer.)
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1: the repeated-adversary machine of the second consumer.)
-/

namespace Turing.ModuleHost

open Complexity

/-! ### Runs: the first halt and the live prefix -/

/-- **The first halt.** If the run of `tm` from a live configuration `cfg` has halted by time
`t`, then it halts for the first time at some time `u` with `0 < u ≤ t`: the configurations
before `u` are live, and the configuration at `u` is the one at `t`.

**Proof sketch.** Take the least halting time `u` (`Nat.find`). It is positive because `cfg` is
live, and since halting is absorbing (`runFrom_of_halt`), the configuration at `t = u + (t - u)`
is the one at `u`. -/
theorem first_halt {k : ℕ} {S : Type} {x : List Bool}
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

/-- **The live prefix.** If the run of `tm` from `c` is live at time `t`, it is live at every
time `u ≤ t` (halting is absorbing, `runFrom_of_halt`). -/
theorem live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-! ### Clean modules -/

/-- Convert a first-positive-exit module into a halting source: a release flag, raised after
the first step, makes the module halt silently when it is at `exit` — so an entry equal to the
exit still executes once. -/
private def stopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with
              state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- The release-flag embedding of a module configuration: the flag `b` joins the state, and
every physical field is kept. -/
private def stopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same physical step as the
module and raises the release flag. -/
private lemma stop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (stopTM C entry exit).tm.step (stopCfg b c) = stopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    have hs' : (stopCfg b c).state = some (b, q) := by simp [stopCfg, hs]
    rw [MultiTapeTM.step_of_some hs', MultiTapeTM.step_of_some hs]
    simp only [stopTM, hq, ↓reduceIte]
    rfl

/-- Stop a clean call one silent step after its certified first positive exit.

**Proof sketch.** Induct on prefixes, keeping the release flag false only at time zero; the
guard prevents an early stop; the final silent halt keeps every seam field and every emitted
bit. -/
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
    (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords_def])
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
  rw [MultiTapeTM.step_of_some (q := (true, exit)) (by simp [stopCfg, Cfg.ofWords_def])]
  simp [stopTM, stopCfg, Cfg.ofWords_def, FinTM.controlAction_def, Action.apply_state,
    Action.apply_output, Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos]

/-- **The clean-module contract.** `Clean M result emit B` says: the module `M` has at least one
work tape (`0 < M.k`), and for every native input `x` and argument `arg`, the run of `M` from the
seam at its start state with `arg` as the only tape-resident word halts for the first time at
some time `t` with `0 < t ≤ B |arg|` (every configuration before `t` is live), and the
configuration at `t` is the seam holding the result word `result arg`, with output exactly
`emit arg`. -/
def Clean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- `Clean M result emit B` holds iff `0 < M.k` and, for every native input `x` and argument
`arg`, some time `t` with `0 < t ≤ B |arg|` is the first halt of `M` from the seam
`Cfg.ofWords M.tm.q₀ (stateWord M.k arg)`, at the seam holding `result arg` with output
`emit arg`. -/
theorem clean_iff (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) :
    Clean M result emit B ↔ 0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t,
        ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
        {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with
          state := none, output := emit arg} :=
  Iff.rfl

/-- **The head envelope of a clean module** (H14's space clause): if `Clean M result emit B`,
then for every native input `x` and argument `arg`, at every time `v` of the run of `M` from the
seam at its start state holding `arg` (before, at and after its first halt), every work head is
within `B |arg|` cells of the origin, where all heads start (`Cfg.ofWords_workTapePos`).

This is the coarse envelope from the time bound: one step moves each head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`), the first halt comes at a time `t ≤ B |arg|`,
and the run is constant from `t` on. The theorem intentionally publishes this coarse
time-derived bound. A sharper one does hold: every head starts at the origin and the terminal
seam (`Cfg.ofWords`) puts it back there, so a head that reaches distance `d` spends at least
`2d ≤ t` steps going out and back, and `|position| ≤ B |arg| / 2`; that factor-two bound is not
stated here (gate 03l round 2, finding 1).

**Proof sketch.** Take the first halt `t ≤ B |arg|` of `Clean`. At a time `v ≤ t` each head is
within `v` cells of its start (`MultiTapeTM.workTapePos_runFrom_mem_Icc`); at `v > t` the run
is halted, so its configuration is the one at `t` (`MultiTapeTM.runFrom_add`,
`MultiTapeTM.runFrom_of_halt`). -/
theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ}
    (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
    |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
      (B arg.length : ℤ) := by
  obtain ⟨t, -, htB, -, hend⟩ := ((clean_iff M result emit B).1 h).2 x arg
  have hhalt : (M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t).state =
      none := by
    rw [hend]
  obtain ⟨u, hut, hu⟩ : ∃ u ≤ t,
      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v =
        M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u := by
    rcases le_total v t with hvt | htv
    · exact ⟨v, hvt, rfl⟩
    · refine ⟨t, le_rfl, ?_⟩
      rw [← Nat.add_sub_of_le htv, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (M.tm.workTapePos_runFrom_mem_Icc
    (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u j)
  rw [Cfg.ofWords_workTapePos] at h1 h2
  have hB : (u : ℤ) ≤ B arg.length := by exact_mod_cast hut.trans htB
  rw [hu, abs_le]
  constructor <;> omega

/-- Turn a clean-call bridge contract into the uniform first-halting form.

**Proof sketch.** The release wrapper stops one step after the positive exit (`stop_clean`);
cutting the run at its first halt (`first_halt`) keeps the whole clean configuration. -/
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
  obtain ⟨u, hu, hut, hguard, hend⟩ := first_halt (stopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords_def]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [stopTM, Cfg.ofWords_def] using hend.trans hs

/-- The bridge overhead `c (A (n+1)^d + n + len + 1) + 1`, with the output length
`len ≤ A (n+1)^d`, fits the single monomial `(c (2A + 1) + 1)(n+1)^{d+1}`.

**Proof sketch.** `n + 1` and both source-time terms are at most multiples of `(n+1)^{d+1}`; the
last unit, which pays for the stop, is at most `(n+1)^{d+1}`. -/
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

/-- **Clean install modules.** Every polynomial-time word function `f` has a clean module that
installs `f arg` as the tape-resident word and emits nothing, with a budget `A (|arg| + 1)^d`.

**Proof sketch.** `Turing.FinTM.exists_installCallTM` gives a module that exits at its first
positive visit of an exit state, within `c (T + |arg| + |f arg| + 1)` steps for the source time
`T = A (|arg|+1)^d`; the output length is at most the source time
(`Turing.MultiTapeTM.output_length_le`). The release wrapper and the first-halt cut
(`clean_stop`) give the uniform contract one step later, and `bridge_bound` puts the budget in
the form `A' (|arg| + 1)^{d+1}`. -/
theorem clean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  -- The bridge's result length depends on the word, so enlarge it pointwise to the source
  -- time before putting it in the uniform argument-length budget.
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

/-- **Clean emit modules.** Every polynomial-time word function `f` has a clean module that
keeps its argument as the tape-resident word and emits exactly `f arg`, with a budget
`A (|arg| + 1)^d`.

**Proof sketch.** As `clean_install`, from `Turing.FinTM.exists_emitCallTM`. -/
theorem clean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
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

/-- **A common budget.** A polynomial budget `A (m + 1)^d` on a request of length `m` with
`m + 1 ≤ N` is at most `A N^D` for every `D ≥ d` (monotonicity of powers, `0 < N`). -/
theorem request_budget (A d D N m : ℕ) (hd : d ≤ D) (hm : m + 1 ≤ N) :
    A * (m + 1) ^ d ≤ A * N ^ D := by
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hm d).trans (Nat.pow_le_pow_right (by omega) hd)

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

/-- The configuration embedding for the shared bank: the padding tapes are blank, with their
heads at the origin. -/
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
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply_state, Action.apply_output,
        Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos, h]
  · funext i
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply_state, Action.apply_output,
        Action.apply_workTapes, Action.apply_workTapePos, Action.apply_inputPos, h]

/-- The padded module runs in lockstep with the module. -/
private lemma pad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (padTM M K hk).tm.runFrom (padCfg c) t = padCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none =>
    have hs' : (padCfg (K := K) c).state = none := hs
    rw [MultiTapeTM.step_of_halt hs', MultiTapeTM.step_of_halt hs]
  | some q =>
    have hw : (fun i : Fin M.k => (padCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [padCfg, Cfg.workTapeSymbols_eq, i.isLt]
    have hstate : (padCfg (K := K) c).state = some q := hs
    rw [MultiTapeTM.step_of_some hstate, MultiTapeTM.step_of_some hs]
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
    · simp [padCfg, Cfg.ofWords_def, stateWord_eq, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [padCfg, Cfg.ofWords_def, stateWord_eq, hi, hn, FinTM.bufferTape_eq]
  · funext i
    simp [padCfg, Cfg.ofWords_def]

/-! ### The host -/

/-- The states of the host over the modules `M : Fin n → FinTM Bool` with control states `C`:
`C ⊕ Σ i, (M i).State`, a control state or module `i` in one of its states. -/
abbrev State (C : Type) {n : ℕ} (M : Fin n → FinTM Bool) : Type :=
  C ⊕ Σ i, (M i).State

/-- The host's state type is `C ⊕ Σ i, (M i).State`. -/
theorem state_eq (C : Type) {n : ℕ} (M : Fin n → FinTM Bool) :
    State C M = (C ⊕ Σ i, (M i).State) :=
  rfl

/-- The entry state of module `i` inside the host: module `i` at its start state. -/
def entry {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (i : Fin n) : State C M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- The entry state of module `i` is `inr ⟨i, (M i).tm.q₀⟩`. -/
theorem entry_eq {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (i : Fin n) :
    entry (C := C) M i = .inr ⟨i, (M i).tm.q₀⟩ :=
  rfl

/-- **The clean-module host** over the modules `M : Fin n → FinTM Bool`: a finite machine with
`K` work tapes (`hk`: every module fits, all modules sharing tape 0), states `State C M`, start
state `q₀`. At a control state `inl c` it applies the consumer's table `ctrl c`; at a module
state `inr ⟨i, s⟩` it applies module `i`'s transition, padded to the `K` tapes and forwarded by
`Turing.emitAction`: the module's emission is the host's, a live successor stays in module `i`,
and a halt passes control to the return state `ret i`. -/
@[simps (config := { isSimp := false }) k tm_q₀]
def hostTM {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ)
    (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) : FinTM Bool where
  k := K
  State := State C M
  tm := {
    q₀ := q₀
    tr := fun q inp work => match q with
      | .inl c => ctrl c inp work
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (ret i)
          ((padTM (M i) K (hk i)).tm.tr s inp work) }

/-- **A control step.** At a configuration in the control state `inl c`, one step of the host
applies the consumer's action `ctrl c` for the scanned input and work symbols. -/
theorem hostTM_step_inl {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) {x : List Bool}
    (cfg : Cfg K Bool (State C M) x) (c : C) (hc : cfg.state = some (.inl c)) :
    (hostTM M K hk ctrl ret q₀).tm.step cfg =
      (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg :=
  MultiTapeTM.step_of_some hc

/-- Forwarding a padded clean seam produces the host's seam with the supplied output prefix (a
positive tape count identifies the tape-zero word). -/
private lemma host_seam {C : Type} {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ)
    (ret : Fin n → State C M) (i : Fin n)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : State C M)) (ret i) pre
      (padCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : State C M))).getD (ret i)))
        (stateWord K w) with output := pre ++ out} := by
  have h := pad_seam (K := K) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h

/-- **A module call inside the host.** Suppose module `i` (with `0 < (M i).k`), run from the seam
at its start state with argument `arg`, is live before time `t` and at time `t` is halted at the
seam holding `result`, with output `out`. Then the host, run from its seam at the entry state of
module `i` holding `arg` with output prefix `pre`, visits no control state before time `t`, and
at time `t` is at the seam in the return state `ret i` holding `result`, with output
`pre ++ out`.

**Proof sketch.** The host seam is the forwarded image (`Turing.emitCfg`) of the padded module
seam (`host_seam`). The module's live run is transferred to the padded machine (`pad_run`) and
then to the host by `Turing.emit_run`, whose agreement hypothesis holds by the definition of
`hostTM`. Every live configuration of the module has a state in module `i`'s summand, hence is
not a control state; the halting endpoint is the forwarded image of the module's terminal seam,
i.e. the host seam at `ret i` (`host_seam` again). -/
theorem host_call {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
        ≠ some (.inl c)) ∧
    (hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
      {Cfg.ofWords (ret i) (stateWord K result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → State C M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (ret i) pre (padCfg (K := K) c) =
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} := by
    simpa [emb, c, entry] using
      host_seam M K ret i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v =
        emitCfg emb (ret i) pre (padCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (padTM (M i) K (hk i)).tm (hostTM M K hk ctrl ret q₀).tm emb (ret i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [pad_run]
        exact hg u (by omega))]
    rw [pad_run]
  constructor
  · intro v hv a
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg_state, padCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact host_seam M K ret i hp x result pre out q none

/-- **The head envelope of a host call** (H14's space clause for one call, inclusive of its
endpoint): run from its seam at the entry state of module `i` holding `arg` with output prefix
`pre`, the host has, at every time `v ≤ t`, every work head within `t` cells of the origin,
where all heads start (`Cfg.ofWords_workTapePos`). Under the hypotheses of `host_call`, `t` is
the duration of the call, so this bounds the heads throughout the call.

This is the coarse envelope from the time bound: one step moves each head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`). A sharper envelope follows from the proof of
`host_call` and is not stated here: before the return, the host's tape `j` is module `i`'s
tape `j` for `j < (M i).k` (the padded module runs in lockstep and the forwarding keeps every
physical field, `Turing.emit_run`), and every other tape stays blank with its head at the
origin, so the host's heads obey any head envelope of the module.

**Proof sketch.** `MultiTapeTM.workTapePos_runFrom_mem_Icc` from the host seam, whose heads are
at the origin, and `v ≤ t`. -/
theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) :
    ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos
        j| ≤ (t : ℤ) := by
  intro v hv j
  have key : ∀ c : Cfg K Bool (State C M) x, c.workTapePos j = 0 →
      |((hostTM M K hk ctrl ret q₀).tm.runFrom c v).workTapePos j| ≤ (t : ℤ) := by
    intro c hc
    obtain ⟨h1, h2⟩ :=
      Finset.mem_Icc.1 ((hostTM M K hk ctrl ret q₀).tm.workTapePos_runFrom_mem_Icc c v j)
    rw [hc] at h1 h2
    have hvt : (v : ℤ) ≤ t := by exact_mod_cast hv
    rw [abs_le]
    constructor <;> omega
  exact key {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
    (Cfg.ofWords_workTapePos (input := x) (entry (C := C) M i) (stateWord K arg) j)

/-- **Chaining guarded segments.** If the run from `c` avoids the state `anchor` before time `a`
and is at `d` at time `a`, and the run from `d` avoids `anchor` before time `b`, then the run
from `c` avoids `anchor` before time `a + b`. -/
theorem guard_add {k : ℕ} {S : Type} {x : List Bool}
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

/-- **A clean module call inside the host.** If module `i` is `Clean` with result map `f`,
emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
`ret i` holding `f arg`, with output `pre ++ g arg`, and visits no control state before `t`.

**Proof sketch.** Unfold `Clean` for `x` and `arg` and apply `host_call` with the result word
`f arg` and the output `g arg`. -/
theorem host_clean {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ :=
    host_call M K hk ctrl ret q₀ i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- **A clean module call inside the host, with its head envelope** (the bounded call of
`host_clean` together with H14's space clause): if module `i` is `Clean` with result map `f`,
emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
`ret i` holding `f arg`, with output `pre ++ g arg`, visits no control state before `t`, and at
every time `v ≤ t` has every work head within `B |arg|` cells of the origin.

The envelope is the coarse one from the time bound (`host_call_envelope`, which also describes
the sharper envelope inherited from the module).

**Proof sketch.** `host_clean` gives `t` and the call; `host_call_envelope` at `t`, with
`t ≤ B |arg|`, gives the envelope. -/
theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)
    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl c)) ∧
      (hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧
      ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
          v).workTapePos j| ≤ (B arg.length : ℤ) := by
  obtain ⟨t, hp, ht, hguard, hend⟩ := host_clean M K hk ctrl ret q₀ i f g B h x arg pre
  refine ⟨t, hp, ht, hguard, hend, fun v hv j => ?_⟩
  have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
  exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB

end Turing.ModuleHost
