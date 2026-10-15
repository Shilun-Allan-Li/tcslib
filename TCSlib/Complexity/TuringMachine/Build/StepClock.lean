/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the step-clocked runner (host H3's clock)

A **step clock** runs a body machine under a binary countdown that ticks once per physical body
step. It exits at `finish` when the body stops (halts, or reaches a designated stop state), and
at `timeout` when the countdown is exhausted first. It is the clock of the windowed runner H3
(`machine-library-design.md` §14) and of the nondeterministic time hierarchy's diagonalizer
(C1, which cites the `Bool` instance `Turing.exists_stepClockTM`). Unlike the round counter
`Turing.counterLoopTMVia`, which restarts its body at a fixed anchor every round, it counts
physical steps, so the body's state survives from step to step.

**Status update (B6-F1 fill): proved.** The statement gate passed 2026-10-14 (round 1,
0/0/5; `audits/b6-hosts-statements-findings.md`). The joint step-clock contract and its `Bool`
instance are proved without admissions, through the prescribed fused controller, public
transports and segment composition.

## Design

* **Layout.** The body is on the first `k` tapes and the counter on the last
  (`Turing.clockCfg`). The counter digits are embedded along `e : Bool ↪ Γ`, as in
  `Turing.counterLoopTMVia`, so the clock runs over any alphabet with a digit embedding; the
  windowed runner runs over the record alphabet.
* **Exact endpoints.** At both exits the body part is the body's configuration at the stopping
  or clock time, and the counter tape differs from its start only on the counter word's cells,
  which hold some word of the same width (`Turing.wordPatch`).
* **Frames.** At every host time up to the exit, the body part (tapes, heads, input head,
  output) is the body's configuration at some body time, and the counter head stays within
  `[cp - 1, cp + |w|]`. This bounds the host's space by the body's plus `|w| + 2`, and carries
  silence and envelopes through the clock.
* The contract is an existential module; the named witness comes at fill time.

## Main definitions

* `Turing.clockCfg` — the host layout: body tapes first, the counter tape last.
* `Turing.wordPatch` — a tape with a word written over an interval.
* `Turing.Cfg.Stopped` — a body configuration that is halted or in a designated stop state.

## Main results

* `Turing.exists_stepClockTMVia` — the step clock over any alphabet (proved; B6-F1 fill).
* `Turing.exists_stepClockTM` — its `Bool` instance, in C1's draft form (proved from it).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, proof of Theorem 3.2: the diagonalizer runs the
  simulation for a bounded number of steps; §4.1.3, Theorem 4.8, whose proof the book assigns
  to Exercise 4.1. The fused step clock is the repository's refinement of that bounded
  simulation, not a construction printed in the book.)
-/

namespace Turing

/-- **The step clock's layout**: the body configuration `c` on the first `k` tapes, the
counter tape `ct` with its head at `cp` as the last tape, the host control `q`, and the body's
input head and output. -/
def clockCfg {k : ℕ} {Γ S Q : Type} {x : List Γ} (q : Option Q) (c : Cfg k Γ S x)
    (ct : ℤ → Option Γ) (cp : ℤ) : Cfg (k + 1) Γ Q x :=
  ⟨q, c.inputPos, Fin.lastCases ct c.workTapes, Fin.lastCases cp c.workTapePos, c.output⟩

/-- **A tape with a word patched in**: the cells `cp, …, cp + |u| - 1` hold `u`, every other
cell is `ct`'s. -/
def wordPatch {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u : List Γ) : ℤ → Option Γ :=
  fun q => if cp ≤ q ∧ q < cp + (u.length : ℤ) then FinTM.bufferTape u (q - cp) else ct q

/-- **A stopped body configuration**: halted, or live in a designated stop state. -/
def Cfg.Stopped {k : ℕ} {Γ S : Type*} {x : List Γ} (stopAt : S → Bool) (c : Cfg k Γ S x) :
    Prop :=
  c.state = none ∨ ∃ s, c.state = some s ∧ stopAt s = true

/-! ### Step-clock fill (B6-F1, brief v2): the fused control -/

/-- **The step clock's control**: a decrement phase carrying the body state it
resumes, one pending body transition, and the two exit families. -/
private inductive sc_State (S : Type) where
  /-- decrement phase `f` on the counter tape, with the body paused at state `s` -/
  | dec (s : S) (f : FlagPhase)
  /-- one body transition from state `s`, after a successful decrement -/
  | body (s : S)
  /-- the exit family `finish`, carrying the stopped body state -/
  | finish (r : Option S)
  /-- the exit family `timeout`, carrying the body state at the deadline -/
  | timeout (r : Option S)
  deriving DecidableEq

/-- The step clock's control is finite. -/
private instance sc_State_fintype (S : Type) [Fintype S] : Fintype (sc_State S) :=
  derive_fintype% _

/-- Where a decrement transition lands: success resumes the paused body at `s`,
underflow is `timeout (some s)`, and every working phase stays a decrement phase. -/
private def sc_decExit {S : Type} (s : S) : FlagPhase → sc_State S
  | .done true => .body s
  | .done false => .timeout (some s)
  | f => .dec s f

/-- The decrement redirection is injective, so it is an embedding of the
decrement's phases into the clock's control.

**Proof sketch.** Compare constructors: the two anchors land on distinct constructors, and the
working phases keep their phase. -/
private theorem sc_decExit_injective {S : Type} (s : S) : Function.Injective (sc_decExit s) := by
  rintro (_ | b | b) (_ | b' | b') h <;> (try cases b) <;> (try cases b') <;>
    simp_all [sc_decExit]

/-- A body transition in the host: the body's action on the body tapes, landing at
the successor's decrement entry, or at `finish none` when the transition halts the body. -/
private def sc_bodyAct {k : ℕ} {Γ S : Type} (a : Action (k + 1) Γ S) :
    Action (k + 1) Γ (sc_State S) where
  inputTape := a.inputTape
  workTapes := a.workTapes
  output := a.output
  state := some (match a.state with
    | some s' => .dec s' .run
    | none => .finish none)

/-- **The fused step clock.** At `dec s .run` a stop state `s` leaves at once for
`finish (some s)`; otherwise the decrement runs on the counter tape (the one-tape
`Turing.decrementTM`, lifted along `e` and placed on the last tape by R1 along
`Turing.lastEmb`) with the body paused at `s`. Success leads to `body s`, which performs one
body transition (R1 along `Fin.castSuccEmb`); underflow is `timeout (some s)`. The exits are
stationary; the initial state is never used. -/
private def sc_clockTM {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) : MultiTapeTM (k + 1) Γ (sc_State S) where
  q₀ := .finish none
  tr := fun q inp work =>
    match q with
    | .dec s f =>
      if f = .run ∧ stopAt s = true then
        ⟨0, fun _ => (none, 0), none, some (.finish (some s))⟩
      else
        ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
          (sc_decExit s)
    | .body s => sc_bodyAct ((embedEmitTM Fin.castSuccEmb M).tr s inp work)
    | .finish r => ⟨0, fun _ => (none, 0), none, some (.finish r)⟩
    | .timeout r => ⟨0, fun _ => (none, 0), none, some (.timeout r)⟩

/-- Away from a stop state, the clock's decrement phases are the lifted,
embedded decrement renamed along `sc_decExit s`: the agreement `sc_debit` asks for.

**Proof sketch.** Unfold the table at `sc_decExit s f`, which is `dec s f` on a working phase;
the stop branch is not taken because `stopAt s = false`. -/
private theorem sc_agree {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) (s : S) (hs : stopAt s = false)
    (f : FlagPhase) (hf : ∀ b, f ≠ .done b) (inp : Option Γ) (work : Fin (k + 1) → Option Γ) :
    (sc_clockTM e M stopAt).tr (sc_decExit s f) inp work =
      ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
        (sc_decExit s) := by
  cases f with
  | run => simp [sc_clockTM, sc_decExit, hs]
  | rewind b => simp [sc_clockTM, sc_decExit]
  | done b => exact absurd rfl (hf b)

/-- **The clock layout is the body's R1 embedding** along
`Fin.castSuccEmb`, with the counter tape as the frame: the eighth member of the R1 layout
family, derived from the public reconstruction lemma rather than re-proved.

**Proof sketch.** `Turing.embedEmitCfg_eq`: the selected tapes and heads are the body's, the one
unselected tape is the last. -/
private theorem sc_layout {k : ℕ} {Γ S : Type} {x : List Γ} (c : Cfg k Γ S x)
    (ct : ℤ → Option Γ) (cp : ℤ) :
    embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c = clockCfg c.state c ct cp := by
  refine embedEmitCfg_eq _ _ _ _ c _ rfl rfl (by simp [clockCfg]) (fun i => by simp [clockCfg])
    fun j hj => ?_
  induction j using Fin.lastCases with
  | last => simp [clockCfg]
  | cast i => exact absurd ⟨i, rfl⟩ hj

/-- **The counter phase's layout**: a one-tape configuration `D` placed on
the last tape by R1 along `Turing.lastEmb`, with the body's tapes and heads as the frame, is the
clock layout of the body `c` with `D`'s tape and head as the counter, when `D` has the body's
input position and output.

**Proof sketch.** `Turing.embedEmitCfg_eq` along `Turing.lastEmb`: the one selected tape is the
last; the unselected ones are the body's. -/
private theorem sc_lastLayout {k : ℕ} {Γ S Q : Type} {x : List Γ} (c : Cfg k Γ S x)
    (D : Cfg 1 Γ Q x) (ct : ℤ → Option Γ) (cp : ℤ) (hin : D.inputPos = c.inputPos)
    (hout : D.output = c.output) :
    embedEmitCfg (lastEmb k) (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) []
        D = clockCfg D.state c (D.workTapes 0) (D.workTapePos 0) := by
  apply embedEmitCfg_eq
  · rfl
  · exact hin
  · simp [clockCfg, hout]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [clockCfg, lastEmb_apply]
  · intro j hj
    induction j using Fin.lastCases with
    | last => exact absurd ⟨0, lastEmb_apply k 0⟩ hj
    | cast i => simp [clockCfg]

/-- **A decrement never moves the input head**:
along every run of the one-tape decrement, at every time, the input position is the starting one
(the frame clause needs it at every debit time, which the decrement's contracts state at the
endpoint only).

**Proof sketch.** Every action has input move `0` (`Turing.decrementTM_tr_action`), so a step
keeps the position (`Turing.moveInputPos_zero`); a halted configuration does not move; induct on
the time. -/
private theorem sc_dec_inputPos {k : ℕ} {x : List Bool} (i : Fin k)
    (d : Cfg k Bool FlagPhase x) (t : ℕ) :
    ((decrementTM k i).runFrom d t).inputPos = d.inputPos := by
  induction t
  case zero => rfl
  case succ t ih =>
    rw [← ih, MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    split
    · rfl
    · simp only [Action.apply, (decrementTM_tr_action i _ _ _).1, moveInputPos_zero]

/-- **Patching in the word a tape already holds changes nothing**: if
`ct` holds `u` delimited at `cp`, then `wordPatch ct cp u = ct` (the round induction's start,
where the counter tape is still the caller's).

**Proof sketch.** Inside the interval the hypothesis says `ct` already reads `u`; outside it the
patch is `ct`. -/
private theorem sc_wordPatch_self {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (u : List Γ)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) → ct (cp + p) = FinTM.bufferTape u p) :
    wordPatch ct cp u = ct := by
  funext q
  unfold wordPatch
  split_ifs with inside
  · have h := hu (q - cp) (by omega) (by omega)
    rw [add_sub_cancel] at h
    exact h.symm
  · rfl

/-- **Patching one interval twice keeps the last patch**, for two words
of the same width.

**Proof sketch.** Pointwise: inside the interval both sides read the second word; outside it
neither patch is visible. -/
private theorem sc_wordPatch_twice {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ)
    (huv : v.length = u.length) :
    wordPatch (wordPatch ct cp u) cp v = wordPatch ct cp v := by
  funext q
  unfold wordPatch
  rw [huv]
  by_cases hq : cp ≤ q ∧ q < cp + (u.length : ℤ) <;> simp [hq]

/-- **A same-width patch keeps the counter delimited**: if `ct` holds
`u` delimited at `cp`, then patching `v` of the same width over it holds `v` delimited at
`cp`.

**Proof sketch.** Inside the interval the patch reads `v`. The two delimiters, at `cp - 1` and
`cp + |v|`, lie outside it, where `ct` is blank by the hypothesis on `u`. -/
private theorem sc_wordPatch_frame {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ)
    (huv : v.length = u.length)
    (hu : ∀ p : ℤ, -1 ≤ p → p ≤ (u.length : ℤ) → ct (cp + p) = FinTM.bufferTape u p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      wordPatch ct cp v (cp + p) = FinTM.bufferTape v p := by
  intro p lo hi
  unfold wordPatch
  by_cases inside : cp ≤ cp + p ∧ cp + p < cp + (v.length : ℤ)
  · rw [if_pos inside, add_sub_cancel_left]
  · rw [if_neg inside]
    rcases (by omega : p = -1 ∨ p = (v.length : ℤ)) with rfl | rfl
    · rw [hu (-1) le_rfl (by omega), FinTM.bufferTape_left, FinTM.bufferTape_left]
    · rw [hu _ (by omega) (by omega)]
      simp [huv]

/-- R1a (success). A predecessor keeps the width. -/
private theorem sc_dec_success_width (w v : List Bool) (h : decFixed w = some v) :
    v.length = w.length := by
  have hs := counter_dec_spec w
  rw [h] at hs
  exact hs.1

/-- The `false` prefix of an all-`false` word is the whole word. -/
private theorem sc_takeWhile_replicate (n : ℕ) :
    ((List.replicate n false).takeWhile not).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ]

/-- R1b (underflow). The debit's cost `2·|takeWhile not w| + 2` is the underflow contract's
`2|w| + 2`. -/
private theorem sc_dec_underflow_cost (w : List Bool) (h : decFixed w = none) :
    (w.takeWhile not).length = w.length := by
  have hs := counter_dec_spec w
  rw [h] at hs
  have := sc_takeWhile_replicate w.length
  rw [← hs] at this
  exact this

/-- R1c. The debit's patched word has the counter's width, in both cases. -/
private theorem sc_dec_patch_width (w : List Bool) :
    ((decFixed w).getD (List.replicate w.length true)).length = w.length := by
  cases h : decFixed w with
  | none => simp
  | some v => simpa using sc_dec_success_width w v h

/-- R1d. The decoded shadow of the debit's one-tape start meets both decrement contracts'
preconditions (state and delimited word). -/
private theorem sc_shadow_pre {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ}
    (ip : Fin (x.length + 2)) (out : List Γ) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    let D : Cfg 1 Γ FlagPhase x := ⟨some .run, ip, fun _ => ct, fun _ => cp, out⟩
    (Cfg.decodeSymbols e D).state = some .run ∧
      ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
        (Cfg.decodeSymbols e D).workTapes 0 ((Cfg.decodeSymbols e D).workTapePos 0 + p) =
          FinTM.bufferTape w p := by
  intro D
  refine ⟨Cfg.decodeSymbols_state e D, fun p lo hi => ?_⟩
  rw [Cfg.decodeSymbols_workTapes, Cfg.decodeSymbols_workTapePos]
  change (ct (cp + p)).bind (decodeBool e) = _
  rw [hw p lo hi, FinTM.bufferTape_map_decode]

/-- R1e. The lifted decrement runs as the overlay of the decrement's run on the shadow, from the
rich start itself (the side conditions are the promoted table lemmas). -/
private theorem sc_lift_run {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ}
    (D : Cfg 1 Γ FlagPhase x) (t : ℕ) :
    ((decrementTM 1 0).liftSymbols e).runFrom D t =
      Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom (Cfg.decodeSymbols e D) t) := by
  conv_lhs => rw [← Cfg.liftOver_decodeSymbols e D]
  exact MultiTapeTM.liftSymbols_runFrom_over e (decrementTM 1 0) (decrementTM_tr_input 0)
    (fun q inp work j => (decrementTM_tr_action 0 q inp work).2 j) _ D (Cfg.decodeSymbols e D) t

/-- R1f. At every time up to the decrement's exit, the overlay keeps the start's input position
and output (what `sc_lastLayout` and the frame clause need), and its head is the decrement's. -/
private theorem sc_lift_frame {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ}
    (D : Cfg 1 Γ FlagPhase x) (T : ℕ)
    (hT : ((decrementTM 1 0).runFrom (Cfg.decodeSymbols e D) T).output = []) :
    ∀ u ≤ T,
      (((decrementTM 1 0).liftSymbols e).runFrom D u).inputPos = D.inputPos ∧
      (((decrementTM 1 0).liftSymbols e).runFrom D u).output = D.output ∧
      (((decrementTM 1 0).liftSymbols e).runFrom D u).workTapePos =
        ((decrementTM 1 0).runFrom (Cfg.decodeSymbols e D) u).workTapePos := by
  intro u hu
  rw [sc_lift_run]
  refine ⟨Fin.ext ?_, ?_, Cfg.liftOver_workTapePos e _ D _⟩
  · rw [Cfg.liftOver_inputPos, sc_dec_inputPos, Cfg.decodeSymbols_inputPos]
  · have hp := MultiTapeTM.output_prefix (decrementTM 1 0) (Cfg.decodeSymbols e D) hu
    rw [hT, List.prefix_nil] at hp
    rw [Cfg.liftOver_output, hp, List.map_nil, List.append_nil]

/-- **One decrement on the last tape
of any host that runs the lifted decrement there.** Let the host `H` agree, on the decrement's
working phases, with the R1-embedded lifted decrement renamed along `ρ`. Start it at `ρ .run` in
the layout `Turing.clockCfg`, with a delimited counter word `w` (digits embedded by `e`) at the
head of the last tape. Then `H` reaches `ρ (.done b)`, where `b` says whether `w` has a
predecessor at its width, after exactly `2·|takeWhile not w| + 2` steps (which is `2|w| + 2` on
underflow) and at no `ρ (.done _)` earlier. The counter interval then holds the predecessor, or
`|w|` copies of `true` on underflow; up to then the body part (its tapes, heads, input head and
output) is unchanged and the counter head stays in `[cp - 1, cp + |w|]`. Every intermediate
state is in the optional image of `ρ`; this additional invariant excludes unrelated host exits.

**Proof sketch.** As the private `counter_debit` of `Build/CounterLoop.lean` does for the
counter loop, with `H` and `ρ` in place of `counterLoopTMVia` and its decrement redirection,
through public lemmas only: decode the one-tape start (`Turing.Cfg.decodeSymbols`, read by its
field lemmas), apply `Turing.decrementTM_run_succ_ofCfg` or
`Turing.decrementTM_run_underflow_ofCfg` (the widths and costs by `Turing.counter_dec_spec`),
lift by `Turing.MultiTapeTM.liftSymbols_runFrom_over` (side conditions
`Turing.decrementTM_tr_input`, `Turing.decrementTM_tr_action`) and read the overlay back by the
`Turing.Cfg.liftOver_*` field lemmas, the input head by `sc_dec_inputPos` and the output by
`Turing.MultiTapeTM.output_prefix`; place on the last tape by
`Turing.embedEmitTM_runFrom` along `Turing.lastEmb` (`sc_lastLayout`), and transfer to `H` by
`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` with `ρ`. -/
private theorem sc_debit {k : ℕ} {Γ S Q : Type} [DecidableEq Γ] {x : List Γ} (e : Bool ↪ Γ)
    (H : MultiTapeTM (k + 1) Γ Q) (ρ : FlagPhase ↪ Q)
    (hagree : ∀ f : FlagPhase, (∀ b, f ≠ .done b) → ∀ inp work,
      H.tr (ρ f) inp work =
        ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState ρ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    H.runFrom (clockCfg (some (ρ .run)) c ct cp) (2 * (w.takeWhile not).length + 2) =
        clockCfg (some (ρ (.done (decFixed w).isSome))) c
          (wordPatch ct cp (((decFixed w).getD (List.replicate w.length true)).map e)) cp ∧
      (∀ u < 2 * (w.takeWhile not).length + 2, ∀ b : Bool,
        (H.runFrom (clockCfg (some (ρ .run)) c ct cp) u).state ≠ some (ρ (.done b))) ∧
      (∀ u ≤ 2 * (w.takeWhile not).length + 2,
        H.runFrom (clockCfg (some (ρ .run)) c ct cp) u =
            clockCfg (H.runFrom (clockCfg (some (ρ .run)) c ct cp) u).state c
              ((H.runFrom (clockCfg (some (ρ .run)) c ct cp) u).workTapes (Fin.last k))
              ((H.runFrom (clockCfg (some (ρ .run)) c ct cp) u).workTapePos (Fin.last k)) ∧
          (H.runFrom (clockCfg (some (ρ .run)) c ct cp) u).workTapePos (Fin.last k) ∈
            Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      ∀ u ≤ 2 * (w.takeWhile not).length + 2, ∃ f : Option FlagPhase,
        (H.runFrom (clockCfg (some (ρ .run)) c ct cp) u).state = f.map ρ := by
  let seed : Cfg 1 Γ FlagPhase x :=
    ⟨some .run, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩
  let shadow := Cfg.decodeSymbols e seed
  let ticks := 2 * (w.takeWhile not).length + 2
  let word := (decFixed w).getD (List.replicate w.length true)
  let result := { shadow with
    state := some (FlagPhase.done (decFixed w).isSome)
    workTapes := fun j p =>
      if j = 0 ∧ shadow.workTapePos j ≤ p ∧ p < shadow.workTapePos j + (w.length : ℤ)
      then FinTM.bufferTape word (p - shadow.workTapePos j) else shadow.workTapes j p }
  have pos : shadow.workTapePos = seed.workTapePos := Cfg.decodeSymbols_workTapePos e seed
  obtain ⟨ready, digits⟩ := sc_shadow_pre e c.inputPos c.output w ct cp hw
  -- Consume the two framed contracts on the same decoded start.
  have binary : (decrementTM 1 0).runFrom shadow ticks = result ∧
      (∀ u < ticks, ∀ b, ((decrementTM 1 0).runFrom shadow u).state ≠ some (.done b)) ∧
      ∀ u ≤ ticks, ((decrementTM 1 0).runFrom shadow u).workTapePos 0 ∈
        Finset.Icc (cp - 1) (cp + (w.length : ℤ)) := by
    cases borrow : decFixed w with
    | none =>
      have length := sc_dec_underflow_cost w borrow
      obtain ⟨endRun, noDone, bounds⟩ :=
        decrementTM_run_underflow_ofCfg 0 w borrow shadow ready digits
      refine ⟨?_, ?_, ?_⟩
      · simpa only [ticks, result, word, borrow, Option.isSome_none, Option.getD_none,
          length] using endRun
      · simpa only [ticks, length] using noDone
      · intro u hu
        have h := bounds 0 u (by simpa only [ticks, length] using hu)
        simpa only [if_pos rfl, pos, seed] using h
    | some v =>
      obtain ⟨endRun, noDone, bounds⟩ :=
        decrementTM_run_succ_ofCfg 0 w v borrow shadow ready digits
      refine ⟨?_, noDone, ?_⟩
      · simpa only [result, word, borrow, Option.isSome_some, Option.getD_some] using endRun
      · intro u hu
        have h := bounds 0 u hu
        simp only [pos, seed, Finset.mem_Icc] at h ⊢
        have length := (List.takeWhile_sublist (p := not) (l := w)).length_le
        constructor
        · exact h.1
        · have upper : ((decrementTM 1 0).runFrom shadow u).workTapePos 0 ≤
              cp + ((w.takeWhile not).length : ℤ) := h.2
          omega
  have silent : ((decrementTM 1 0).runFrom shadow ticks).output = [] := by
    rw [binary.1]
    exact Cfg.decodeSymbols_output e seed
  let rich := (decrementTM 1 0).liftSymbols e
  let placed := embedEmitTM (lastEmb k) rich
  let start : Cfg (k + 1) Γ FlagPhase x := clockCfg (some .run) c ct cp
  have bankStart : embedEmitCfg (lastEmb k) (Fin.lastCases ct c.workTapes)
      (Fin.lastCases cp c.workTapePos) [] seed = start :=
    sc_lastLayout c seed ct cp rfl rfl
  -- R1 and the field API identify the entire placed run, not only its endpoint.
  have placedRun (u : ℕ) (hu : u ≤ ticks) :
      placed.runFrom start u =
        clockCfg ((decrementTM 1 0).runFrom shadow u).state c
          ((rich.runFrom seed u).workTapes 0)
          (((decrementTM 1 0).runFrom shadow u).workTapePos 0) := by
    obtain ⟨ip, out, heads⟩ := sc_lift_frame e seed ticks silent u hu
    have control : (rich.runFrom seed u).state =
        ((decrementTM 1 0).runFrom shadow u).state := by
      rw [sc_lift_run, Cfg.liftOver_state]
    rw [← bankStart, embedEmitTM_runFrom, sc_lastLayout c _ ct cp ip out, control, heads]
  have transported (u : ℕ) (hu : u ≤ ticks) :
      H.runFrom (clockCfg (some (ρ .run)) c ct cp) u =
        clockCfg (((decrementTM 1 0).runFrom shadow u).state.map ρ) c
          ((rich.runFrom seed u).workTapes 0)
          (((decrementTM 1 0).runFrom shadow u).workTapePos 0) := by
    have guarded := MultiTapeTM.runFrom_mapState_of_agreeOn placed H ρ
      (fun f => ∀ b, f ≠ .done b) hagree start u (by
        intro t ht f hf b hfb
        have hstate := congrArg Cfg.state (placedRun t (by omega))
        have seen : ((decrementTM 1 0).runFrom shadow t).state = some (.done b) := by
          exact hstate.symm.trans (hf.trans (congrArg some hfb))
        exact binary.2.1 t (by omega) b seen)
    have initial : start.mapState ρ = clockCfg (some (ρ .run)) c ct cp := rfl
    rw [initial, placedRun u hu] at guarded
    exact guarded
  -- The overlay retains the rich frame; its changed interval is precisely the word patch.
  have finalTape : (rich.runFrom seed ticks).workTapes 0 = wordPatch ct cp (word.map e) := by
    funext p
    rw [sc_lift_run, binary.1, Cfg.liftOver_workTapes]
    have width : word.length = w.length := sc_dec_patch_width w
    simp only [result, pos, seed, true_and, wordPatch, List.length_map, width]
    by_cases inside : cp ≤ p ∧ p < cp + (w.length : ℤ)
    · simp only [if_pos inside, FinTM.bufferTape_map]
      by_cases unchanged : FinTM.bufferTape word (p - cp) = (ct p).bind (decodeBool e)
      · rw [if_pos unchanged]
        have index : (p - cp).toNat < word.length := by omega
        have digit : FinTM.bufferTape word (p - cp) = some word[(p - cp).toNat] := by
          simp [FinTM.bufferTape, inside.1, index]
        cases cell : ct p with
        | none => simp [cell, digit] at unchanged
        | some a =>
          have decode : decodeBool e a = some word[(p - cp).toNat] := by
            simpa only [cell, Option.bind_some, digit] using unchanged.symm
          rw [digit, Option.map_some, decodeBool_eq_some e a _ decode]
      · rw [if_neg unchanged]
    · simp only [if_neg inside]
      rw [show shadow.workTapes 0 p = (ct p).bind (decodeBool e) from
        Cfg.decodeSymbols_workTapes e seed 0 p, if_pos rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [transported ticks le_rfl, finalTape, binary.1]
    simp only [result, Option.map_some, pos, seed, word]
  · intro u hu b bad
    have state := congrArg Cfg.state (transported u hu.le)
    rw [state] at bad
    obtain ⟨f, hf, same⟩ := Option.map_eq_some_iff.mp bad
    exact binary.2.1 u hu b (hf.trans (congrArg some (ρ.injective same)))
  · intro u hu
    rw [transported u hu]
    simp only [clockCfg, Fin.lastCases_last]
    exact ⟨True.intro, binary.2.2 u hu⟩
  · intro u hu
    exact ⟨_, congrArg Cfg.state (transported u hu)⟩

/-- **A stop state leaves at once.** At `dec s .run` with `stopAt s`, one
step reaches `finish (some s)` and changes nothing else.

**Proof sketch.** Unfold one step: the stop branch is a stationary, silent, write-free
action. -/
private theorem sc_stop_step {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) {x : List Γ} (c : Cfg k Γ S x) (s : S)
    (hs : stopAt s = true) (ct : ℤ → Option Γ) (cp : ℤ) :
    (sc_clockTM e M stopAt).step (clockCfg (some (.dec s .run)) c ct cp) =
      clockCfg (some (.finish (some s))) c ct cp := by
  apply Cfg.ext <;> simp [MultiTapeTM.step, clockCfg, sc_clockTM, hs, moveInputPos]

/-- **One body transition.** From `body s` with the body configuration
`c` live at `s`, one host step is the body's own step on the body tapes, landing at the
successor's decrement entry, or at `finish none` if the transition halts the body; the counter
tape and its head are untouched.

**Proof sketch.** One R1 step (`Turing.embedEmitTM_runFrom` at time `1` along
`Fin.castSuccEmb`, with the counter tape as the frame, read through `sc_layout`), followed by
the landing map `sc_bodyAct`, which changes only the successor state. -/
private theorem sc_body_step {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) {x : List Γ} (c : Cfg k Γ S x) (s : S)
    (hs : c.state = some s) (ct : ℤ → Option Γ) (cp : ℤ) :
    (sc_clockTM e M stopAt).step (clockCfg (some (.body s)) c ct cp) =
      clockCfg (some (match (M.step c).state with
          | some s' => sc_State.dec s' .run
          | none => sc_State.finish none))
        (M.step c) ct cp := by
  have hE := embedEmitTM_runFrom Fin.castSuccEmb M (fun _ => ct) (fun _ => cp) [] c 1
  rw [sc_layout, sc_layout, hs] at hE
  simp only [MultiTapeTM.runFrom, Function.iterate_one] at hE
  rw [show (embedEmitTM Fin.castSuccEmb M).step (clockCfg (some s) c ct cp) =
      ((embedEmitTM Fin.castSuccEmb M).tr s (clockCfg (some s) c ct cp).inputSymbol
        (clockCfg (some s) c ct cp).workTapeSymbols).apply (clockCfg (some s) c ct cp)
      from rfl] at hE
  rw [show (sc_clockTM e M stopAt).step (clockCfg (some (sc_State.body s)) c ct cp) =
      ((sc_clockTM e M stopAt).tr (sc_State.body s)
        (clockCfg (some (sc_State.body s)) c ct cp).inputSymbol
        (clockCfg (some (sc_State.body s)) c ct cp).workTapeSymbols).apply
          (clockCfg (some (sc_State.body s)) c ct cp) from rfl]
  apply Cfg.ext
  · have h1 := congrArg Cfg.state hE
    simp only [Action.apply, clockCfg] at h1
    simp only [Action.apply, sc_clockTM, sc_bodyAct, clockCfg]
    exact congrArg (fun r => some (match r with
      | some s' => sc_State.dec s' .run
      | none => sc_State.finish none)) h1
  · have h := congrArg Cfg.inputPos hE
    exact h
  · have h := congrArg Cfg.workTapes hE
    exact h
  · have h := congrArg Cfg.workTapePos hE
    exact h
  · have h := congrArg Cfg.output hE
    exact h

/-- The two exit families, as the forbidden set of a clock segment. -/
private def sc_exits {S : Type} : Set (Option (sc_State S)) :=
  {q | ∃ r, q = some (.finish r) ∨ q = some (.timeout r)}

/-- The controller after a body step: resume a live body, or finish a halted body. -/
private def sc_resume {S : Type} : Option S → sc_State S
  | some s => .dec s .run
  | none => .finish none

/-- Observations of a finite run give a segment without unfolding the segment definition.

**Proof sketch.** Induct on its length, using only the public empty-segment and prepend
operations. Shift the observations by one step for the induction hypothesis. This is an
adapter to the existing segment interface, not a new span structure. -/
private theorem sc_observedSegment {k : ℕ} {Γ Q : Type} {x : List Γ}
    (N : MultiTapeTM k Γ Q) (F : Set (Option Q)) (P : (Fin k → ℤ) → Prop)
    (a : Cfg k Γ Q x) (t : ℕ)
    (cut : ∀ u < t, (N.runFrom a u).state ∉ F)
    (heads : ∀ u ≤ t, P (N.runFrom a u).workTapePos) :
    Segment N F P a (N.runFrom a t) t := by
  induction t generalizing a with
  | zero => exact Segment.zero (heads 0 le_rfl)
  | succ t ih =>
    have tail := ih (N.step a) (by
      intro u hu
      rw [← MultiTapeTM.runFrom_succ_eq_step]
      exact cut (u + 1) (by omega)) (by
      intro u hu
      rw [← MultiTapeTM.runFrom_succ_eq_step]
      exact heads (u + 1) (by omega))
    have joined := Segment.cons (M := N) rfl (cut 0 (by omega)) (heads 0 (by omega)) tail
    simpa only [Nat.succ_eq_add_one, Nat.add_comm 1,
      MultiTapeTM.runFrom_succ_eq_step] using joined

/-- A segment ending in its forbidden set has no earlier exit, through the public interface.

**Proof sketch.** An earlier exit would make the corresponding prefix another first-exit
segment. The public uniqueness theorem equates its length with the full segment's length. -/
private theorem sc_firstExit {k : ℕ} {Γ Q : Type} {x : List Γ}
    {N : MultiTapeTM k Γ Q} {F : Set (Option Q)} {P : (Fin k → ℤ) → Prop}
    {a b : Cfg k Γ Q x} {t : ℕ} (h : Segment N F P a b t) (last : b.state ∈ F) :
    ∀ u < t, (N.runFrom a u).state ∉ F := by
  intro u hu earlier
  have equal := Segment.time_eq (h.take hu.le) earlier h last
  omega

/-- A clock debit is a segment avoiding both exit families before its end.

**Proof sketch.** Instantiate the generic debit at the prescribed redirection. Its state-image
clause says every working state is a decrement state; its cut excludes both done phases.
Package these observations through the public segment constructors. -/
private theorem sc_clockDebit {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) {x : List Γ} (c : Cfg k Γ S x)
    (s : S) (hs : stopAt s = false) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    let H := sc_clockTM e M stopAt
    let a := clockCfg (some (sc_State.dec s .run)) c ct cp
    let b := clockCfg (some (sc_decExit s (.done (decFixed w).isSome))) c
      (wordPatch ct cp (((decFixed w).getD (List.replicate w.length true)).map e)) cp
    let t := 2 * (w.takeWhile not).length + 2
    H.runFrom a t = b ∧
      Segment H sc_exits (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1)
        (cp + (w.length : ℤ))) a b t ∧
      ∀ u ≤ t,
        H.runFrom a u = clockCfg (H.runFrom a u).state c
            ((H.runFrom a u).workTapes (Fin.last k))
            ((H.runFrom a u).workTapePos (Fin.last k)) ∧
          (H.runFrom a u).workTapePos (Fin.last k) ∈
            Finset.Icc (cp - 1) (cp + (w.length : ℤ)) := by
  intro H a b t
  obtain ⟨run, cut, frame, image⟩ := sc_debit e H
    ⟨sc_decExit s, sc_decExit_injective s⟩ (sc_agree e M stopAt s hs) c w ct cp hw
  change H.runFrom a t = b at run
  have avoid : ∀ u < t, (H.runFrom a u).state ∉ sc_exits := by
    intro u hu
    obtain ⟨f, hf⟩ := image u hu.le
    change (H.runFrom a u).state = f.map (sc_decExit s) at hf
    rintro ⟨r, exit⟩
    cases f with
    | none => simp [hf] at exit
    | some f =>
      cases f with
      | run => simp [hf, sc_decExit] at exit
      | rewind b => simp [hf, sc_decExit] at exit
      | done b => exact cut u hu b hf
  have seg := sc_observedSegment H sc_exits
    (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ))) a t
    avoid (fun u hu => (frame u hu).2)
  rw [run] at seg
  exact ⟨run, seg, frame⟩

/-- A body that has not stopped has a live state whose stop flag is false.
**Proof sketch.** Inspect its optional state and then its Boolean stop flag. -/
private theorem sc_live {k : ℕ} {Γ S : Type} {x : List Γ} (stopAt : S → Bool)
    (c : Cfg k Γ S x) (h : ¬c.Stopped stopAt) :
    ∃ s, c.state = some s ∧ stopAt s = false := by
  cases state : c.state with
  | none => exact False.elim (h (Or.inl state))
  | some s =>
    refine ⟨s, rfl, ?_⟩
    cases flag : stopAt s with
    | false => rfl
    | true => exact False.elim (h (Or.inr ⟨s, state, flag⟩))

/-- The first `n` physical body steps have the exact debit-plus-step cost and a full trajectory.

**Proof sketch.** Induct on `n`. The next counter word is supplied by the public decrement
bridge; same-width patches retain the original tape frame. Append the clock debit and the
single body action as segments. During the debit the body is at time `n`; after the action it
is at time `n + 1`. Keep this full-configuration observation separately from the segment's
head relation, so the input position and output use the same body time. -/
private theorem sc_rounds {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) {x : List Γ} (c : Cfg k Γ S x) (q : S)
    (hq : c.state = some q) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (n : ℕ) (budget : n ≤ Nat.ofDigits 2 (w.map Bool.toNat))
    (before : ∀ v < n, ¬(M.runFrom c v).Stopped stopAt) :
    let H := sc_clockTM e M stopAt
    let a := clockCfg (some (sc_State.dec q .run)) c ct cp
    H.runFrom a (counterOverhead w n + n) =
        clockCfg (some (sc_resume (M.runFrom c n).state)) (M.runFrom c n)
          (wordPatch ct cp ((counterWord w n).map e)) cp ∧
      Segment H sc_exits
        (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ))) a
        (clockCfg (some (sc_resume (M.runFrom c n).state)) (M.runFrom c n)
          (wordPatch ct cp ((counterWord w n).map e)) cp) (counterOverhead w n + n) ∧
      ∀ u ≤ counterOverhead w n + n, ∃ v ≤ n, ∃ z tape head,
        H.runFrom a u = clockCfg z (M.runFrom c v) tape head ∧
          head ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) := by
  intro H a
  induction n with
  | zero =>
    have initial := sc_wordPatch_self ct cp (w.map e) (by simpa using hw)
    rw [counterOverhead_zero, counterWord_zero]
    simp only [Nat.zero_add, MultiTapeTM.runFrom_zero, hq, sc_resume, initial]
    refine ⟨rfl, Segment.zero ?_, ?_⟩
    · simp [a, clockCfg, Finset.mem_Icc]
    · intro u hu
      obtain rfl : u = 0 := by omega
      exact ⟨0, le_rfl, some (.dec q .run), ct, cp, rfl, by simp [Finset.mem_Icc]⟩
  | succ n ih =>
    obtain ⟨reached, segment, trace⟩ := ih (by omega) (fun v hv => before v (by omega))
    obtain ⟨s, state, flag⟩ := sc_live stopAt (M.runFrom c n) (before n (by omega))
    simp only [state, sc_resume] at reached segment
    have wordNext := counter_word_decrement w n (by omega)
    have delimited := sc_wordPatch_frame ct cp (w.map e) ((counterWord w n).map e)
      (by simp only [List.length_map, counterWord_length]) (by simpa using hw)
    obtain ⟨debit, debitSegment, debitTrace⟩ := sc_clockDebit e M stopAt (M.runFrom c n) s flag
      (counterWord w n) (wordPatch ct cp ((counterWord w n).map e)) cp (by simpa using delimited)
    have overwrite := sc_wordPatch_twice ct cp ((counterWord w n).map e)
      ((counterWord w (n + 1)).map e) (by simp only [List.length_map, counterWord_length])
    simp only [wordNext, Option.isSome_some, Option.getD_some, sc_decExit, overwrite,
      counterWord_length] at debit debitSegment
    simp only [counterWord_length] at debitTrace
    let middle := clockCfg (some (sc_State.body s)) (M.runFrom c n)
      (wordPatch ct cp ((counterWord w (n + 1)).map e)) cp
    have action : H.step middle =
        clockCfg (some (sc_resume (M.runFrom c (n + 1)).state)) (M.runFrom c (n + 1))
          (wordPatch ct cp ((counterWord w (n + 1)).map e)) cp := by
      simpa only [MultiTapeTM.runFrom_succ_eq_step', sc_resume] using
        sc_body_step e M stopAt (M.runFrom c n) s state
          (wordPatch ct cp ((counterWord w (n + 1)).map e)) cp
    have bodySegment := Segment.one (M := H) (F := sc_exits)
      (P := fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)))
      (a := middle) (by rintro ⟨r, h⟩; simp [middle, clockCfg] at h)
      (by simp [middle, clockCfg, Finset.mem_Icc])
      (by rw [action]; simp [clockCfg, Finset.mem_Icc])
    rw [action] at bodySegment
    have combined := segment.trans (debitSegment.trans bodySegment)
    have time : counterOverhead w (n + 1) + (n + 1) = counterOverhead w n + n +
        ((2 * ((counterWord w n).takeWhile not).length + 2) + 1) := by
      rw [counterOverhead_succ]
      omega
    rw [time]
    refine ⟨?_, combined, ?_⟩
    · rw [MultiTapeTM.runFrom_add, reached, MultiTapeTM.runFrom_add, debit]
      exact action
    · intro u hu
      by_cases old : u ≤ counterOverhead w n + n
      · obtain ⟨v, hv, z, tape, head, seen, bound⟩ := trace u old
        exact ⟨v, by omega, z, tape, head, seen, bound⟩
      · have splitTime : u = counterOverhead w n + n + (u - (counterOverhead w n + n)) := by
          omega
        rw [splitTime, MultiTapeTM.runFrom_add, reached]
        by_cases during : u - (counterOverhead w n + n) ≤
            2 * ((counterWord w n).takeWhile not).length + 2
        · obtain ⟨seen, bound⟩ := debitTrace _ during
          exact ⟨n, by omega, _, _, _, seen, bound⟩
        · have last : u - (counterOverhead w n + n) =
              (2 * ((counterWord w n).takeWhile not).length + 2) + 1 := by omega
          rw [last, MultiTapeTM.runFrom_add, debit]
          change ∃ v ≤ n + 1, ∃ z tape head,
            H.step middle = clockCfg z (M.runFrom c v) tape head ∧ _
          rw [action]
          exact ⟨n + 1, le_rfl, _, _, cp, rfl, by simp [Finset.mem_Icc]⟩

/-- Package an exit segment and its joint trajectory into the headline's concrete clauses.

**Proof sketch.** First-exit uniqueness supplies the cut without unfolding `Segment`.
Read the body fields from each observed clock configuration, keeping the same source time
for every field. The endpoint word and the time bound are supplied by the caller. -/
private theorem sc_deliver {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) {x : List Γ} (c : Cfg k Γ S x) (q : S)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ) (τ B : ℕ)
    (exit : Option S → sc_State S) (w' : List Bool) (T : ℕ)
    (width : w'.length = w.length) (time : T ≤ B)
    (exit_mem : some (exit (M.runFrom c τ).state) ∈ sc_exits)
    (run : (sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) T =
      clockCfg (some (exit (M.runFrom c τ).state)) (M.runFrom c τ)
        (wordPatch ct cp (w'.map e)) cp)
    (seg : Segment (sc_clockTM e M stopAt) sc_exits
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)))
      (clockCfg (some (.dec q .run)) c ct cp)
      (clockCfg (some (exit (M.runFrom c τ).state)) (M.runFrom c τ)
        (wordPatch ct cp (w'.map e)) cp) T)
    (trace : ∀ u ≤ T, ∃ v ≤ τ, ∃ z tape head,
      (sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u =
        clockCfg z (M.runFrom c v) tape head ∧
      head ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ))) :
    ∃ T ≤ B, ∃ w' : List Bool, w'.length = w.length ∧
      (sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) T =
        clockCfg (some (exit (M.runFrom c τ).state)) (M.runFrom c τ)
          (wordPatch ct cp (w'.map e)) cp ∧
      (∀ u < T, ∀ r,
        ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).state ≠
            some (.finish r) ∧
        ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).state ≠
            some (.timeout r)) ∧
      ∀ u ≤ T, ∃ v ≤ τ,
        (∀ j : Fin k,
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapes
              j.castSucc = (M.runFrom c v).workTapes j ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapePos
              j.castSucc = (M.runFrom c v).workTapePos j) ∧
        ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).inputPos =
          (M.runFrom c v).inputPos ∧
        ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).output =
          (M.runFrom c v).output ∧
        ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapePos
            (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) := by
  refine ⟨T, time, w', width, run, ?_, ?_⟩
  · intro u hu r
    have avoid := sc_firstExit seg exit_mem u hu
    exact ⟨fun h => avoid ⟨r, Or.inl h⟩, fun h => avoid ⟨r, Or.inr h⟩⟩
  · intro u hu
    obtain ⟨v, hv, z, tape, head, seen, bound⟩ := trace u hu
    refine ⟨v, hv, ?_, ?_, ?_, ?_⟩
    · intro j
      rw [seen]
      simp [clockCfg]
    · rw [seen]; rfl
    · rw [seen]; rfl
    · rw [seen]
      simpa only [clockCfg, Fin.lastCases_last] using bound

/-- **The finish clause** of `Turing.exists_stepClockTMVia` for the
fused clock, word for word with `H := sc_clockTM e M stopAt`, `inj s := dec s .run` and
`finish := sc_State.finish`.

**Proof sketch.** Rounds `r < τ`: from `dec (state of c_r) .run` with the counter at
`counterWord w r` (value `d - r > 0`), `sc_debit` at `ρ := sc_decExit _` (agreement
`sc_agree`), then `sc_body_step`; each round is a `Turing.Segment` against the exits, joined by
`Turing.Segment.trans`. The counter word of round `r + 1` is `Turing.counter_word_decrement`'s
successor, its tape `sc_wordPatch_twice` and `sc_wordPatch_frame` of round `r`'s (round `0` by
`Turing.counterWord_zero` and `sc_wordPatch_self`). Time: `counterOverhead w τ + τ ≤ 5τ + 2|w|`
(`Turing.counterOverhead_succ`, `Turing.counterOverhead_le_of_le`), plus one step of
`sc_stop_step` if the stop is a live stop state; a halting last transition lands on
`finish none` directly. -/
private theorem sc_finish {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) {x : List Γ} (c : Cfg k Γ S x) (q : S)
    (hq : c.state = some q) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    ∀ τ ≤ Nat.ofDigits 2 (w.map Bool.toNat), (M.runFrom c τ).Stopped stopAt →
      (∀ u < τ, ¬(M.runFrom c u).Stopped stopAt) →
      ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ w' : List Bool, w'.length = w.length ∧
        (sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) T =
          clockCfg (some (.finish (M.runFrom c τ).state)) (M.runFrom c τ)
            (wordPatch ct cp (w'.map e)) cp ∧
        (∀ u < T, ∀ r,
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).state ≠
              some (.finish r) ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).state ≠
              some (.timeout r)) ∧
        ∀ u ≤ T, ∃ v ≤ τ,
          (∀ j : Fin k,
            ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapes
                j.castSucc = (M.runFrom c v).workTapes j ∧
            ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapePos
                j.castSucc = (M.runFrom c v).workTapePos j) ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).inputPos =
            (M.runFrom c v).inputPos ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).output =
            (M.runFrom c v).output ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapePos
              (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) := by
  intro τ budget stopped before
  obtain ⟨reached, segment, trajectory⟩ := sc_rounds e M stopAt c q hq w ct cp hw τ budget before
  have amortized := counterOverhead_le_of_le w τ budget
  cases state : (M.runFrom c τ).state with
  | none =>
    rw [← state]
    apply sc_deliver e M stopAt c q w ct cp τ (5 * τ + 2 * w.length + 2)
      sc_State.finish (counterWord w τ) (counterOverhead w τ + τ)
      (counterWord_length w τ) (by omega) ⟨_, Or.inl rfl⟩
    · simpa only [state, sc_resume] using reached
    · simpa only [state, sc_resume] using segment
    · exact trajectory
  | some s =>
    have flag : stopAt s = true := by
      rcases stopped with halt | ⟨r, hr, hflag⟩
      · exact False.elim (Option.noConfusion (state.symm.trans halt))
      · have same : r = s := Option.some.inj (hr.symm.trans state)
        simpa only [same] using hflag
    simp only [state, sc_resume] at reached segment
    let lastStart := clockCfg (some (sc_State.dec s .run)) (M.runFrom c τ)
      (wordPatch ct cp ((counterWord w τ).map e)) cp
    have dispatch : (sc_clockTM e M stopAt).step lastStart =
        clockCfg (some (sc_State.finish (some s))) (M.runFrom c τ)
          (wordPatch ct cp ((counterWord w τ).map e)) cp :=
      sc_stop_step e M stopAt (M.runFrom c τ) s flag
        (wordPatch ct cp ((counterWord w τ).map e)) cp
    have finalSegment := Segment.one (M := sc_clockTM e M stopAt) (F := sc_exits)
      (P := fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)))
      (a := lastStart) (by rintro ⟨r, h⟩; simp [lastStart, clockCfg] at h)
      (by simp [lastStart, clockCfg, Finset.mem_Icc])
      (by rw [dispatch]; simp [clockCfg, Finset.mem_Icc])
    rw [dispatch] at finalSegment
    have joined := segment.trans finalSegment
    rw [← state]
    apply sc_deliver e M stopAt c q w ct cp τ (5 * τ + 2 * w.length + 2)
      sc_State.finish (counterWord w τ) (counterOverhead w τ + τ + 1)
      (counterWord_length w τ) (by omega) ⟨_, Or.inl rfl⟩
    · rw [MultiTapeTM.runFrom_add, reached]
      simpa only [state] using dispatch
    · simpa only [state] using joined
    · intro u hu
      by_cases old : u ≤ counterOverhead w τ + τ
      · exact trajectory u old
      · have last : u = counterOverhead w τ + τ + 1 := by omega
        rw [last, MultiTapeTM.runFrom_add, reached]
        change ∃ v ≤ τ, ∃ z tape head,
          (sc_clockTM e M stopAt).step lastStart = clockCfg z (M.runFrom c v) tape head ∧ _
        rw [dispatch]
        exact ⟨τ, le_rfl, _, _, cp, rfl, by simp [Finset.mem_Icc]⟩

/-- **The timeout clause** of `Turing.exists_stepClockTMVia` for the fused
clock, word for word with `H := sc_clockTM e M stopAt`, `inj s := dec s .run` and
`timeout := sc_State.timeout`.

**Proof sketch.** The `d` rounds of `sc_finish`'s proof, then at round `d` the counter word has
value `0` (`Turing.counterWord_value`), so it underflows (`Turing.counter_dec_zero`) and
`sc_debit` reaches `timeout (some _)`, with the counter all `true`. Time:
`counterOverhead w (d + 1) + d ≤ 5d + 2|w| + 2` (`Turing.counterOverhead_succ`,
`Turing.counterOverhead_le`). -/
private theorem sc_timeout {k : ℕ} {Γ S : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (stopAt : S → Bool) {x : List Γ} (c : Cfg k Γ S x) (q : S)
    (hq : c.state = some q) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    (∀ u ≤ Nat.ofDigits 2 (w.map Bool.toNat), ¬(M.runFrom c u).Stopped stopAt) →
      ∃ T ≤ 5 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2,
        ∃ w' : List Bool, w'.length = w.length ∧
        (sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) T =
          clockCfg (some (.timeout (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))).state))
            (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat)))
            (wordPatch ct cp (w'.map e)) cp ∧
        (∀ u < T, ∀ r,
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).state ≠
              some (.finish r) ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).state ≠
              some (.timeout r)) ∧
        ∀ u ≤ T, ∃ v ≤ Nat.ofDigits 2 (w.map Bool.toNat),
          (∀ j : Fin k,
            ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapes
                j.castSucc = (M.runFrom c v).workTapes j ∧
            ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapePos
                j.castSucc = (M.runFrom c v).workTapePos j) ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).inputPos =
            (M.runFrom c v).inputPos ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).output =
            (M.runFrom c v).output ∧
          ((sc_clockTM e M stopAt).runFrom (clockCfg (some (.dec q .run)) c ct cp) u).workTapePos
              (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) := by
  intro notStopped
  let d := Nat.ofDigits 2 (w.map Bool.toNat)
  obtain ⟨reached, segment, trajectory⟩ := sc_rounds e M stopAt c q hq w ct cp hw d le_rfl
    (fun u hu => notStopped u hu.le)
  obtain ⟨s, state, flag⟩ := sc_live stopAt (M.runFrom c d) (notStopped d le_rfl)
  simp only [state, sc_resume] at reached segment
  have exhausted : decFixed (counterWord w d) = none := by
    apply (counter_dec_zero _).mpr
    have value := counterWord_value w d le_rfl
    simpa only [d, Nat.sub_self] using value
  have delimited := sc_wordPatch_frame ct cp (w.map e) ((counterWord w d).map e)
    (by simp only [List.length_map, counterWord_length]) (by simpa using hw)
  obtain ⟨debit, debitSegment, debitTrace⟩ := sc_clockDebit e M stopAt (M.runFrom c d) s flag
    (counterWord w d) (wordPatch ct cp ((counterWord w d).map e)) cp (by simpa using delimited)
  simp only [exhausted, Option.isSome_none, Option.getD_none, sc_decExit,
    counterWord_length] at debit debitSegment debitTrace
  have overwrite := sc_wordPatch_twice ct cp ((counterWord w d).map e)
    ((List.replicate w.length true).map e)
    (by simp only [List.length_map, List.length_replicate, counterWord_length])
  rw [overwrite] at debit debitSegment
  have joined := segment.trans debitSegment
  let T := counterOverhead w d + d + (2 * ((counterWord w d).takeWhile not).length + 2)
  have bound : T ≤ 5 * d + 2 * w.length + 2 := by
    have amortized := counterOverhead_le w
    rw [counterOverhead_succ] at amortized
    dsimp only [T, d]
    omega
  apply sc_deliver e M stopAt c q w ct cp d (5 * d + 2 * w.length + 2)
    sc_State.timeout (List.replicate w.length true) T (by simp) bound
    ⟨_, Or.inr rfl⟩
  · change (sc_clockTM e M stopAt).runFrom _
      (counterOverhead w d + d + (2 * ((counterWord w d).takeWhile not).length + 2)) = _
    rw [MultiTapeTM.runFrom_add, reached, debit, state]
  · simpa only [state] using joined
  · intro u hu
    by_cases old : u ≤ counterOverhead w d + d
    · exact trajectory u old
    · have splitTime : u = counterOverhead w d + d + (u - (counterOverhead w d + d)) := by
        omega
      rw [splitTime, MultiTapeTM.runFrom_add, reached]
      obtain ⟨seen, envelope⟩ := debitTrace (u - (counterOverhead w d + d)) (by
        dsimp only [T] at hu
        omega)
      exact ⟨d, le_rfl, _, _, _, seen, envelope⟩

/-- **H3's clock, the step-clocked runner** (joint statement with C1, whose draft
`exists_stepClockTM` is the instance `Γ = Bool`, `e = refl`; generalized to any alphabet with
a digit embedding, as the windowed runner runs over the record alphabet). For a body `M` with
designated stop states, there is a host on one more tape, with an injection `inj` of the body
states and two exit families `finish` and `timeout` carrying the body state, all distinct, as
follows. Start it at `inj q` with the body configuration `c` (live, at `q`) and a delimited
counter word `w` of value `d` (digits embedded by `e`) on the last tape.
* If the body first stops (halts, or reaches a stop state) at time `τ ≤ d`, the host reaches
  `finish` with the body's configuration at `τ`, within `5τ + 2|w| + 2` steps.
* If the body has not stopped by time `d`, the host reaches `timeout` with the body's
  configuration at time `d`, within `5d + 2|w| + 2` steps.

In both cases no exit occurs earlier; the counter tape differs from its start only on the
counter word's own cells, which hold some word of the same width, and its head is back at
`cp`; and at every host time up to the exit the host's body tapes, body heads, input head and
output are the body's at some body time no later than `τ` (or `d`), while the counter head
stays in `[cp - 1, cp + |w|]`. So the host's work space is the body's plus `|w| + 2`, and it
emits exactly what the body emits. This clock counts **physical body steps**, unlike the round
counter `Turing.counterLoopTMVia`, so a body's state survives from step to step. [AB09, §3.2,
proof of Theorem 3.2; §4.1.3, Theorem 4.8 with Exercise 4.1; the fused construction is the
repository's refinement]

**Proof sketch.** Fuse one decrement with every body transition: from `inj s`, if `s` is a stop
state go to `finish`; otherwise run the lifted decrement on the counter tape
(`Turing.decrementTM_run_succ_ofCfg` under `Turing.MultiTapeTM.liftSymbols`), whose success
anchor performs one body transition (the body tapes embedded by R1 along `Fin.castSucc`, as in
`Turing.counterLoopTMVia`) and returns to `inj` of the successor, or to `finish none` when the
transition halts the body; the decrement's underflow anchor is `timeout`. The decrement costs
sum to at most `4τ + 2|w|` (`Turing.counterOverhead_le_of_le`), plus the final underflow sweep
`2|w| + 2` in the timeout case (`Turing.counterOverhead_le`). The round induction is that of
`Turing.counterLoopTMVia_run_done` with one body step per round and an unrestricted body
state. A decrement moves only the counter head and writes only the counter tape, and a body
transition is the body's own step on the body tapes, which gives the frame clause. 

**Fill appendix (B6-F1).** The prescribed controller and headline glue are retained. The
proved generic debit additionally records its optional phase image, which excludes unrelated
host exits. The round induction keeps one joint full-configuration trajectory; the two exits
share its packaging into the headline. Segments are introduced through `Segment.zero` and
`Segment.cons`, concatenated through `Segment.trans`, and read for first-exit information
through `Segment.take` and `Segment.time_eq`; their definition is never unfolded. The timeout
uses the whole decrement-plus-underflow bound. The only extra step on finish is a live stop
dispatch; a halting body transition finishes directly. No admission remains. -/
theorem exists_stepClockTMVia {k : ℕ} {Γ S : Type} [Fintype S] [DecidableEq S]
    [DecidableEq Γ] (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (stopAt : S → Bool) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : MultiTapeTM (k + 1) Γ Q)
      (inj : S → Q) (finish timeout : Option S → Q),
      Function.Injective finish ∧ Function.Injective timeout ∧
      (∀ a b, finish a ≠ timeout b) ∧ (∀ s r, inj s ≠ finish r ∧ inj s ≠ timeout r) ∧
      ∀ {x : List Γ} (c : Cfg k Γ S x) (q : S), c.state = some q →
      ∀ (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ),
        (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p) →
        (∀ τ ≤ Nat.ofDigits 2 (w.map Bool.toNat), (M.runFrom c τ).Stopped stopAt →
          (∀ u < τ, ¬(M.runFrom c u).Stopped stopAt) →
          ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ w' : List Bool, w'.length = w.length ∧
            H.runFrom (clockCfg (some (inj q)) c ct cp) T =
              clockCfg (some (finish (M.runFrom c τ).state)) (M.runFrom c τ)
                (wordPatch ct cp (w'.map e)) cp ∧
            (∀ u < T, ∀ r,
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (finish r) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)) ∧
            ∀ u ≤ T, ∃ v ≤ τ,
              (∀ j : Fin k,
                (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapes j.castSucc =
                  (M.runFrom c v).workTapes j ∧
                (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapePos j.castSucc =
                  (M.runFrom c v).workTapePos j) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).inputPos =
                (M.runFrom c v).inputPos ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).output =
                (M.runFrom c v).output ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapePos (Fin.last k) ∈
                Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
        ((∀ u ≤ Nat.ofDigits 2 (w.map Bool.toNat), ¬(M.runFrom c u).Stopped stopAt) →
          ∃ T ≤ 5 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2,
            ∃ w' : List Bool, w'.length = w.length ∧
            H.runFrom (clockCfg (some (inj q)) c ct cp) T =
              clockCfg (some (timeout (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))).state))
                (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat)))
                (wordPatch ct cp (w'.map e)) cp ∧
            (∀ u < T, ∀ r,
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (finish r) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)) ∧
            ∀ u ≤ T, ∃ v ≤ Nat.ofDigits 2 (w.map Bool.toNat),
              (∀ j : Fin k,
                (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapes j.castSucc =
                  (M.runFrom c v).workTapes j ∧
                (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapePos j.castSucc =
                  (M.runFrom c v).workTapePos j) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).inputPos =
                (M.runFrom c v).inputPos ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).output =
                (M.runFrom c v).output ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).workTapePos (Fin.last k) ∈
                Finset.Icc (cp - 1) (cp + (w.length : ℤ))) := by
  refine ⟨sc_State S, inferInstance, inferInstance, sc_clockTM e M stopAt,
    fun s => .dec s .run, sc_State.finish, sc_State.timeout,
    fun _ _ h => sc_State.finish.inj h, fun _ _ h => sc_State.timeout.inj h,
    fun _ _ h => sc_State.noConfusion h,
    fun _ _ => ⟨fun h => sc_State.noConfusion h, fun h => sc_State.noConfusion h⟩, ?_⟩
  intro x c q hq w ct cp hw
  exact ⟨sc_finish e M stopAt c q hq w ct cp hw, sc_timeout e M stopAt c q hq w ct cp hw⟩

/-- **C1's step clock** (the `Bool` instance of `Turing.exists_stepClockTMVia`). This is the
statement of C1's draft `exists_stepClockTM` (`audits/evidence/c1/C1HostsDraft.lean.txt`, §4)
word for word: over `Bool`, with the counter tape's final contents left existential and without
the frame clause. It is proved here from the joint statement, so C1 may cite either.
[AB09, §3.2, proof of Theorem 3.2]

**Proof sketch.** Instantiate the joint statement at `e := Function.Embedding.refl Bool`
(`w.map e = w`) and forget the extra clauses. -/
theorem exists_stepClockTM {k : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (M : MultiTapeTM k Bool S) (stopAt : S → Bool) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : MultiTapeTM (k + 1) Bool Q)
      (inj : S → Q) (finish timeout : Option S → Q),
      ∀ {x : List Bool} (c : Cfg k Bool S x) (q : S), c.state = some q →
      ∀ (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ),
        (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p) →
        let d := Nat.ofDigits 2 (w.map Bool.toNat)
        let stopped : Cfg k Bool S x → Prop := fun e =>
          e.state = none ∨ ∃ s, e.state = some s ∧ stopAt s = true
        (∀ τ ≤ d, stopped (M.runFrom c τ) → (∀ u < τ, ¬stopped (M.runFrom c u)) →
          ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ ct' : ℤ → Option Bool,
            H.runFrom (clockCfg (some (inj q)) c ct cp) T =
              clockCfg (some (finish (M.runFrom c τ).state)) (M.runFrom c τ) ct' cp ∧
            ∀ u < T, ∀ r, (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠
              some (finish r) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)) ∧
        ((∀ u ≤ d, ¬stopped (M.runFrom c u)) →
          ∃ T ≤ 5 * d + 2 * w.length + 2, ∃ ct' : ℤ → Option Bool,
            H.runFrom (clockCfg (some (inj q)) c ct cp) T =
              clockCfg (some (timeout (M.runFrom c d).state)) (M.runFrom c d) ct' cp ∧
            ∀ u < T, ∀ r, (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠
              some (finish r) ∧
              (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)) := by
  obtain ⟨Q, hQ, dQ, H, inj, finish, timeout, -, -, -, -, h⟩ :=
    exists_stepClockTMVia (Function.Embedding.refl Bool) M stopAt
  refine ⟨Q, hQ, dQ, H, inj, finish, timeout, ?_⟩
  intro x c q hq w ct cp hw
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    have hid : w.map (Function.Embedding.refl Bool) = w := by
      rw [Function.Embedding.coe_refl, List.map_id]
    rw [hid]
    exact hw
  obtain ⟨hfin, hto⟩ := h c q hq w ct cp hw'
  refine ⟨fun τ hτ hs hmin => ?_, fun hns => ?_⟩
  · obtain ⟨T, hT, w', -, hrun, hcut, -⟩ := hfin τ hτ hs hmin
    exact ⟨T, hT, _, hrun, hcut⟩
  · obtain ⟨T, hT, w', -, hrun, hcut, -⟩ := hto hns
    exact ⟨T, hT, _, hrun, hcut⟩

end Turing
