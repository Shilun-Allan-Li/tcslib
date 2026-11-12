/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.StepBlock
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.VirtualInput

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The step block's counter loop (H2's loop form)

**Status: proved; statement gate passed** (2026-10-14,
`audits/h1-harvest-statements-findings.md`: PASS, 0 blockers, 0 majors, 4 minors; resolutions
`audits/h1-harvest-statements-resolutions.md`).

**H2's loop form**, the clocked interpreter loop of `machine-library-design.md` §14: the binary
counter loop `Turing.counterLoopTM` (§12.7) whose round is one simulated transition of the step
block `Turing.StepBlock.roundTM` (host H2), and the same loop hosted on a buffered input by the
forwarding virtual-input transformer `Turing.vhostEmitTM` (Z1, §13). One finite machine per
work-tape count `k` runs any `k`-work-tape binary transition table, held as data in the
`Turing.tableBitsK` layout, for as many simulated steps as a binary counter says, and leaves
through one of two live exits: `done` when the deadline passes with the simulated machine still
live, `escape` when the simulated machine halts first.

**Harvested** from the private assembly of B5a's H1 continuation 2 in
`TuringMachine/CodeSimulator.lean` (fills-8; renamed from the `h1…` names, which belong to that
brief and not to host H1 of the registry), as ruling 5 of the C1 host-contracts gate
(`audits/c1-hosts-statements-findings.md`) requires before the brief of the interpreter core
`Turing.exists_ndInterpreterCore`. The private contracts are generalized in three ways:
* **an arbitrary represented live start**: the simulated run starts from any live
  configuration that the step block's seam relation `Turing.StepBlock.Rep` represents, not only
  the initial one, for instance the replay machine's initial configuration with the choice
  stream already on its choice tape (`Turing.NDTM.withChoiceTape`);
* **the early-escape time bound**: when the simulated run halts by `t' ≤ t`, the loop exits
  within `t'·B + 4t' + 2|w|`, linear in `t'` and not in the deadline `t` (the counter word's
  width `|w|` aside);
* **live exits usable by the caller**: the two exits are live control states with the exact
  endpoint configuration, the cut at both exits for every boundary tag, the counter frame, and
  `Turing.StepBlock.hostedLoop_read` for the verdict cell under its head.
The counter is any delimited binary word of value `t`, in any frame, as in the counter loop's
own contracts.

## Design

* **No round-time function in a statement.** The rounds are indexed, in the proofs only, by the
  first positive return of the block to either exit, defined by `Nat.find` (formerly
  `h1RoundTime`). It stays private until MIG-0b's round adapter makes the round time public
  (H2 design note O7, `audits/evidence/h2/r2/H2-design-r2.md` §5). Its specification now takes
  its uniqueness step from `Turing.StepBlock.roundTM_firstExit_unique` instead of re-proving it.
* **No orbit in a statement.** The public statements are existential in the time and the
  endpoint and do not mention `Turing.counterLoopOrbit` (since MIG-0b an abbreviation of the
  core's `Turing.roundOrbit`); the proofs never unfold the orbit, and take its successor equation
  from `Turing.roundOrbit_succ`. The private `h1Clock_orbit` unfolded it, which is why MIG-0b had
  to edit that proof.
* **The one-bit verdict stays with its consumer.** `CodeSimulator`'s `h1HostedVerdictTM`, which
  replaces both exits by a halting emission for the deterministic uniform simulator, and the
  semantic clock `summaryClock` stay there and cite this module.

## Main definitions

* `Turing.StepBlock.loopTM` — the step block's counter loop (formerly `h1ClockTM`).
* `Turing.StepBlock.hostedLoopTM` — the loop on a buffered input (formerly `h1HostedClockTM`).

## Main results

* `Turing.StepBlock.loopTM_run` — the loop's contract from any represented live start, with the
  full-budget and the early-escape bounds (generalizing the former private
  `h1Clock_effect`).
* `Turing.StepBlock.hostedLoopTM_run` — the same, hosted on a buffered input (generalizing the
  former private `h1HostedClock_effect`).
* `Turing.StepBlock.hostedLoop_read` — the control, native head, output and verdict cell of a
  hosted loop configuration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, the proof of Theorem 1.9: the universal machine
  simulates one step at a time; §3.1, the proof of Theorem 3.1: the universal simulation run
  for a bounded number of steps.)
-/

namespace Turing

namespace StepBlock

/-! ## The machines -/

/-- **The step block's counter loop** (H2's loop form; formerly the private `h1ClockTM` of
`CodeSimulator`): the counter-driven loop host `Turing.counterLoopTM` whose body is the step
block `roundTM k`, whose round anchor is the block's entry `exit k true`, and whose designated
body exit is the block's live halting exit `exit k false`. Its `k + 3` work tapes are the
block's `k + 2` and the binary counter last. It starts with a decrement; each successful
decrement runs one round of the block, that is, one simulated transition; an underflow leaves
through the live anchor `done`, and a simulated halt through the live anchor `escape`. Its
control does not depend on the simulated table. [AB09, §1.4.1, proof of Theorem 1.9; §3.1,
proof of Theorem 3.1: the simulation run for a bounded number of steps] -/
def loopTM (k : ℕ) : MultiTapeTM (k + 2 + 1) Bool (CounterLoopState (Σ key, Ph k key)) :=
  counterLoopTM (roundTM k) (exit k true) (some (exit k false))

/-- **The step block's counter loop on a buffered input** (formerly `h1HostedClockTM`): the
loop `loopTM k` hosted by the forwarding virtual-input transformer `Turing.vhostEmitTM` (Z1).
Its `1 + (k + 3)` work tapes are the buffer, which holds the simulated input, and then the
loop's tapes; its control is the loop's paired with Z1's boundary tag; it never moves the native
input head, and it forwards the loop's (empty) emissions. [AB09, §1.4.1] -/
def hostedLoopTM (k : ℕ) :
    MultiTapeTM (1 + (k + 2 + 1)) Bool (CounterLoopState (Σ key, Ph k key) × Bool) :=
  vhostEmitTM (loopTM k)

/-! ## The rounds (internal) -/

/-- The first positive return of the step block to either of its exits (`0` if there is none),
the round index of the loop's proofs (formerly `h1RoundTime`, moved unchanged). It is a proof
index, not a machine that computes a time, and it stays private until MIG-0b's round adapter
(H2 design O7). -/
private noncomputable def loopRoundTime {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (Σ key, Ph k key) x) : ℕ := by
  classical
  exact if h : ∃ t, 0 < t ∧ ∃ b, ((roundTM k).runFrom d t).state =
      some (exit k b) then Nat.find h else 0

/-- The next round of the loop's orbit starts where the current one ends: the core's
`Turing.roundOrbit_succ` (MIG-0b), read through the abbreviation `Turing.counterLoopOrbit`, so
that the orbit lemmas below rewrite by it and never unfold the orbit. -/
private lemma loopOrbit_succ {k : ℕ} {x : List Bool}
    (d : Cfg (k + 2) Bool (Σ key, Ph k key) x) (r : ℕ) :
    counterLoopOrbit (roundTM k) loopRoundTime d (r + 1) =
      (roundTM k).runFrom (counterLoopOrbit (roundTM k) loopRoundTime d r)
        (loopRoundTime (counterLoopOrbit (roundTM k) loopRoundTime d r)) :=
  roundOrbit_succ (roundTM k) loopRoundTime d r

/-- The round index inherits the step block's endpoint, cut, silence and bound at a live
represented entry (formerly `h1RoundTime_spec`; the same statement).

**Proof sketch.** The block's contract `roundTM_effect` supplies a positive exit time `T` with
its endpoint, cut, silence and bound. The least positive exit time and `T` are both first
positive exits, so they are equal by `roundTM_firstExit_unique`; this replaces the private
proof's own uniqueness argument (H2 design O7). -/
private lemma loopRoundTime_spec {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (live : c.state ≠ none) (d : Cfg (k + 2) Bool (Σ key, Ph k key) x)
    (entry : d.state = some (exit k true)) (rel : Rep M.tr c d) :
    0 < loopRoundTime d ∧ loopRoundTime d ≤ 50 * ((tableBitsK M.tr).length + 1) ∧
      let e := (roundTM k).runFrom d (loopRoundTime d)
      e.state = some (exit k (M.step c).state.isSome) ∧
      Rep M.tr (M.step c) e ∧ e.output = d.output ∧
      (∀ u, 0 < u → u < loopRoundTime d → ∃ s,
        ((roundTM k).runFrom d u).state = some s ∧
          s ≠ exit k true ∧ s ≠ exit k false) := by
  classical
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp live
  obtain ⟨T, positive, bound, state, related, _, cut, silent, _⟩ :=
    roundTM_effect M.tr c q hq d entry rel
  have step : M.step c = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    simp only [MultiTapeTM.step, hq]
  have existsExit : ∃ t, 0 < t ∧ ∃ b,
      ((roundTM k).runFrom d t).state = some (exit k b) :=
    ⟨T, positive, _, state⟩
  have exits (u : ℕ) : (∃ b, ((roundTM k).runFrom d u).state = some (exit k b)) ↔
      (((roundTM k).runFrom d u).state = some ⟨.entry, ()⟩ ∨
        ((roundTM k).runFrom d u).state = some ⟨.halt, ()⟩) := by
    constructor
    · rintro ⟨b, hb⟩
      cases b
      · exact Or.inr hb
      · exact Or.inl hb
    · rintro (h | h)
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
  obtain ⟨T', -, unique⟩ := roundTM_firstExit_unique M.tr c q hq d entry rel
  have first (V : ℕ) (hV : 0 < V ∧ ∃ b, ((roundTM k).runFrom d V).state = some (exit k b))
      (before : ∀ u, 0 < u → u < V →
        ¬∃ b, ((roundTM k).runFrom d u).state = some (exit k b)) : V = T' :=
    unique V ⟨hV.1, (exits V).mp hV.2, fun u hu huV => by
      have h := before u hu huV
      rw [exits u] at h
      exact ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩⟩
  have least : Nat.find existsExit = T := by
    rw [first (Nat.find existsExit) (Nat.find_spec existsExit)
      (fun u hu hlt h => Nat.find_min existsExit hlt ⟨hu, h⟩)]
    refine (first T ⟨positive, _, state⟩ (fun u hu huT => ?_)).symm
    obtain ⟨s, hs, he, hh⟩ := cut u hu huT
    rintro ⟨b, hb⟩
    have equal : s = exit k b := Option.some.inj (hs.symm.trans hb)
    cases b
    · exact hh equal
    · exact he equal
  have duration : loopRoundTime d = T := by
    simp only [loopRoundTime, dif_pos existsExit, least]
  rw [duration]
  exact ⟨positive, bound, by simpa only [step] using state,
    by simpa only [step] using related, silent T le_rfl, cut⟩

/-- **The orbit invariant** (formerly `h1Clock_orbit`, generalized from the initial
configuration to any live start `c`): while the source run from `c` is live before round `r`,
the block's orbit after `r` rounds is at the exit that records whether the source is still live
after `r` steps, represents the source's configuration after `r` steps, and has emitted nothing.

**Proof sketch.** Induct on `r`. Each live source configuration uses the block's contract at
its round index (`loopRoundTime_spec`); the successor equation of the orbit and the source's
run-addition law identify the next configuration; each round keeps the output. -/
private lemma loopOrbit_rep {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (start : c.state ≠ none) (d : Cfg (k + 2) Bool (Σ key, Ph k key) x)
    (entry : d.state = some (exit k true)) (rel : Rep M.tr c d)
    (r : ℕ) (live : ∀ u < r, (M.runFrom c u).state ≠ none) :
    let e := counterLoopOrbit (roundTM k) loopRoundTime d r
    e.state = some (exit k (M.runFrom c r).state.isSome) ∧
      Rep M.tr (M.runFrom c r) e ∧ e.output = d.output := by
  induction r with
  | zero =>
    dsimp only
    rw [MultiTapeTM.runFrom_zero, Option.isSome_iff_ne_none.mpr start]
    exact ⟨entry, rel, rfl⟩
  | succ r ih =>
    obtain ⟨state, related, output⟩ := ih (fun u hu => live u (by omega))
    have alive := live r (by omega)
    have anchor :
        (counterLoopOrbit (roundTM k) loopRoundTime d r).state = some (exit k true) := by
      simpa only [Option.isSome_iff_ne_none.mpr alive] using state
    obtain ⟨_, _, hs, hr, ho, _⟩ := loopRoundTime_spec M (M.runFrom c r) alive
      (counterLoopOrbit (roundTM k) loopRoundTime d r) anchor related
    dsimp only
    rw [loopOrbit_succ, MultiTapeTM.runFrom_succ_eq_step']
    exact ⟨hs, hr, ho.trans output⟩

/-- **A live round** (formerly `h1Clock_round`, generalized to any start `c`): while the source
is live up to step `r`, the loop's round `r` starts at the anchor and lasts a positive time at
most `50·(|tableBitsK M.tr| + 1)`, strictly inside which the block is at neither exit.

**Proof sketch.** The orbit invariant at `r` puts the orbit at the anchor, the source being
live at `r`; the round index's specification at that live represented configuration gives the
positive bounded time and the cut. -/
private lemma loopOrbit_round {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (d : Cfg (k + 2) Bool (Σ key, Ph k key) x)
    (entry : d.state = some (exit k true)) (rel : Rep M.tr c d)
    (r : ℕ) (live : ∀ u ≤ r, (M.runFrom c u).state ≠ none) :
    let e := counterLoopOrbit (roundTM k) loopRoundTime d r
    e.state = some (exit k true) ∧
      0 < loopRoundTime e ∧ loopRoundTime e ≤ 50 * ((tableBitsK M.tr).length + 1) ∧
      (∀ u, 0 < u → u < loopRoundTime e → ∃ s,
        ((roundTM k).runFrom e u).state = some s ∧
          s ≠ exit k true ∧ s ≠ exit k false) := by
  have start : c.state ≠ none := by simpa using live 0 (Nat.zero_le r)
  obtain ⟨state, related, _⟩ := loopOrbit_rep M c start d entry rel r
    (fun u hu => live u (Nat.le_of_lt hu))
  have alive := live r le_rfl
  have anchor :
      (counterLoopOrbit (roundTM k) loopRoundTime d r).state = some (exit k true) := by
    simpa only [Option.isSome_iff_ne_none.mpr alive] using state
  obtain ⟨positive, bound, _, _, _, cut⟩ := loopRoundTime_spec M (M.runFrom c r) alive
    (counterLoopOrbit (roundTM k) loopRoundTime d r) anchor related
  exact ⟨anchor, positive, bound, cut⟩

/-! ## The contracts -/

/-- **The step block's counter loop, from any represented live start** (harvested from the
private `h1Clock_effect` of `CodeSimulator` and generalized). Let `M` be a `k`-work-tape binary
machine with `n + 1` states, `c` a live configuration of it on the input `x` (not necessarily
the initial one), and `d` a configuration of the step block at its entry `exit k true` that
represents `c` for `M`'s table (`Rep`). Let the last tape hold a binary counter word `w` of
value `t` (little-endian, possibly padded with high zeros) on the tape contents `ct`, delimited
by blanks at `cp - 1` and `cp + |w|`, with its head at `cp`; write `B = 50·(|tableBitsK M.tr| +
1)`. Started at its first decrement, the loop `loopTM k` reaches, at some time `T`:
* the live exit `done` if `M`'s run from `c` is still live after `t` steps, and the live exit
  `escape` if it has halted by then;
* with its body part `e` representing `M`'s configuration after `t` steps (in the escape case,
  by halting absorption, the configuration in which it halted), the physical output that of `d`,
  the counter head back at `cp`, and the counter tape changed only on `[cp, cp + |w|)`;
* at neither exit at any earlier time;
* with `T ≤ t·B + 4t + 2|w| + 2`, and (**the early-escape bound**) `T ≤ t'·B + 4t' + 2|w|`
  whenever `M`'s run from `c` has halted by some `t' ≤ t`.
The bounds depend on the table only through `|tableBitsK M.tr|`, not on the input, the tape
contents or the start. [AB09, §1.4.1, proof of Theorem 1.9; §3.1, proof of Theorem 3.1]

The private `h1Clock_effect` is the case `c = M.initCfg x`, `w = bits t`,
`ct = FinTM.bufferTape (bits t)`, `cp = 0`, without the early-escape bound and the counter
frame. Not stated: the exact time (the round times of the private round index plus
`Turing.counterOverhead`; no round-time function is public before MIG-0b's round adapter), and
the head trajectories (`Turing.counterLoopTM_run_done` and `Turing.counterLoopTM_run_escape`
state them for the body heads).

**Proof sketch.** As the proof of the former private `h1Clock_effect`, from `c`. The rounds are
indexed by the first positive return of the block to an exit. By induction on the number of
completed source steps, the block's orbit represents the source's run from `c` and keeps the
output (the orbit invariant `loopOrbit_rep`, formerly `h1Clock_orbit`), each live round being
the block's contract `roundTM_effect`, of positive length at most `B`. If the source is live
after `t` steps, the returning loop theorem `Turing.counterLoopTM_run_done` and the uniform round
bound `Turing.counterLoop_time_le` give `done` within `t·B + 4t + 2|w| + 2`. Otherwise let
`u ≤ t` be the first halting time, positive because `c` is live; the escaping theorem
`Turing.counterLoopTM_run_escape` at round `u - 1` gives `escape` at exactly the first `u` round
times plus `Turing.counterOverhead w u`, at most `u·B + 4u + 2|w|` by
`Turing.counterOverhead_le_of_le` (as `u ≤ t`), and every `t'` at which the source has halted is
at least `u`. Halting absorption identifies the represented endpoint; `roundTM_iterate` is the
unclocked analogue of the returning case. -/
theorem loopTM_run {k n : ℕ} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (live : c.state ≠ none) (d : Cfg (k + 2) Bool (Σ key, Ph k key) x)
    (entry : d.state = some (exit k true)) (rel : Rep M.tr c d)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (t : ℕ) (ht : Nat.ofDigits 2 (w.map Bool.toNat) = t) :
    ∃ T e ct',
      T ≤ t * (50 * ((tableBitsK M.tr).length + 1)) + 4 * t + 2 * w.length + 2 ∧
      (∀ t' ≤ t, (M.runFrom c t').state = none →
        T ≤ t' * (50 * ((tableBitsK M.tr).length + 1)) + 4 * t' + 2 * w.length) ∧
      Rep M.tr (M.runFrom c t) e ∧ e.output = d.output ∧
      (∀ q, ¬(cp ≤ q ∧ q < cp + (w.length : ℤ)) → ct' q = ct q) ∧
      (loopTM k).runFrom (counterLoopCfg (some (.dec .run)) d ct cp) T =
        counterLoopCfg
          (some (if (M.runFrom c t).state.isSome then .done else .escape)) e ct' cp ∧
      ∀ u < T,
        ((loopTM k).runFrom (counterLoopCfg (some (.dec .run)) d ct cp) u).state ≠
          some .done ∧
        ((loopTM k).runFrom (counterLoopCfg (some (.dec .run)) d ct cp) u).state ≠
          some .escape := by
  by_cases halted : (M.runFrom c t).state = none
  · -- The source halts first at some `u ≤ t`: the loop escapes after round `u - 1`.
    obtain ⟨u, deadline, before, same⟩ := M.exists_first_halt c halted
    have positive : 0 < u := by
      by_contra h
      have zero : u = 0 := by omega
      have bad := congrArg Cfg.state same
      rw [zero, MultiTapeTM.runFrom_zero, halted] at bad
      exact live bad
    let r := u - 1
    have count : r + 1 = u := by dsimp [r]; omega
    have alive (j : ℕ) (hj : j ≤ r) : (M.runFrom c j).state ≠ none := before j (by omega)
    have round (j : ℕ) (hj : j ≤ r) :=
      loopOrbit_round M c d entry rel j (fun i hi => alive i (hi.trans hj))
    obtain ⟨lastState, lastRep, lastOutput⟩ := loopOrbit_rep M c live d entry rel u before
    rw [same, halted, Option.isSome_none] at lastState
    rw [same] at lastRep
    let T := (∑ j ∈ Finset.range u,
      loopRoundTime (counterLoopOrbit (roundTM k) loopRoundTime d j)) + counterOverhead w u
    have run := counterLoopTM_run_escape (roundTM k)
      (exit k true) (exit k false) (by simp [exit])
      loopRoundTime d w ct cp hw r (by rw [ht]; omega)
      (fun j hj => ⟨(round j hj).1, (round j hj).2.1, (round j hj).2.2.2⟩)
      (by simpa only [count] using lastState) T (by simp only [T, count])
    have sumBound : (∑ j ∈ Finset.range u,
        loopRoundTime (counterLoopOrbit (roundTM k) loopRoundTime d j)) ≤
        u * (50 * ((tableBitsK M.tr).length + 1)) := by
      calc
        _ ≤ ∑ _j ∈ Finset.range u, (50 * ((tableBitsK M.tr).length + 1)) :=
          Finset.sum_le_sum (fun j hj => (round j (by
            have := Finset.mem_range.mp hj; omega)).2.2.1)
        _ = _ := by simp
    have overhead := counterOverhead_le_of_le w u (by rw [ht]; omega)
    refine ⟨T, counterLoopOrbit (roundTM k) loopRoundTime d u,
      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then
        FinTM.bufferTape (counterWord w u) (q - cp) else ct q),
      ?_, ?_, lastRep, lastOutput, ?_, ?_, run.2.1⟩
    · have bounded := Nat.mul_le_mul_right (50 * ((tableBitsK M.tr).length + 1)) deadline
      dsimp [T]
      omega
    · -- The early-escape bound: a halt by `t'` comes no earlier than the first halt `u`.
      intro t' _ halt'
      have early : u ≤ t' := by
        by_contra h
        exact before t' (by omega) halt'
      have bounded := Nat.mul_le_mul_right (50 * ((tableBitsK M.tr).length + 1)) early
      dsimp [T]
      omega
    · intro q hq
      simp only [hq, ↓reduceIte]
    · simpa only [loopTM, count, halted, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte] using run.1
  · -- The source is live after `t` steps: the loop runs `t` rounds and underflows.
    have alive (j : ℕ) (hj : j ≤ t) : (M.runFrom c j).state ≠ none :=
      M.runFrom_state_ne_none_of_le c t halted j hj
    have round (j : ℕ) (hj : j < t) :=
      loopOrbit_round M c d entry rel j (fun i hi => alive i (by omega))
    let T := (∑ j ∈ Finset.range t,
      loopRoundTime (counterLoopOrbit (roundTM k) loopRoundTime d j)) +
        counterOverhead w (t + 1)
    have run := counterLoopTM_run_done (roundTM k) (exit k true)
      (some (exit k false)) loopRoundTime d w ct cp hw t ht (by
        intro j hj
        obtain ⟨anchor, positive, _, interior⟩ := round j hj
        obtain ⟨next, _, _⟩ := loopOrbit_rep M c live d entry rel (j + 1)
          (fun i hi => alive i (by omega))
        refine ⟨anchor, positive, ?_, ?_⟩
        · intro v hv hlt
          obtain ⟨s, hs, ha, he⟩ := interior v hv hlt
          exact ⟨s, hs, ha, fun eq => he (Option.some.inj eq).symm⟩
        · simpa only [Option.isSome_iff_ne_none.mpr (alive (j + 1) (by omega))] using next)
      T rfl
    obtain ⟨_, finalRep, finalOutput⟩ := loopOrbit_rep M c live d entry rel t
      (fun j hj => alive j (Nat.le_of_lt hj))
    refine ⟨T, counterLoopOrbit (roundTM k) loopRoundTime d t,
      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q),
      counterLoop_time_le (roundTM k) loopRoundTime d w t ht
        (50 * ((tableBitsK M.tr).length + 1)) (fun j hj => (round j hj).2.2.1),
      ?_, finalRep, finalOutput, ?_, ?_, run.2.1⟩
    · intro t' ht' halt'
      exact absurd halt' (alive t' ht')
    · intro q hq
      simp only [hq, ↓reduceIte]
    · simpa only [loopTM, Option.isSome_iff_ne_none.mpr halted, ↓reduceIte] using run.1

/-- **The step block's counter loop on a buffered input, from any represented live start**
(harvested from the private `h1HostedClock_effect` and generalized): `loopTM_run` with the loop
hosted by Z1 on the buffered simulated input `x`, over any native input `z` whose head is frozen
at `p`, from any boundary tag `b` valid at the start's input position, and after any prior
physical output `pre`. At the same time `T`, within the same two bounds, the host is at the live
exit `(done, b')` or `(escape, b')`, chosen as in `loopTM_run`, for some arrival tag `b'` valid
at the endpoint's input position, in the transported configuration (`Turing.vhostCfg`) of the
loop's endpoint: the body part `e` represents `M`'s configuration after `t` steps, the output is
`pre` followed by `d`'s, the native head is at `p`, and the counter tape is changed only on
`[cp, cp + |w|)`. At no earlier time is the host at either exit, with either tag.
[AB09, §1.4.1, proof of Theorem 1.9; §3.1, proof of Theorem 3.1]

The private `h1HostedClock_effect` is the case `c = M.initCfg x`, `b = true`, `pre = []`, the
counter `bits t` at `0`, without the early-escape bound and the counter frame. For the
interpreter core `R`, `x` is the copied input window and `c` the replay machine's initial
configuration with the stream on its choice tape.

**Proof sketch.** As the former private `h1HostedClock_effect`'s: apply `loopTM_run`, then the Z1
lockstep `Turing.vhostEmitTM_runFrom` to the whole run, which also gives the arrival tag. Apply
the lockstep again at each strict prefix and project the host control to the loop's, which
transfers the loop's two exit cuts to every tag. The arrival tag is existential, never assumed
to be the initial one. -/
theorem hostedLoopTM_run {k n : ℕ} {x z : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x)
    (live : c.state ≠ none) (d : Cfg (k + 2) Bool (Σ key, Ph k key) x)
    (entry : d.state = some (exit k true)) (rel : Rep M.tr c d)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (t : ℕ) (ht : Nat.ofDigits 2 (w.map Bool.toNat) = t)
    (b : Bool) (hb : FinTM.VirtualTag c.inputPos b) (p : Fin (z.length + 2))
    (pre : List Bool) :
    ∃ T e ct' b',
      T ≤ t * (50 * ((tableBitsK M.tr).length + 1)) + 4 * t + 2 * w.length + 2 ∧
      (∀ t' ≤ t, (M.runFrom c t').state = none →
        T ≤ t' * (50 * ((tableBitsK M.tr).length + 1)) + 4 * t' + 2 * w.length) ∧
      Rep M.tr (M.runFrom c t) e ∧ e.output = d.output ∧
      (∀ q, ¬(cp ≤ q ∧ q < cp + (w.length : ℤ)) → ct' q = ct q) ∧
      FinTM.VirtualTag e.inputPos b' ∧
      (hostedLoopTM k).runFrom
          (vhostCfg (counterLoopCfg (some (.dec .run)) d ct cp) b p pre) T =
        vhostCfg (counterLoopCfg
          (some (if (M.runFrom c t).state.isSome then .done else .escape)) e ct' cp) b' p pre ∧
      ∀ u < T, ∀ tag,
        ((hostedLoopTM k).runFrom
            (vhostCfg (counterLoopCfg (some (.dec .run)) d ct cp) b p pre) u).state ≠
          some (.done, tag) ∧
        ((hostedLoopTM k).runFrom
            (vhostCfg (counterLoopCfg (some (.dec .run)) d ct cp) b p pre) u).state ≠
          some (.escape, tag) := by
  obtain ⟨T, e, ct', bound, early, related, output, frame, run, cut⟩ :=
    loopTM_run M c live d entry rel w ct cp hw t ht
  let start := counterLoopCfg (some (.dec .run)) d ct cp
  have valid : FinTM.VirtualTag start.inputPos b := by
    change FinTM.VirtualTag d.inputPos b
    rw [rel.1]
    exact hb
  obtain ⟨b', tag, hosted⟩ := vhostEmitTM_runFrom (loopTM k) start b valid p pre T
  rw [run] at tag hosted
  refine ⟨T, e, ct', b', bound, early, related, output, frame, tag, hosted, ?_⟩
  intro u hu tag'
  obtain ⟨b'', _, hostedPrefix⟩ := vhostEmitTM_runFrom (loopTM k) start b valid p pre u
  change ((vhostEmitTM (loopTM k)).runFrom (vhostCfg start b p pre) u).state ≠ _ ∧ _
  rw [hostedPrefix]
  constructor
  all_goals
    intro bad
    have projected := congrArg (Option.map Prod.fst) bad
    simp only [vhostCfg, Option.map_map, Function.comp_def, Option.map_id_fun',
      Option.map_some] at projected
    first
    | exact (cut u hu).1 projected
    | exact (cut u hu).2 projected

/-- **Reading a hosted loop configuration** (the caller's view of the live exits; generalized
from the reading steps of `CodeSimulator`'s `h1HostedVerdict_effect`): in the transported
configuration of a loop configuration with control `q`, counter `ct` at `cp`, and body part `e`
representing a source configuration `c'` of a table `tr`, the host's control is `(q, b)` (live),
its native input head is at `p`, its output is `pre` followed by `e`'s, and the bank cell under
the summary tape's head (`vhostBank (summaryTape k).castSucc`) holds `outputSummary c'.output`:
`some true` exactly when `c'` has emitted exactly `[true]` (`outputSummary_true`). A caller that
redirects the exits of `hostedLoopTM_run` reads its verdict there in one step, as `CodeSimulator`'s
`h1HostedVerdictTM` does.

**Proof sketch.** Control, native head and output are those of `Turing.vhostCfg` over
`Turing.counterLoopCfg` (`Turing.counter_cfg_eq`). The summary tape is a body tape, which the
host keeps on its bank; the seam relation puts its head at cell `0`, which holds the summary. -/
theorem hostedLoop_read {k n : ℕ} {x z : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (c' : Cfg k Bool (Fin (n + 1)) x) (e : Cfg (k + 2) Bool (Σ key, Ph k key) x)
    (rel : Rep tr c' e) (q : CounterLoopState (Σ key, Ph k key)) (ct : ℤ → Option Bool)
    (cp : ℤ) (b : Bool) (p : Fin (z.length + 2)) (pre : List Bool) :
    (vhostCfg (counterLoopCfg (some q) e ct cp) b p pre).state = some (q, b) ∧
      (vhostCfg (counterLoopCfg (some q) e ct cp) b p pre).inputPos = p ∧
      (vhostCfg (counterLoopCfg (some q) e ct cp) b p pre).output = pre ++ e.output ∧
      (vhostCfg (counterLoopCfg (some q) e ct cp) b p pre).workTapeSymbols
        (vhostBank (summaryTape k).castSucc) = outputSummary c'.output := by
  have cell : e.workTapeSymbols (summaryTape k) = outputSummary c'.output := by
    simp only [Cfg.workTapeSymbols, rel.2.2.2.2.2, rel.2.2.2.1, summaryCells, ↓reduceIte]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [vhostCfg, counter_cfg_eq]
  · simpa [vhostCfg, vhostBank, Cfg.workTapeSymbols, counter_cfg_eq] using cell

end StepBlock

end Turing
