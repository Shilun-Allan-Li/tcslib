/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalBlock
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The universal Turing machine

[AB09, §1.4.1 and Theorem 1.9, relaxed form]: there is a single machine `U` that,
given a code and an input, simulates the machine the code denotes — `U(x, α) =
M_α(x)` — with the simulation overhead depending only on the code, not on the input.

The construction lives in `UniversalStartup.lean` (prefix parsing,
canonization, and table capture), `UniversalInterpreter.lean` (the four-tape
table interpreter and the block-simulation assembly), and `UniversalBlock.lean`
(the live table block and the checkpoint relation), split out mechanically at
the epoch-3→4 merge; this file holds only the public statements.

## Design and deviations from [AB09] (all shaped by the phase-3 audit)

* Statements are relative to an `Turing.EffectiveMachineCode`: the purely algebraic
  scheme admits noncomputable-meaning pathologies against which no universal machine
  exists (audit finding 1, Argument A).
* **Input layout is `pairEncode α x` — code first, input second** — deviating from
  [AB09]'s `⟨x, α⟩`: with the input first, the startup cost of reaching the code
  grows with `|x|` and the stated bounds are false (audit finding 2, Argument B).
  With the code first, startup (parsing and canonizing `α`) costs a constant
  depending only on `α`, absorbed into `C`, and the simulated input head walks the
  verbatim `x` region on demand.
* `universal` is the **all-string evaluator** [AB09's `U(x, α) = M_α(x)`, p. 20]:
  it covers every `α` through `c.decode` (padded and fallback representations
  included), and it carries **both directions** — the forward time bound, and the
  converse that any *completed* output of `U` (output on halting; intermediate
  emissions of a non-halting run are unconstrained) is a completed output of the
  simulated machine, so divergence is preserved (round-1 finding 3; round-2
  Argument C).
* The constant `C` depends on the **representation** `α`, a documented weakening of
  [AB09]'s machine-dependent constant that is *necessary* at this generality: an
  effective scheme can reserve arbitrarily long identical-prefix representations of
  two fixed machines, defeating any constant that factors through `c.decode α`
  (round-2 audit, finding 6 and Argument E). Recovering the book's dependence would
  require further representation assumptions.
* **The core bound is linear**, `C · (t + 1)`: coded machines are already in
  one-work-tape binary normal form, so `U` pays a constant per simulated step.
  [AB09]'s relaxed quadratic bound reappears in `universal_quadratic`, where an
  *arbitrary* binary machine is first normal-formed ([AB09, Claims 1.5-1.6]); that
  corollary is stated — and labeled — at the level of **total function computation**
  (audit finding 4), the machine-level partial statement being `universal` itself.
  The `O(T log T)` sharpening ([AB09, §1.7]) is the phase-5 stretch goal.
* `timed_universal` outputs `true :: output` on success and `[false]` on timeout, a
  concrete rendering of [AB09]'s "special failure symbol" (§1.4.1); its budget is
  quadratic (binary clock maintenance). The deadline convention: halting is checked
  after every simulated transition *including the `t`-th*, so a machine first
  halting exactly at the deadline is a success; at budget `0` no initialized machine
  has halted, and the timeout branch applies (audit finding 6).

## Main results

* `Turing.universal` — the all-string evaluator [AB09, Theorem 1.9 core].
* `Turing.universal_quadratic` — the relaxed quadratic form for total functions of
  arbitrary binary machines [AB09, Theorem 1.9 as proved in §1.4.1].
* `Turing.timed_universal` — the time-bounded universal machine [AB09, §1.4.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21; Figure 1.6.)
-/

namespace Turing

open FinTM

/-- **The universal machine as an all-string evaluator** [AB09, Theorem 1.9]: for any
effective scheme there is a single machine `U` such that for every string `α` there
is a constant `C` (depending on `α`, absorbing its decoding) with, for every input
`x`: whenever the machine `α` denotes halts on `x` within `t` steps with `output`,
`U` on `pairEncode α x` halts with the same output within `C · (t + 1)` steps —
and conversely every *completed* output of `U` on `pairEncode α x` (its output on
halting) is a completed output of the denoted machine on `x`, so divergence is
preserved.

**Proof sketch** (after [AB09, Figure 1.6], adapted to the code-first layout).
Startup: `U` runs the scheme's `canonizer` on the doubled-bit `α`-region (via the
composition combinators), leaving the fixed serialization of `M := c.decode α` — the
state count, initial state, and table — on a *table* work tape, and writes the
initial state on a *state* tape; cost `O(canonizerTime |α| + |α| + 1)`, a constant
for fixed `α`, absorbed into `C`. `U`'s input head then parks at the start of the
verbatim `x` region, and a *work* tape mirrors `M`'s work tape. **The simulated
input's left boundary must be emulated explicitly** (round-2 audit, finding 3): the
cell physically left of the `x` region is the pairing delimiter's `true`, not a
blank, so `U` keeps a marker on a spare work tape whose head tracks the virtual
input position — at virtual position zero it supplies a blank read and suppresses
further outward moves (mirroring `moveInputPos`'s clamp), and for empty `x` the
virtual head starts at the right boundary blank adjacent to that marked left
boundary. Each simulated step: read the mirrored work symbol and the input symbol
under the simulated head (the input head moves one cell per simulated move — `x` is
verbatim, no doubling — with the boundary marker moved in lockstep), scan the table
for the record matching (state, input read, work read) — at most the table length,
constant in `t` — and apply it: update the state tape, write/move on the mirrored
tape, emit `M`'s emission verbatim. Forward bound: `C · (t + 1)`. Converse:
`U` emits only what the simulation emits and halts only when the simulation halts,
so any completed output of `U` is an output of `M` on `x`. -/
theorem universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      (∀ output : List Bool,
        (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (c.decode α).toFinTM.ComputesInTime x output t) := by
  refine ⟨universalTM c, ?_⟩
  apply universal_from_blocks c (universalTM c) (universalStartupBound c)
    (universalBlockBound c) (universalRelation c)
  · exact universalRelation_start c
  · intro α x src dst h
    by_cases hs : src.state = none
    · have hu := (universalRelation_halt c α x src dst h).mp hs
      refine ⟨1, le_refl _, ?_, ?_⟩
      · simp only [universalBlockBound]
        omega
      · rw [MultiTapeTM.step_of_halt hs, MultiTapeTM.runFrom_of_halt _ hu]
        exact h
    · -- Remaining obligation: execute one complete serialized-table lookup and
      -- application block for a live source, with positive duration and the
      -- code-dependent bound. Startup, boundary motion, and the two-clause
      -- assembly are proved above; this concrete block proof remains open.
      -- Completion (epoch 3B2): lift the proved interpreter block through capture.
      obtain ⟨p, tapes, heads, hp, rfl⟩ := h
      obtain ⟨d, p', hd, hB, hp', he⟩ := universal_live_block (c.decode α) α src p hp hs
      refine ⟨d, hd, hB, p', tapes, heads, hp', ?_⟩
      change (universalCaptureTM (universalCanonTM c) universalInterpreter).tm.runFrom
        (rightCfg Sum.inr (universalSimulationCfg (c.decode α) α src p) tapes heads) d = _
      rw [universalCapture_interpreter_run, he]
  · exact universalRelation_halt c
  · exact universalRelation_output c

/-- **The relaxed quadratic form, for total functions** [AB09, Theorem 1.9 as proved
in §1.4.1 — labeled per audit finding 4: this is the total-function corollary; the
machine-level, partial-computation statement is `Turing.universal`]: every binary
machine computing a total function `f` within `T` has a code `α` such that the
*same* universal machine computes `f x` from `pairEncode α x` within
`C · (T |x| + 1)²`.

**Proof sketch.** Normal-form the machine with `Turing.FinTM.one_work_tape_binary`
(quadratic, [AB09, Claims 1.5-1.6]), relabel its states with `Turing.exists_codeTM`,
take `α := c.encode` of that coded machine (so `c.decode α` is that machine, by
`MachineCode.decode_encode`), and apply the forward direction of `Turing.universal`;
the constants compose as `C_U · (c₁ · (T n + 1)² + 1) ≤ C · (T n + 1)²`. -/
theorem universal_quadratic (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (M₀ : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ),
      M₀.ComputesFunInTime f T →
      ∃ (α : List Bool) (C : ℕ), ∀ x : List Bool,
        U.ComputesInTime (pairEncode α x) (f x) (C * (T x.length + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := universal c
  refine ⟨U, ?_⟩
  intro M₀ f T hM
  obtain ⟨M₁, c₁, hk, h₁⟩ := FinTM.one_work_tape_binary M₀ f T hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := c.encode N
  obtain ⟨C_U, hCU⟩ := hU α
  refine ⟨α, C_U * (c₁ + 1), fun x => ?_⟩
  have hcoded : (c.decode α).toFinTM.ComputesInTime x (f x)
      (c₁ * (T x.length + 1) ^ 2) := by
    rw [show c.decode α = N from c.toMachineCode.decode_encode N]
    exact (hN x (f x) _).2 (h₁ x)
  apply ((hCU x).1 (f x) _ hcoded).mono
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc C_U * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ C_U * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl C_U) (Nat.add_le_add_left hpow _)
    _ = C_U * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

/-! ### Epoch 4: private stopped-interpreter infrastructure

**Implementation note (epoch 4).** The private construction below implements the
frozen timed-machine sketch. A prefix parser saves the clock and canonizes only
the code. The interpreter borrows before each source transition and routes source
halting to a buffered-output phase. The final induction checks the successor's
halting state before requiring any further clock credit.

The stop controller follows the audited interpreter until an action is ready.
Its next transition then halts without applying that action. A live endpoint
therefore certifies that no earlier action was applied. This permits replay
through the clock/buffer wrapper using the existing table representation.
-/

/-- Stop immediately before applying a selected source record. -/
private def timedCutInterpreter : MultiTapeTM 4 Bool UniversalControl where
  q₀ := universalInterpreter.q₀
  tr := fun q inp ws => match q with
    | .applyRecord _ _ => ⟨0, fun _ => (none, 0), none, none⟩
    | _ => universalInterpreter.tr q inp ws

/-- The four administrative reads. -/
private lemma timedCut_Eval_reads {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) :
    (universalEvalCfg base q table tp state sp).workTapeSymbols =
      universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3) := by
  funext i
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- One administrative action changes only the two designated tape cursors and
optionally the state-tape cell. -/
private lemma timedCut_Admin_apply {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool)) :
    (universalAdmin q' dt (w, ds)).apply (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> cases w <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;>
      first | rfl | exact add_zero _

/-- Read-based administrative step rule. -/
private lemma timedCut_Eval_step {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool))
    (h : timedCutInterpreter.tr q base.inputSymbol
      (universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3)) = universalAdmin q' dt (w, ds)) :
    timedCutInterpreter.step (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  change (timedCutInterpreter.tr q _ _).apply _ = _
  rw [timedCut_Eval_reads]
  change (timedCutInterpreter.tr q base.inputSymbol _).apply _ = _
  conv_lhs => rw [h]
  cases w <;> exact timedCut_Admin_apply base q q' table tp state sp dt ds _

/-- Look up the first unconsumed cell of a contiguous table. -/
private lemma timedCut_table_read (l r : List Bool) (b : Bool) :
    bufferTape (l ++ b :: r) (l.length : ℤ) = some b := by
  rw [bufferTape_nat, List.getElem?_append_right (le_refl _)]
  simp

/-- Exact-cost table rewind. The initial unconditional left move has put the
cursor at `j-1`, where `j` is at most the table length.

**Proof sketch.** At `j=0`, the cursor is the left blank and one move right
starts the count parser. At positive `j`, a nonblank table cell is read and the
cursor decreases once. Induction accounts for every transition and leaves all
other tapes, physical input, and accumulated output unchanged. -/
private lemma timedCut_table_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ j, j ≤ table.length →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.rewindTable initial index) table (j - 1) state sp) (j + 1) =
      universalEvalCfg base (.countFirst initial index) table 0 state sp := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.rewindTable initial index) (.countFirst initial index)
      table (-1) state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour])
    simpa using he
  | succ j ih =>
    intro hj
    have hr : bufferTape table (j : ℤ) = some table[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := timedCut_Eval_step base (.rewindTable initial index) (.rewindTable initial index)
      table (j : ℤ) state sp .neg 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    have hh : (j + 1 : ℤ) - 1 = j := by omega
    simp only [Nat.cast_add, Nat.cast_one, hh]
    rw [he]
    simpa using ih (by omega)

/-- Skip an arbitrary doubled, delimited count field at exact cost. No binary
arithmetic on its value is needed by the interpreter.

**Proof sketch.** Each doubled pair returns the parser to its first-half state
in two transitions. The terminal aligned `false,true` pair selects the initial
state copier or skipper. Induct on the count-bit list while growing the consumed
prefix, so table lookup is justified at every cursor position. -/
private lemma timedCut_count_run {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (bits : List Bool) (l r : List Bool)
    (ht : table = l ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.countFirst initial index) table l.length state sp)
      (2 * bits.length + 2) =
    universalEvalCfg base (if initial then .initialCopy else .initialSkip index) table
      (l.length + 2 * bits.length + 2) state sp := by
  induction bits generalizing l with
  | nil =>
    have hr0 : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l (true :: r) false
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some true := by
      have h' : table = (l ++ [false]) ++ true :: r := by simp [ht, List.append_assoc]
      have h := timedCut_table_read (l ++ [false]) r true
      simpa [h', List.length_append] using h
    have he0 := timedCut_Eval_step base (.countFirst initial index)
      (.countSecond initial index false) table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr0])
    have he1 := timedCut_Eval_step base (.countSecond initial index false)
      (if initial then .initialCopy else .initialSkip index)
      table (l.length + 1) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr1])
    change timedCutInterpreter.runFrom _ (0 + 1 + 1) = _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero,
      List.length_nil, Nat.cast_zero, mul_zero]
    congr 1
  | cons b bits ih =>
    have hr0 : bufferTape table (l.length : ℤ) = some b := by
      rw [ht]
      simpa [List.flatMap_cons, List.append_assoc] using
        timedCut_table_read l (b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r)) b
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some b := by
      have h' : table = (l ++ [b]) ++ b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) := by
        simp [ht, List.append_assoc]
      have h := timedCut_table_read (l ++ [b]) ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) b
      simpa [h', List.length_append] using h
    have he0 := timedCut_Eval_step base (.countFirst initial index)
      (.countSecond initial index b) table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr0])
    have he1 := timedCut_Eval_step base (.countSecond initial index b)
      (.countFirst initial index) table (l.length + 1) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr1])
    have h' : table = (l ++ [b, b]) ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r := by
      simp [ht, List.append_assoc]
    have hi := ih (l ++ [b, b]) h'
    conv_lhs => rw [show 2 * (b :: bits).length + 2 =
      1 + 1 + (2 * bits.length + 2) by simp; omega]
    rw [MultiTapeTM.runFrom_add]
    change timedCutInterpreter.runFrom
      (timedCutInterpreter.step (timedCutInterpreter.step _)) _ = _
    rw [he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega


/-- Appending a next-state unary symbol extends the intact state tape. -/
private lemma timedCut_StateTape_append (n : ℕ) :
    Function.update (universalStateTape n) (n + 1 : ℤ) (some true) =
      universalStateTape (n + 1) := by
  have h := bufferTape_append (false :: List.replicate n true) true
  simpa only [universalStateTape, List.replicate_add, List.replicate_one,
    List.cons_append, List.length_cons, List.length_replicate,
    Nat.cast_add, Nat.cast_one] using h.symm

/-- An intact unary state reads its blank immediately after the last symbol. -/
private lemma timedCut_StateTape_end (n : ℕ) :
    universalStateTape n (n + 1) = none := by
  simp [universalStateTape, bufferTape]

/-- A marker-directed state rewind has exact cost equal to cursor plus one.
Its premise is deliberately independent of whether traversed cells are erased
blanks or retained unary ones.

**Proof sketch.** Each positive cursor sees a non-marker cell and moves left.
At zero the permanent marker causes one right move and transfer to the supplied
continuation. The entire tape, input head, and real output stay unchanged. -/
private lemma timedCut_state_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl)
    (table : List Bool) (tp : ℤ) (state : ℤ → Option Bool)
    (hzero : state 0 = some false)
    (hother : ∀ j : ℕ, 0 < j → state j ≠ some false)
    (hstop : ∀ inp work, work 1 = some false →
      timedCutInterpreter.tr q inp work = universalAdmin q' 0 (none, .pos))
    (hscan : ∀ inp work, work 1 ≠ some false →
      timedCutInterpreter.tr q inp work = universalAdmin q 0 (none, .neg)) :
    ∀ j : ℕ, timedCutInterpreter.runFrom
      (universalEvalCfg base q table tp state j) (j + 1) =
      universalEvalCfg base q' table tp state 1 := by
  intro j
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base q q' table tp state 0 0 .pos none
      (hstop _ _ (by simpa [universalFour] using hzero))
    simpa using he
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := timedCut_Eval_step base q q table tp state (j + 1) 0 .neg none
      (hscan _ _ (by simpa [universalFour] using hother (j + 1) (by omega)))
    rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by omega, he]
    simpa using ih

/-- The table's initial-state unary field can be skipped at exact cost.

**Proof sketch.** Induct on the number of unary ones. Each one advances the table
cursor; the final zero advances once more and enters record-group selection. -/
private lemma timedCut_initial_skip {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.initialSkip index) table l.length state sp) (n + 1) =
      universalEvalCfg base (.group index) table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.initialSkip index) (.group index)
      table l.length state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base (.initialSkip index) (.initialSkip index)
      table l.length state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega



/-- Copy a unary table field onto the state tape. This single gadget serves both
initial-state extraction and live successor-state replacement.

**Proof sketch.** A `true` table cell appends one unary state symbol and moves both
cursors right. A terminal `false` switches to the supplied continuation, with its
specified table movement. Induction preserves exact table/state positions and
accounts for all `n+1` transitions. -/
private lemma timedCut_unary_copy {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl) (doneMove : SignType)
    (table : List Bool)
    (htrue : ∀ inp work, work 0 = some true →
      timedCutInterpreter.tr q inp work = universalAdmin q .pos (some (some true), .pos))
    (hfalse : ∀ inp work, work 0 = some false →
      timedCutInterpreter.tr q inp work = universalAdmin q' doneMove (none, 0))
    (n j : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base q table l.length (universalStateTape j) (j + 1)) (n + 1) =
      universalEvalCfg base q' table (l.length + n + (doneMove : ℤ))
        (universalStateTape (j + n)) (j + n + 1) := by
  induction n generalizing l j with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base q q' table l.length (universalStateTape j) (j + 1)
      doneMove 0 none (hfalse _ _ (by simp [universalFour, hr]))
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base q q table l.length (universalStateTape j) (j + 1)
      .pos .pos (some (some true)) (htrue _ _ (by simp [universalFour, hr]))
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, timedCut_StateTape_append]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (j + 1) (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 n, Int.add_assoc] <;> congr 1 <;> omega

/-- Installing a single permanent marker in an otherwise blank tape. -/
private lemma timedCut_install_marker (b : Bool) :
    Function.update (fun _ : ℤ => none) 0 (some b) = bufferTape [b] := by
  simpa using (bufferTape_append [] b).symm

/-- Interpreter entry with the captured table on its right blank and three
fresh auxiliary tapes. Physical input is already parked at the suffix start. -/
private def timedCut_InterpreterInitial {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) : Cfg 4 Bool UniversalControl x :=
  ⟨some .start, p, universalFour (bufferTape table) (fun _ => none) (fun _ => none)
      (fun _ => none), universalFour table.length 0 0 0, []⟩

/-- Inactive data during interpreter initialization: physical input is stationary,
simulated work is blank, and the virtual-left marker is installed at zero with
its head at one (also for empty suffixes). -/
private def timedCut_InterpreterBase {x : List Bool} (p : Fin (x.length + 2)) :
    Cfg 4 Bool UniversalControl x :=
  ⟨some .main, p, universalFour (fun _ => none) (fun _ => none) (fun _ => none)
      (bufferTape [true]), universalFour 0 0 0 1, []⟩

/-- The first interpreter step installs the permanent markers and starts the
unconditional table rewind. -/
private lemma timedCut_Interpreter_first {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) :
    timedCutInterpreter.step (timedCut_InterpreterInitial p table) =
      universalEvalCfg (timedCut_InterpreterBase p) (.rewindTable true 0) table
        (table.length - 1) (universalStateTape 0) 1 := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · rfl
    · exact timedCut_install_marker false
    · rfl
    · exact timedCut_install_marker true
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- Exact interpreter initialization for a canonical count/initial-state prefix.
No transition-table lookup is involved yet.

**Proof sketch.** Install both markers (one transition), rewind the whole captured
table (`|table|+1`), skip the doubled count (`2|bits|+2`), copy the initial unary
state (`n+1`), and rewind its cursor (`n+2`). The sum is
`|table| + 2|bits| + 2n + 7`. Every intermediate configuration keeps the physical
input fixed and real output empty. -/
private lemma timedCut_Interpreter_initialize {x : List Bool}
    (p : Fin (x.length + 2)) (table bits records : List Bool) (n : ℕ)
    (ht : table = pairEncode bits (List.replicate n true ++ false :: records)) :
    timedCutInterpreter.runFrom (timedCut_InterpreterInitial p table)
      (table.length + 2 * bits.length + 2 * n + 7) =
    universalEvalCfg (timedCut_InterpreterBase p) .main table
      (2 * bits.length + 2 + n + 1) (universalStateTape n) 1 := by
  let base := timedCut_InterpreterBase p
  have hrew := timedCut_table_rewind base true 0 table (universalStateTape 0) 1
    table.length (le_refl _)
  have hcount := timedCut_count_run base true 0 table (universalStateTape 0) 1
    bits [] (List.replicate n true ++ false :: records) (by simpa [pairEncode] using ht)
  let countPrefix := (bits.flatMap fun b => [b, b]) ++ [false, true]
  have hlen : countPrefix.length = 2 * bits.length + 2 := by
    simpa [countPrefix, pairEncode] using universal_pair_length bits []
  have hcopy := timedCut_unary_copy base .initialCopy (.rewindState none) .pos table
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) n 0 countPrefix records
    (by simpa [countPrefix, pairEncode, List.append_assoc] using ht)
  have hstate := timedCut_state_rewind base (.rewindState none) .main table
    (2 * bits.length + 2 + n + 1) (universalStateTape n)
    (universalStateTape_marker n).1 (universalStateTape_marker n).2
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (n + 1)
  have htime : table.length + 2 * bits.length + 2 * n + 7 =
      1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1) + (n + 2) := by omega
  rw [htime,
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1)) (n + 2),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2)) (n + 1),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1)) (2 * bits.length + 2),
    MultiTapeTM.runFrom_add _ 1 (table.length + 1)]
  change timedCutInterpreter.runFrom
    (timedCutInterpreter.runFrom
      (timedCutInterpreter.runFrom
        (timedCutInterpreter.runFrom
          (timedCutInterpreter.step (timedCut_InterpreterInitial p table))
          (table.length + 1)) (2 * bits.length + 2)) (n + 1)) (n + 2) = _
  rw [timedCut_Interpreter_first, hrew]
  have hc : timedCutInterpreter.runFrom
      (universalEvalCfg base (.countFirst true 0) table 0 (universalStateTape 0) 1)
      (2 * bits.length + 2) =
    universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1 := by
    simpa using hcount
  rw [hc]
  have hp : timedCutInterpreter.runFrom
      (universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1)
      (n + 1) =
    universalEvalCfg base (.rewindState none) table (2 * bits.length + 2 + n + 1)
      (universalStateTape n) (n + 1) := by
    simpa [hlen] using hcopy
  rw [hp]
  simpa using hstate



/-- Skip the remaining fixed action fields, one transition per bit.

**Proof sketch.** Descending induction on the number of fields still to skip.
The last field enters the unary scanner; every other field increments the
bounded field register. No tape content is inspected or modified. -/
private lemma timedCut_skip_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ (n : ℕ) (field : Fin 8) (tp : ℤ), field.val + n = 7 →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.skipFixed dest rem field) table tp state sp) (n + 1) =
      universalEvalCfg base (.skipUnary dest rem) table (tp + n + 1) state sp := by
  intro n
  induction n with
  | zero =>
    intro field tp hf
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.skipFixed dest rem field) (.skipUnary dest rem)
      table tp state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, show field.val = 7 by omega])
    simpa using he
  | succ n ih =>
    intro field tp hf
    have hne : field.val ≠ 7 := by omega
    have he := timedCut_Eval_step base (.skipFixed dest rem field)
      (.skipFixed dest rem ⟨field.val + 1, by omega⟩) table tp state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, hne])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ (tp + 1) (by simp; omega) using 1 <;>
      push_cast <;> congr 1 <;> omega


/-- The unary tail of a skipped record costs exactly its serialized length.

**Proof sketch.** A true cell advances once without changing control. The false
terminator either finishes the request or decrements the bounded record counter.
Induction grows the consumed list prefix by one cell. -/
private lemma timedCut_skip_unary {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipUnary dest rem) table l.length state sp) (n + 1) =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.skipUnary dest rem)
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table l.length state sp .pos 0 none
      (by
        by_cases h : rem.val = 0
        · have hz : rem = 0 := Fin.ext h
          simp [timedCutInterpreter, universalInterpreter, universalFour, hr, hz, universalSkipDone]
        · have hz : rem ≠ 0 := fun he => h (congrArg Fin.val he)
          simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz, universalSkipDone])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base (.skipUnary dest rem) (.skipUnary dest rem)
      table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    convert ih (l ++ [true]) ht' using 1 <;>
      simp [List.length_append, List.length_cons] <;> congr 1 <;> omega

/-- Skip one complete serialized record at exact cost.

**Proof sketch.** Concatenate the eight fixed-field transitions and the unary
tail scan. The record grammar identifies their total with the record length. -/
private lemma timedCut_skip_record {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (a : Action 1 Bool (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ universalRecordBits a ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (universalRecordBits a).length =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + (universalRecordBits a).length) state sp := by
  have hlen : (universalRecordBits a).length = 8 + (universalNextOnes a.state + 1) := by
    rw [universal_record_shape]
    simp only [List.length_append, List.length_ofFn, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hfixed := timedCut_skip_fixed base dest rem table state sp 7 0 l.length rfl
  have hunary := timedCut_skip_unary base dest rem table state sp
    (universalNextOnes a.state) (l ++ List.ofFn (universalActionBits a)) r
    (by simpa [universal_record_shape, List.append_assoc] using ht)
  rw [hlen, MultiTapeTM.runFrom_add]
  have hf : timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp) 8 =
      universalEvalCfg base (.skipUnary dest rem) table (l.length + 8) state sp := by
    simpa only [Nat.cast_ofNat, Int.add_assoc, show (7 : ℤ) + 1 = 8 from rfl] using hfixed
  rw [hf]
  simpa only [List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat,
    Int.add_assoc] using hunary

/-- A bounded request skips precisely the specified nonempty list of records.

**Proof sketch.** Execute the first record and decrement the record counter.
The last record enters the requested continuation. Run addition adds the
serialized lengths, without an extra transition between consecutive records. -/
private lemma timedCut_skip_records {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9))
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (as : List (Action 1 Bool (Fin (n + 1)))) (l r : List Bool)
    (rem : Fin 9) (hlen : as.length = rem.val + 1)
    (ht : table = l ++ as.flatMap universalRecordBits ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (as.flatMap universalRecordBits).length =
    universalEvalCfg base (universalSkipDone dest) table
      (l.length + (as.flatMap universalRecordBits).length) state sp := by
  induction as generalizing l rem with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a as ih =>
    have hv : rem.val = as.length := by simp only [List.length_cons] at hlen; omega
    have he := timedCut_skip_record base dest rem table state sp a l
      (as.flatMap universalRecordBits ++ r)
      (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
    rw [List.flatMap_cons, List.length_append, MultiTapeTM.runFrom_add, he]
    cases as with
    | nil => simp [hv]
    | cons b bs =>
      have hn : rem.val ≠ 0 := by simp only [List.length_cons] at hv; omega
      rw [dif_neg hn]
      have htail : (b :: bs).length = rem.val - 1 + 1 := by
        simp only [List.length_cons] at hv ⊢
        omega
      have hi := ih (l ++ universalRecordBits a) ⟨rem.val - 1, by omega⟩ htail
        (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
      convert hi using 1 <;>
        simp only [List.length_append, Nat.cast_add] <;> congr 1 <;> omega

/-- Each erased unary state symbol skips exactly nine transition records.

**Proof sketch.** Erase the first remaining state symbol, run the nine-record
scanner, and repeat for the remaining groups. At the final blank one transition
enters the state rewind. The state-window invariant records all erasures. -/
private lemma timedCut_skip_groups {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9) (l r : List Bool) (j : ℕ)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateWindow j groups.length) (j + 1))
      (groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) =
    universalEvalCfg base (.rewindState (some index)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length)
      (universalStateWindow (j + groups.length) 0) (j + groups.length + 1) := by
  induction groups generalizing l j with
  | nil =>
    simp only [List.length_nil, List.flatMap_nil, Nat.add_zero, Nat.zero_add,
      Nat.cast_zero, add_zero, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.group index) (.rewindState (some index))
      table l.length (universalStateWindow j 0) (j + 1) 0 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, universalStateWindow_end])
    simpa using he
  | cons g gs ih =>
    have hgl : g.length = 9 := hg g (by simp)
    have he := timedCut_Eval_step base (.group index) (.skipFixed (some index) 8 0)
      table l.length (universalStateWindow j (gs.length + 1)) (j + 1) 0 .pos (some none)
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, universalStateWindow_read])
    have hskip := timedCut_skip_records base (some index) table
      (universalStateWindow (j + 1) gs.length) (j + 2) g l
      (gs.flatMap (fun g => g.flatMap universalRecordBits) ++ r) 8 hgl
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have hrest := ih (fun a ha => hg a (by simp [ha]))
      (l ++ g.flatMap universalRecordBits) (j + 1)
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have htime : (g :: gs).length +
        ((g :: gs).flatMap (fun g => g.flatMap universalRecordBits)).length + 1 =
        1 + (g.flatMap universalRecordBits).length +
          (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) := by
      simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega
    rw [htime, MultiTapeTM.runFrom_add _ (1 + (g.flatMap universalRecordBits).length)
      (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1),
      MultiTapeTM.runFrom_add _ 1 (g.flatMap universalRecordBits).length]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.coe_zero, add_zero, SignType.pos_eq_one, SignType.coe_one,
      universalStateWindow_erase]
    rw [show (j : ℤ) + 1 + 1 = j + 2 by omega, hskip]
    simpa only [universalSkipDone, List.flatMap_cons, List.length_append, List.length_cons,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Int.add_assoc, Int.add_left_comm, Int.add_comm, Int.reduceAdd] using hrest

/-- Reading fixed action fields fills the finite eight-bit register exactly.

**Proof sketch.** The register already agrees with the record before the current
field. Read and update that field, maintaining agreement on a longer prefix.
After field seven the agreement covers every register entry. -/
private lemma timedCut_read_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool)
    (state : ℤ → Option Bool) (sp : ℤ) (bits : Fin 8 → Bool) (l r : List Bool)
    (ht : table = l ++ List.ofFn bits ++ r) :
    ∀ (n : ℕ) (field : Fin 8) (old : Fin 8 → Bool), field.val + n = 7 →
      (∀ i : Fin 8, i.val < field.val → old i = bits i) →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.readAction field old) table
          (l.length + field.val) state sp) (n + 1) =
      universalEvalCfg base (.nextState bits) table (l.length + 8) state sp := by
  intro n
  induction n with
  | zero =>
    intro field old hf hknown
    have hv : field.val = 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : Function.update old field (bits field) = bits := by
      funext i
      by_cases hi : i = field
      · subst i; simp
      · rw [Function.update_of_ne hi]
        apply hknown
        have hn : i.val ≠ field.val := fun h => hi (Fin.ext h)
        omega
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.readAction field old) (.nextState bits)
      table (l.length + field.val) state sp .pos 0 none
      (by
        simp only [timedCutInterpreter, universalInterpreter, universalFour, ↓reduceIte, hr]
        simp only [hv, ↓reduceDIte, hb])
    rw [he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    congr 1
    omega
  | succ n ih =>
    intro field old hf hknown
    have hv : field.val ≠ 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : ∀ i : Fin 8, i.val < field.val + 1 →
        Function.update old field (bits field) i = bits i := by
      intro i hi
      by_cases he : i = field
      · subst i; simp
      · rw [Function.update_of_ne he]
        apply hknown
        have hn : i.val ≠ field.val := fun h => he (Fin.ext h)
        omega
    have he := timedCut_Eval_step base (.readAction field old)
      (.readAction ⟨field.val + 1, by omega⟩ (Function.update old field (bits field)))
      table (l.length + field.val) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr, hv])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ _ (by simp; omega) hb using 1 <;>
      simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one] <;> congr 1 <;> omega

/-- Successor decoding, copying, and rewinding cost, before applying the action. -/
private def timedCut_NextCost {n : ℕ} : Option (Fin (n + 1)) → ℕ
  | none => 1
  | some q => 2 * q.val + 4

/-- Decode the successor field and install its unary state at cursor one.

**Proof sketch.** A halting flag takes one transition. A live flag takes one,
copying its index takes `q+1`, and rewinding the new state takes `q+2`.
The table cursor stops on the field's false terminator in both cases. -/
private lemma timedCut_prepare_next {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool) (bits : Fin 8 → Bool)
    (next : Option (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ List.replicate (universalNextOnes next) true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.nextState bits) table l.length (universalStateTape 0) 1)
      (timedCut_NextCost next) =
    universalEvalCfg base (.applyRecord bits next.isNone) table
      (l.length + universalNextOnes next) (universalStateTape ((next.map Fin.val).getD 0)) 1 := by
  cases next with
  | none =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa [universalNextOnes] using timedCut_table_read l r false
    have he := timedCut_Eval_step base (.nextState bits) (.applyRecord bits true)
      table l.length (universalStateTape 0) 1 0 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    simpa [timedCut_NextCost, universalNextOnes, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero] using he
  | some q =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate q.val true ++ false :: r) true
    have he := timedCut_Eval_step base (.nextState bits) (.copyState bits)
      table l.length (universalStateTape 0) 1 .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    have hcopy := timedCut_unary_copy base (.copyState bits) (.rewindNext bits) 0 table
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) q.val 0 (l ++ [true]) r
      (by simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using ht)
    have hrew := timedCut_state_rewind base (.rewindNext bits) (.applyRecord bits false)
      table (l.length + q.val + 1) (universalStateTape q.val)
      (universalStateTape_marker q.val).1 (universalStateTape_marker q.val).2
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (q.val + 1)
    have hc : timedCutInterpreter.runFrom
        (universalEvalCfg base (.copyState bits) table (l.length + 1) (universalStateTape 0) 1)
        (q.val + 1) =
      universalEvalCfg base (.rewindNext bits) table (l.length + q.val + 1)
        (universalStateTape q.val) (q.val + 1) := by
      simpa [List.length_append, Int.add_assoc, Int.add_comm 1] using hcopy
    change timedCutInterpreter.runFrom _ (2 * q.val + 4) = _
    rw [show 2 * q.val + 4 = 1 + (q.val + 1) + (q.val + 2) by omega,
      MultiTapeTM.runFrom_add _ (1 + (q.val + 1)) (q.val + 2),
      MultiTapeTM.runFrom_add _ 1 (q.val + 1)]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [hc]
    simpa only [universalNextOnes, Option.isNone_some, Option.map_some, Option.getD_some,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Int.add_assoc] using hrew

/-- The nine actions for a state, in input-major, work-minor order. -/
private def timedCut_Actions (M : CodeTM) (q : Fin (M.numStates + 1)) :
    List (Action 1 Bool (Fin (M.numStates + 1))) :=
  ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
    ([none, some false, some true] : List (Option Bool)).map fun work =>
      M.tm.tr q inp (fun _ => work)

/-- Each state contributes nine records and the read offset selects its action. -/
private lemma timedCut_Actions_lookup (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    (timedCut_Actions M q).length = 9 ∧
    (timedCut_Actions M q)[(universalRecordIndex inp work).val]'(by
      change (universalRecordIndex inp work).val < 9
      exact (universalRecordIndex inp work).isLt) = M.tm.tr q inp (fun _ => work) := by
  constructor
  · rfl
  · rcases inp with _ | (_ | _) <;> rcases work with _ | (_ | _) <;> rfl

/-- Count prefix and initial-state field, excluding transition records. -/
private def timedCut_Header (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates) [] ++ List.replicate M.tm.q₀.val true ++ [false]

/-- Serialization as a header followed by the ordered lists of nine actions.

**Proof sketch.** Expand the serializer into its count, initial state, and table.
Identify each encoded action by its finite directions, optional symbols, and
successor, then regroup the nested enumerations into nine actions per state. -/
private lemma timedCut_serialization_actions (M : CodeTM) :
    M.serialize = timedCut_Header M ++
      ((List.finRange (M.numStates + 1)).map (timedCut_Actions M)).flatMap
        (fun g => g.flatMap universalRecordBits) := by
  have hr : M.serialize = pairEncode (Nat.bits M.numStates)
      (List.replicate M.tm.q₀.val true ++ false :: universalRecords M) := by
    unfold CodeTM.serialize
    change pairEncode _ ((List.replicate M.tm.q₀.val true ++ [false]) ++ _) = _
    rw [List.append_assoc]
    apply congrArg (pairEncode (Nat.bits M.numStates))
    apply congrArg (fun r : List Bool => List.replicate M.tm.q₀.val true ++ false :: r)
    unfold universalRecords
    dsimp only [List.append]
    congr 1
    funext q
    congr 1
    funext inp
    congr 1
    funext work
    generalize M.tm.tr q inp (fun _ => work) = a
    rcases a with ⟨di, tapes, out, next⟩
    have htapes : tapes = fun _ => tapes 0 := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
    rw [htapes]
    generalize tapes 0 = entry
    rcases entry with ⟨write, dm⟩
    cases di <;> cases dm <;> rcases write with _ | (_ | (_ | _)) <;>
      rcases out with _ | (_ | _) <;> cases next <;> rfl
  rw [hr]
  simp [pairEncode, timedCut_Header, universalRecords, timedCut_Actions,
    List.flatMap_map, List.append_assoc]

/-- Decompose the canonical table at the action selected by state and reads.

**Proof sketch.** Split the increasing state enumeration at the source state,
and split its nine-entry list at the read offset. The two prefixes are exactly
the groups and records traversed by the controller. -/
private lemma timedCut_lookup_parts (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    ∃ (groups : List (List (Action 1 Bool (Fin (M.numStates + 1)))))
      (before : List (Action 1 Bool (Fin (M.numStates + 1)))) (after : List Bool),
      groups.length = q.val ∧ (∀ g ∈ groups, g.length = 9) ∧
      before.length = (universalRecordIndex inp work).val ∧
      M.serialize = timedCut_Header M ++
        groups.flatMap (fun g => g.flatMap universalRecordBits) ++
        before.flatMap universalRecordBits ++
        universalRecordBits (M.tm.tr q inp (fun _ => work)) ++ after := by
  let states := List.finRange (M.numStates + 1)
  let index := universalRecordIndex inp work
  let actions := timedCut_Actions M q
  have hq : q.val < states.length := by simpa [states] using q.isLt
  have hi : index.val < actions.length := by
    rw [(timedCut_Actions_lookup M q inp work).1]
    exact index.isLt
  have hs : states = states.take q.val ++ q :: states.drop (q.val + 1) := by
    have h := List.take_append_drop q.val states
    rw [List.drop_eq_getElem_cons hq] at h
    simpa [states] using h.symm
  have ha : actions = actions.take index.val ++
      M.tm.tr q inp (fun _ => work) :: actions.drop (index.val + 1) := by
    have h := List.take_append_drop index.val actions
    rw [List.drop_eq_getElem_cons hi, (timedCut_Actions_lookup M q inp work).2] at h
    exact h.symm
  refine ⟨(states.take q.val).map (timedCut_Actions M), actions.take index.val,
    (actions.drop (index.val + 1)).flatMap universalRecordBits ++
      ((states.drop (q.val + 1)).map (timedCut_Actions M)).flatMap
        (fun g => g.flatMap universalRecordBits), ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hq)]
  · intro g hg
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hg
    exact (timedCut_Actions_lookup M s none none).1
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    rfl
  · rw [timedCut_serialization_actions]
    change timedCut_Header M ++ (states.map (timedCut_Actions M)).flatMap _ = _
    conv_lhs => rw [hs, List.map_append, List.map_cons, List.flatMap_append,
      List.flatMap_cons]
    change timedCut_Header M ++ (_ ++ (actions.flatMap universalRecordBits ++ _)) = _
    conv_lhs => rw [ha]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Decoding the four fixed pairs recovers the source action fields. -/
private lemma timedCut_ActionBits_decode {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    universalSign (universalActionBits a 0) (universalActionBits a 1) = a.inputTape ∧
    universalWrite (universalActionBits a 2) (universalActionBits a 3) = (a.workTapes 0).1 ∧
    universalSign (universalActionBits a 4) (universalActionBits a 5) = (a.workTapes 0).2 ∧
    (if universalActionBits a 6 then some (universalActionBits a 7) else none) = a.output := by
  simp only [universalActionBits]
  constructor
  · cases a.inputTape <;> rfl
  constructor
  · rcases (a.workTapes 0).1 with _ | (_ | (_ | _)) <;> rfl
  constructor
  · cases (a.workTapes 0).2 <;> rfl
  · rcases a.output with _ | (_ | _) <;> rfl


/-- Select a record by destructive state counting and the bounded read offset.

**Proof sketch.** Skip the preceding state groups while erasing the unary state.
Rewind the erased state tape to one, then skip the read-offset prefix. An offset
of zero enters the action reader directly. The table scans cost their total
serialized length, and state administration costs twice the old index plus three. -/
private lemma timedCut_select {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9)
    (before : List (Action 1 Bool (Fin (n + 1)))) (hb : before.length = index.val)
    (l r : List Bool)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++
      before.flatMap universalRecordBits ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateTape groups.length) 1)
      (2 * groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length + 3) =
    universalEvalCfg base (.readAction 0 (fun _ => false)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length) (universalStateTape 0) 1 := by
  let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
  let pb := before.flatMap universalRecordBits
  let next := if h : index.val = 0 then UniversalControl.readAction 0 (fun _ => false)
    else .skipFixed none ⟨index.val - 1, by omega⟩ 0
  have hgroup := timedCut_skip_groups base index table groups hg l (pb ++ r) 0
    (by simpa [pg, pb, List.append_assoc] using ht)
  have hgr : timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length (universalStateTape groups.length) 1)
      (groups.length + pg.length + 1) =
    universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
      (universalStateTape 0) (groups.length + 1) := by
    simpa only [Nat.cast_zero, zero_add, universalStateWindow_empty,
      universalStateWindow_zero] using hgroup
  have hrew := timedCut_state_rewind base (.rewindState (some index)) next table
    (l.length + pg.length) (universalStateTape 0)
    (universalStateTape_marker 0).1 (universalStateTape_marker 0).2
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h, next])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (groups.length + 1)
  have hrw : timedCutInterpreter.runFrom
      (universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
        (universalStateTape 0) (groups.length + 1)) (groups.length + 2) =
    universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrew
  have hskip : timedCutInterpreter.runFrom
      (universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1)
      pb.length = universalEvalCfg base (.readAction 0 (fun _ => false)) table
        (l.length + pg.length + pb.length) (universalStateTape 0) 1 := by
    by_cases hi : index.val = 0
    · have hz : before = [] := List.length_eq_zero_iff.mp (hb.trans hi)
      simp [next, hi, pb, hz]
    · have hh := timedCut_skip_records base none table (universalStateTape 0) 1
        before (l ++ pg) r ⟨index.val - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
        (by simpa [pg, pb, List.append_assoc] using ht)
      simpa only [next, dif_neg hi, universalSkipDone, List.length_append, Nat.cast_add]
        using hh
  change timedCutInterpreter.runFrom _ (2 * groups.length + pg.length + pb.length + 3) = _
  rw [show 2 * groups.length + pg.length + pb.length + 3 =
      (groups.length + pg.length + 1) + (groups.length + 2) + pb.length by omega,
    MultiTapeTM.runFrom_add _ ((groups.length + pg.length + 1) + (groups.length + 2)) pb.length,
    MultiTapeTM.runFrom_add _ (groups.length + pg.length + 1) (groups.length + 2),
    hgr, hrw, hskip]

/-- Concatenate two configuration equalities without unfolding either run. -/
private lemma timedCut_run_join {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) {a b c : Cfg k Bool Q x} {s t : ℕ}
    (hs : tm.runFrom a s = b) (ht : tm.runFrom b t = c) :
    tm.runFrom a (s + t) = c := by
  rw [MultiTapeTM.runFrom_add, hs, ht]


/-- Applying the decoded record commutes with the complete source checkpoint.

**Proof sketch.** Decode the four fixed pairs. The virtual-input movement lemma
supplies both the physical head equality and the marker-head equality. Optional
writes and emissions then agree field by field; the newly installed unary state
is precisely the successor representation, including the halting case. -/
private lemma timed_apply_record (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (oldp p : ℕ)
    (a : Action 1 Bool (Fin (M.numStates + 1))) :
    universalInterpreter.step
      (universalEvalCfg (universalSimulationCfg M α src oldp)
        (.applyRecord (universalActionBits a) a.state.isNone) M.serialize p
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1) =
    universalSimulationCfg M α (a.apply src) p := by
  let base := universalSimulationCfg M α src oldp
  let cfg := universalEvalCfg base (.applyRecord (universalActionBits a) a.state.isNone)
    M.serialize p (universalStateTape ((a.state.map Fin.val).getD 0)) 1
  let d := virtualMove (decide (bufferTape [true] (src.inputPos.val : ℤ) ≠ some true))
    src.inputSymbol a.inputTape
  have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
      src.inputSymbol := universalInput_read α src
  have hb := timedCut_ActionBits_decode a
  have htr : universalInterpreter.tr
      (.applyRecord (universalActionBits a) a.state.isNone) cfg.inputSymbol cfg.workTapeSymbols =
      (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
        a.state.map (fun _ => .main)⟩ : Action 4 Bool UniversalControl) := by
    have hr3 : cfg.workTapeSymbols 3 = base.workTapeSymbols 3 := rfl
    have hip : cfg.inputSymbol = base.inputSymbol := rfl
    simp only [universalInterpreter, hr3, hip, hi, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    change (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
      if a.state.isNone then none else some .main⟩ : Action 4 Bool UniversalControl) = _
    cases a.state <;> rfl
  change (universalInterpreter.tr _ cfg.inputSymbol cfg.workTapeSymbols).apply cfg = _
  rw [htr]
  have hmove := universalInput_move α src a.inputTape
  refine Cfg.ext rfl hmove.1 ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact add_zero _
    · exact add_zero _
    · rfl
    · exact hmove.2

/-- A live lookup reaches the pending action whose application realizes one source transition.

**Proof sketch.** Read the virtual input and mirrored work symbol, rewind the
table, skip its count and initial-state fields, and select the source record.
Read its eight fixed bits and prepare its successor, stopping immediately before
the source action. Concatenate the exact runs; identify the pending native action
separately. The old cursor, count prefix, and all skipped records are each
bounded by the serialization length; every source state index is below the
number of states. The resulting bound is `3L + 5N + 20`. -/
private lemma timedCut_live_block (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (p : ℕ)
    (hp : p ≤ M.serialize.length) (hs : src.state ≠ none) :
    ∃ (d p' : ℕ) (ready : Cfg 4 Bool UniversalControl (pairEncode α x)),
      d ≤ 3 * M.serialize.length + 5 * (M.numStates + 1) + 20 ∧
      p' ≤ M.serialize.length ∧
      (∃ bits halt, ready.state = some (.applyRecord bits halt)) ∧
      timedCutInterpreter.runFrom (universalSimulationCfg M α src p) d = ready ∧
      universalInterpreter.step ready = universalSimulationCfg M α (M.tm.step src) p'  := by
  cases hq : src.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let base := universalSimulationCfg M α src p
    let index := universalRecordIndex src.inputSymbol (src.workTapeSymbols 0)
    let a := M.tm.tr q src.inputSymbol (fun _ => src.workTapeSymbols 0)
    obtain ⟨groups, before, after, hglen, hg, hblen, hparts⟩ :=
      timedCut_lookup_parts M q src.inputSymbol (src.workTapeSymbols 0)
    let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
    let pb := before.flatMap universalRecordBits
    let count := pairEncode (Nat.bits M.numStates) []
    let k := 2 * (Nat.bits M.numStates).length + 2
    let pre := timedCut_Header M ++ pg ++ pb
    let bits := universalActionBits a
    let p' := pre.length + 8 + universalNextOnes a.state
    let selectTime := 2 * q.val + pg.length + pb.length + 3
    let d := 1 + (p + 1) + k + (M.tm.q₀.val + 1) + selectTime + 8 +
      timedCut_NextCost a.state
    have hclen : count.length = k := by
      simpa [count, k] using universal_pair_length (Nat.bits M.numStates) []
    have hhlen : (timedCut_Header M).length = k + M.tm.q₀.val + 1 := by
      change (count ++ List.replicate M.tm.q₀.val true ++ [false]).length = _
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, hclen]
    have hplen : pre.length = (timedCut_Header M).length + pg.length + pb.length := by
      simp only [pre, List.length_append]
    have ht : M.serialize = pre ++ universalRecordBits a ++ after := by
      simpa only [pre, pg, pb, a, List.append_assoc] using hparts
    have hcfg : base = universalEvalCfg base .main M.serialize p (universalStateTape q.val) 1 := by
      simp only [base, universalSimulationCfg, universalEvalCfg, hq,
        Option.map_some, Option.getD_some]
      rfl
    have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
        src.inputSymbol := universalInput_read α src
    have hmain : timedCutInterpreter.runFrom base 1 =
        universalEvalCfg base (.rewindTable false index) M.serialize (p - 1)
          (universalStateTape q.val) 1 := by
      rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero]
      conv_lhs => rw [hcfg]
      have he := timedCut_Eval_step base .main (.rewindTable false index)
        M.serialize p (universalStateTape q.val) 1 .neg 0 none (by
          change universalAdmin (.rewindTable false (universalRecordIndex
            (if base.workTapeSymbols 3 = some true then none else base.inputSymbol)
            (base.workTapeSymbols 2))) .neg = _
          rw [hi]
          rfl)
      simpa only [SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.coe_zero,
        add_zero, sub_eq_add_neg] using he
    have hrew := timedCut_table_rewind base false index M.serialize
      (universalStateTape q.val) 1 p hp
    have hcount := timedCut_count_run base false index M.serialize
      (universalStateTape q.val) 1 (Nat.bits M.numStates) []
      (List.replicate M.tm.q₀.val true ++ false :: (pg ++ pb ++ universalRecordBits a ++ after))
      (by simpa [timedCut_Header, pairEncode, pg, pb, a, List.append_assoc] using hparts)
    have hc : timedCutInterpreter.runFrom
        (universalEvalCfg base (.countFirst false index) M.serialize 0 (universalStateTape q.val) 1) k =
      universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1 := by
      simpa only [Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.cast_zero,
        zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcount
    have hinit := timedCut_initial_skip base index M.serialize (universalStateTape q.val) 1
      M.tm.q₀.val count (pg ++ pb ++ universalRecordBits a ++ after)
      (by simpa [count, timedCut_Header, pg, pb, a, List.append_assoc] using hparts)
    have hinit' : timedCutInterpreter.runFrom
        (universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1)
        (M.tm.q₀.val + 1) =
      universalEvalCfg base (.group index) M.serialize (timedCut_Header M).length
        (universalStateTape q.val) 1 := by
      simpa only [hclen, hhlen, Nat.cast_add, Nat.cast_one] using hinit
    have hselect := timedCut_select base index M.serialize groups hg before hblen
      (timedCut_Header M) (universalRecordBits a ++ after)
      (by simpa only [a, List.append_assoc] using hparts)
    have hsel : timedCutInterpreter.runFrom
        (universalEvalCfg base (.group index) M.serialize (timedCut_Header M).length
          (universalStateTape q.val) 1) selectTime =
      universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
        (universalStateTape 0) 1 := by
      simpa only [hglen, hplen, Nat.cast_add] using hselect
    have hread := timedCut_read_fixed base M.serialize (universalStateTape 0) 1 bits pre
      (List.replicate (universalNextOnes a.state) true ++ false :: after)
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
      7 0 (fun _ => false) rfl (by intro i hi; exact False.elim (Nat.not_lt_zero _ hi))
    have hrd : timedCutInterpreter.runFrom
        (universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
          (universalStateTape 0) 1) 8 =
      universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
        (universalStateTape 0) 1 := by
      simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hread
    have hnext := timedCut_prepare_next base M.serialize bits a.state
      (pre ++ List.ofFn bits) after
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
    have hn : timedCutInterpreter.runFrom
        (universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
          (universalStateTape 0) 1) (timedCut_NextCost a.state) =
      universalEvalCfg base (.applyRecord bits a.state.isNone) M.serialize p'
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1 := by
      simpa only [p', List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat] using hnext
    have hrun := timedCut_run_join timedCutInterpreter
      (timedCut_run_join timedCutInterpreter
        (timedCut_run_join timedCutInterpreter
          (timedCut_run_join timedCutInterpreter
            (timedCut_run_join timedCutInterpreter
              (timedCut_run_join timedCutInterpreter hmain hrew) hc) hinit') hsel) hrd) hn
    have hstep : M.tm.step src = a.apply src := by
      have hw : src.workTapeSymbols = fun _ : Fin 1 => src.workTapeSymbols 0 := by
        funext i
        rw [Fin.eq_zero i]
      simp only [MultiTapeTM.step, hq]
      rw [hw]
    have hlength : M.serialize.length = pre.length + 8 +
        universalNextOnes a.state + 1 + after.length := by
      rw [ht, universal_record_shape]
      simp only [List.length_append, List.length_ofFn, List.length_replicate,
        List.length_cons, List.length_nil]
      omega
    have hnextBound : timedCut_NextCost a.state ≤ 2 * (M.numStates + 1) + 4 := by
      cases hnxt : a.state with
      | none => simp [timedCut_NextCost]
      | some q' => have hq' := q'.isLt; simp only [timedCut_NextCost]; omega
    have hqb := q.isLt
    have hq₀b := M.tm.q₀.isLt
    refine ⟨d, p', _, ?_, ?_, ⟨bits, a.state.isNone, rfl⟩, hrun, ?_⟩
    · dsimp only [d, selectTime]
      rw [hplen, hhlen] at hlength
      omega
    · dsimp only [p']; omega
    · rw [hstep]
      exact timed_apply_record M α src p p' a

/-- The physical prefix occupied by the twice-doubled clock and its delimiter. -/
private def timedClockPrefix (bs : List Bool) : List Bool :=
  bs.flatMap (fun b => [b, b, b, b]) ++ [false, false, true, true]

/-- Removing the clock region leaves precisely the original code-first pair. -/
private lemma timed_input_layout (bs α x : List Bool) :
    pairEncode (pairEncode bs α) x = timedClockPrefix bs ++ pairEncode α x := by
  induction bs with
  | nil => simp [pairEncode, timedClockPrefix]
  | cons b bs ih =>
    simpa only [pairEncode, timedClockPrefix, List.flatMap_cons, List.flatMap_append,
      List.cons_append, List.nil_append, List.append_assoc] using congrArg (fun l => b :: b :: b :: b :: l) ih

/-- The clock region has four physical cells per bit plus four delimiter cells. -/
private lemma timedClockPrefix_length (bs : List Bool) :
    (timedClockPrefix bs).length = 4 * bs.length + 4 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons] at *
    omega

/-- Finite control for separating the twice-doubled clock from the doubled code. -/
private inductive TimedPrefixControl where
  | clockFirst | clockSecond (b : Bool) | clockThird (b : Bool)
  | clockFourth (b : Bool) | clockEnd | codeFirst | codeSecond (b : Bool)
  deriving DecidableEq, Fintype

/-- The prefix parser stores only clock bits on its work tape and emits only code
bits. It stops on the outer separator, before reading the input suffix. -/
private def timedPrefixTM : FinTM Bool where
  k := 1
  State := TimedPrefixControl
  tm :=
    { q₀ := .clockFirst
      tr := fun q inp _ => match q with
        | .clockFirst => ⟨.pos, fun _ => (none, 0), none, inp.map .clockSecond⟩
        | .clockSecond b => ⟨.pos, fun _ => (none, 0), none, some (.clockThird b)⟩
        | .clockThird b => ⟨.pos, fun _ => (none, 0), none,
            some (if inp = some b then .clockFourth b else .clockEnd)⟩
        | .clockFourth b => ⟨.pos, fun _ => (some (some b), .pos), none, some .clockFirst⟩
        | .clockEnd => ⟨.pos, fun _ => (none, 0), none, some .codeFirst⟩
        | .codeFirst => ⟨.pos, fun _ => (none, 0), none, inp.map .codeSecond⟩
        | .codeSecond b =>
            if inp = some b then
              ⟨.pos, fun _ => (none, 0), some b, some .codeFirst⟩
            else ⟨.pos, fun _ => (none, 0), none, none⟩ }

/-- Configuration of the prefix parser, with its complete captured clock. -/
private def timedPrefixCfg (bs α x : List Bool) (q : Option TimedPrefixControl)
    (p : Fin ((pairEncode (pairEncode bs α) x).length + 2))
    (clock out : List Bool) : Cfg 1 Bool TimedPrefixControl (pairEncode (pairEncode bs α) x) :=
  ⟨q, p, fun _ => bufferTape clock, fun _ => clock.length, out⟩

/-- Length arithmetic for both nested delimiters. -/
private lemma timed_input_length (bs α x : List Bool) :
    (pairEncode (pairEncode bs α) x).length = 4 * bs.length + 2 * α.length + 6 + x.length := by
  rw [universal_pair_length, universal_pair_length]
  omega

/-- Every cell of a quadrupled clock bit has the same value. -/
private lemma timed_clock_get (bs α x : List Bool) (j r : ℕ)
    (hj : j < bs.length) (hr : r < 4) :
    (pairEncode (pairEncode bs α) x)[4 * j + r]? = some bs[j] := by
  rw [timed_input_layout]
  induction bs generalizing j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero =>
      have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    | succ j =>
      have hh := ih j (by simpa using hj)
      simpa only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
        List.getElem?_cons_succ, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm 4 r] using hh

/-- The inner separator is doubled by the outer pairing. -/
private lemma timed_clock_separator (bs α x : List Bool) (r : ℕ) (hr : r < 4) :
    (pairEncode (pairEncode bs α) x)[4 * bs.length + r]? =
      [false, false, true, true][r]? := by
  rw [timed_input_layout]
  induction bs with
  | nil =>
    have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  | cons b bs ih =>
    simpa only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 4 r,
      List.getElem?_cons_succ] using ih

/-- A non-writing parser transition advances exactly one physical input cell. -/
private lemma timedPrefix_advance (bs α x clock out : List Bool)
    (q : TimedPrefixControl) (q' : Option TimedPrefixControl) (emit : Option Bool)
    (p : ℕ) (hp : p < (pairEncode (pairEncode bs α) x).length) (b : Bool)
    (hb : (pairEncode (pairEncode bs α) x)[p]? = some b)
    (htr : ∀ ws, timedPrefixTM.tm.tr q (some b) ws =
      ⟨.pos, fun _ => (none, 0), emit, q'⟩) :
    timedPrefixTM.tm.step
      (timedPrefixCfg bs α x (some q) ⟨p + 1, by omega⟩ clock out) =
    timedPrefixCfg bs α x q' ⟨p + 2, by omega⟩ clock (out ++ emit.toList) := by
  have hr : (timedPrefixCfg bs α x (some q) ⟨p + 1, by omega⟩ clock out).inputSymbol =
      some b := (inputSymbol_at _ p (by omega) rfl).trans hb
  change (timedPrefixTM.tm.tr q _ _).apply _ = _
  rw [hr, htr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by change p + 1 ≠ (pairEncode (pairEncode bs α) x).length + 1; omega)
  · funext i; exact add_zero _

/-- The fourth cell of a clock bit appends exactly its undoubled value. -/
private lemma timedPrefix_write (bs α x clock : List Bool) (b : Bool)
    (p : ℕ) (hp : p < (pairEncode (pairEncode bs α) x).length) :
    timedPrefixTM.tm.step
      (timedPrefixCfg bs α x (some (.clockFourth b)) ⟨p + 1, by omega⟩ clock []) =
    timedPrefixCfg bs α x (some .clockFirst) ⟨p + 2, by omega⟩ (clock ++ [b]) [] := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by change p + 1 ≠ (pairEncode (pairEncode bs α) x).length + 1; omega)
  · funext i; exact (bufferTape_append clock b).symm
  · funext i
    change (clock.length : ℤ) + 1 = ((clock ++ [b]).length : ℤ)
    simp

/-- Clock extraction consumes four cells and stores one bit per iteration.
The physical suffix and the native output remain untouched.

**Proof sketch.** Induct on the clock prefix already consumed. Four physical copies
of a bit take four transitions, with just one write to the clock tape; concatenate
these runs while preserving the untouched code and input suffix. -/
private lemma timedPrefix_clock (bs α x : List Bool) :
    ∀ j, (hj : j ≤ bs.length) →
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * j) =
    timedPrefixCfg bs α x (some .clockFirst)
      ⟨4 * j + 1, by rw [timed_input_length]; omega⟩ (bs.take j) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    apply Cfg.ext <;> simp [timedPrefixTM, timedPrefixCfg]
  | succ j ih =>
    intro hj
    have hlen := timed_input_length bs α x
    have hj' : j < bs.length := by omega
    have h0 := timedPrefix_advance bs α x (bs.take j) [] .clockFirst
      (some (.clockSecond bs[j])) none (4 * j) (by omega) bs[j]
      (by simpa using timed_clock_get bs α x j 0 hj' (by omega)) (by intro ws; rfl)
    have h1 := timedPrefix_advance bs α x (bs.take j) [] (.clockSecond bs[j])
      (some (.clockThird bs[j])) none (4 * j + 1) (by omega) bs[j]
      (timed_clock_get bs α x j 1 hj' (by omega)) (by intro ws; rfl)
    have h2 := timedPrefix_advance bs α x (bs.take j) [] (.clockThird bs[j])
      (some (.clockFourth bs[j])) none (4 * j + 2) (by omega) bs[j]
      (timed_clock_get bs α x j 2 hj' (by omega)) (by intro ws; simp [timedPrefixTM])
    have h3 := timedPrefix_write bs α x (bs.take j) bs[j] (4 * j + 3) (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1 h2 h3
    conv_lhs => rw [show 4 * (j + 1) = 4 * j + 1 + 1 + 1 + 1 by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega), h0]
    rw [h1, h2, h3]
    have ht : bs.take j ++ [bs[j]] = bs.take (j + 1) := by
      rw [List.take_succ, List.getElem?_eq_getElem hj']
      rfl
    rw [ht]
    congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- The four physical delimiter cells transfer from clock capture to code extraction.

**Proof sketch.** Read the four separator cells in sequence. The first two zeros
are recognized as the start of the separator when the following one disagrees;
the fourth cell completes the switch to code extraction without writing a clock bit. -/
private lemma timedPrefix_clock_end (bs α x : List Bool) :
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 4) =
    timedPrefixCfg bs α x (some .codeFirst)
      ⟨4 * bs.length + 5, by rw [timed_input_length]; omega⟩ bs [] := by
  have hlen := timed_input_length bs α x
  have h0 := timedPrefix_advance bs α x bs [] .clockFirst (some (.clockSecond false)) none
    (4 * bs.length) (by omega) false
    (by simpa using timed_clock_separator bs α x 0 (by omega)) (by intro ws; rfl)
  have h1 := timedPrefix_advance bs α x bs [] (.clockSecond false) (some (.clockThird false)) none
    (4 * bs.length + 1) (by omega) false
    (timed_clock_separator bs α x 1 (by omega)) (by intro ws; rfl)
  have h2 := timedPrefix_advance bs α x bs [] (.clockThird false) (some .clockEnd) none
    (4 * bs.length + 2) (by omega) true
    (timed_clock_separator bs α x 2 (by omega)) (by intro ws; rfl)
  have h3 := timedPrefix_advance bs α x bs [] .clockEnd (some .codeFirst) none
    (4 * bs.length + 3) (by omega) true
    (timed_clock_separator bs α x 3 (by omega)) (by intro ws; rfl)
  simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1 h2 h3
  conv_lhs => rw [show 4 * bs.length + 4 = 4 * bs.length + 1 + 1 + 1 + 1 by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timedPrefix_clock bs α x bs.length (le_refl _), List.take_length, h0]
  rw [h1, h2, h3]

/-- Suffix indexing after the complete clock prefix. -/
private lemma timed_code_get (bs α x : List Bool) (j : ℕ) :
    (pairEncode (pairEncode bs α) x)[4 * bs.length + 4 + j]? = (pairEncode α x)[j]? := by
  rw [timed_input_layout, ← timedClockPrefix_length,
    List.getElem?_append_right (by omega)]
  simp

/-- An aligned pair in the code region contains the corresponding code bit. -/
private lemma timed_pair_get (α x : List Bool) (j : ℕ) (hj : j < α.length) :
    (pairEncode α x)[2 * j]? = some α[j] ∧
      (pairEncode α x)[2 * j + 1]? = some α[j] := by
  induction α generalizing j with
  | nil => simp at hj
  | cons b α ih =>
    cases j with
    | zero => simp [pairEncode]
    | succ j =>
      simpa only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
        Nat.mul_add, Nat.mul_one, Nat.add_assoc, List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih j (by simpa using hj)

/-- The aligned separator immediately follows the doubled code. -/
private lemma timed_pair_separator (α x : List Bool) :
    (pairEncode α x)[2 * α.length]? = some false ∧
      (pairEncode α x)[2 * α.length + 1]? = some true := by
  induction α with
  | nil => simp [pairEncode]
  | cons b α ih =>
    simpa only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      List.getElem?_cons_succ] using ih

/-- Code extraction emits the undoubled code prefix and preserves the stored clock.

**Proof sketch.** Induct on the code prefix. Each equal pair emits one code bit and
advances two input cells. The unequal terminal pair halts the parser without an
emission, leaving the saved clock unchanged. -/
private lemma timedPrefix_code (bs α x : List Bool) :
    ∀ j, (hj : j ≤ α.length) →
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 4 + 2 * j) =
    timedPrefixCfg bs α x (some .codeFirst)
      ⟨4 * bs.length + 4 + 2 * j + 1, by rw [timed_input_length]; omega⟩ bs (α.take j) := by
  intro j
  induction j with
  | zero => intro hj; simpa only [Nat.mul_zero, Nat.add_zero, List.take_zero] using timedPrefix_clock_end bs α x
  | succ j ih =>
    intro hj
    have hlen := timed_input_length bs α x
    have hj' : j < α.length := by omega
    have hr := timed_pair_get α x j hj'
    have h0 := timedPrefix_advance bs α x bs (α.take j) .codeFirst
      (some (.codeSecond α[j])) none (4 * bs.length + 4 + 2 * j) (by omega) α[j]
      (by rw [timed_code_get]; exact hr.1) (by intro ws; rfl)
    have h1 := timedPrefix_advance bs α x bs (α.take j) (.codeSecond α[j])
      (some .codeFirst) (some α[j]) (4 * bs.length + 4 + 2 * j + 1) (by omega) α[j]
      (by rw [Nat.add_assoc _ (2 * j) 1, timed_code_get]; exact hr.2)
      (by intro ws; simp [timedPrefixTM])
    simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1
    conv_lhs => rw [show 4 * bs.length + 4 + 2 * (j + 1) =
      4 * bs.length + 4 + 2 * j + 1 + 1 by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [h0, h1]
    have ht : α.take j ++ [α[j]] = α.take (j + 1) := by
      rw [List.take_succ, List.getElem?_eq_getElem hj']; rfl
    simp only [Option.toList_some, ht]
    congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- Exact completed parser configuration, including the clock tape and parked input.
Both delimiters are consumed, including when the clock and code are empty. -/
private lemma timedPrefix_complete (bs α x : List Bool) :
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 2 * α.length + 6) =
    timedPrefixCfg bs α x none
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩ bs α := by
  have hlen := timed_input_length bs α x
  have hr := timed_pair_separator α x
  have h0 := timedPrefix_advance bs α x bs α .codeFirst (some (.codeSecond false)) none
    (4 * bs.length + 4 + 2 * α.length) (by omega) false
    (by rw [timed_code_get]; exact hr.1) (by intro ws; rfl)
  have h1 := timedPrefix_advance bs α x bs α (.codeSecond false) none none
    (4 * bs.length + 4 + 2 * α.length + 1) (by omega) true
    (by rw [Nat.add_assoc _ (2 * α.length) 1, timed_code_get]; exact hr.2)
    (by intro ws; rfl)
  simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1
  conv_lhs => rw [show 4 * bs.length + 2 * α.length + 6 =
      4 * bs.length + 4 + 2 * α.length + 1 + 1 by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timedPrefix_code bs α x α.length (le_refl _), List.take_length]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [h0, h1]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- Little-endian value of a fixed-width clock word. -/
private def timedValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (timedValue bs)

/-- Canonical clock words represent their given deadline. -/
private lemma timedValue_bits (t : ℕ) : timedValue t.bits = t := by
  induction t using Nat.binaryRec' with
  | zero => simp [timedValue]
  | bit b t ht ih => rw [Nat.bits_append_bit t b ht]; exact congrArg (Nat.bit b) ih

/-- Fixed-width binary subtraction, carrying an underflow flag. -/
private def timedBorrow : Bool → List Bool → Bool × List Bool
  | carry, [] => (carry, [])
  | carry, b :: bs =>
    let rest := timedBorrow (carry && !b) bs
    (rest.1, Bool.xor b carry :: rest.2)

/-- A cleared borrow leaves the remaining word unchanged. -/
private lemma timedBorrow_false (bs : List Bool) : timedBorrow false bs = (false, bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [timedBorrow, ih]

/-- Subtraction preserves the allocated word width. -/
private lemma timedBorrow_length (carry : Bool) (bs : List Bool) :
    (timedBorrow carry bs).2.length = bs.length := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [timedBorrow, List.length_cons, ih]

/-- Borrow underflow detects exactly a zero remaining budget. -/
private lemma timedBorrow_underflow (bs : List Bool) :
    (timedBorrow true bs).1 = true ↔ timedValue bs = 0 := by
  induction bs with
  | nil => simp [timedBorrow, timedValue]
  | cons b bs ih =>
    cases b <;> simp [timedBorrow, timedBorrow_false, timedValue, Nat.bit_val, ih]

/-- A successful borrow removes exactly one transition from the budget. -/
private lemma timedBorrow_value (bs : List Bool) (h : 0 < timedValue bs) :
    timedValue (timedBorrow true bs).2 + 1 = timedValue bs := by
  induction bs with
  | nil => simp [timedValue] at h
  | cons b bs ih =>
    cases b with
    | false =>
      have ht : 0 < timedValue bs := by simpa [timedValue, Nat.bit_val] using h
      have hb := ih ht
      change Nat.bit true (timedValue (timedBorrow true bs).2) + 1 = Nat.bit false (timedValue bs)
      simp only [Nat.bit_val]
      change (2 * timedValue (timedBorrow true bs).2 + 1) + 1 = 2 * timedValue bs + 0
      omega
    | true => simp [timedBorrow, timedBorrow_false, timedValue, Nat.bit_val]

/-- Extra phases retain a selected action while its clock is serviced. -/
private inductive TimedControl where
  | work (q : UniversalControl)
  | clockBack (bits : Fin 8 → Bool) (halt : Bool)
  | borrow (bits : Fin 8 → Bool) (halt carry : Bool)
  | execute (bits : Fin 8 → Bool) (halt : Bool)
  | emitStart | emitBack | flush
  deriving DecidableEq, Fintype

/-- Four audited interpreter lanes followed by the clock and output buffer. -/
private def timedSix {A : Type} (core : Fin 4 → A) (clock buffer : A) : Fin 6 → A :=
  fun i => if i = 0 then core 0 else if i = 1 then core 1 else
    if i = 2 then core 2 else if i = 3 then core 3 else if i = 4 then clock else buffer

/-- Lift an interpreter action while buffering its emission and intercepting halt. -/
private def timedAction (a : Action 4 Bool UniversalControl) : Action 6 Bool TimedControl :=
  ⟨a.inputTape, timedSix a.workTapes (none, 0)
    (a.output.map some, if a.output = none then 0 else .pos), none,
    some ((a.state.map TimedControl.work).getD .emitStart)⟩

/-- A clock-only or output-buffer-only administrative action. -/
private def timedAdmin (q : Option TimedControl)
    (clock buffer : Option (Option Bool) × SignType) (emit : Option Bool := none) :
    Action 6 Bool TimedControl :=
  ⟨0, timedSix (fun _ => (none, 0)) clock buffer, emit, q⟩

/-- Finite timed interpreter. A selected action is applied only after a successful
borrow. Its halting transition remains live until the success tag and buffered
emissions have been flushed. A failed borrow emits only the timeout tag. -/
private def timedInterpreter : MultiTapeTM 6 Bool TimedControl where
  q₀ := .work .start
  tr := fun q inp ws => match q with
    | .work (.applyRecord bits halt) =>
        timedAdmin (some (.clockBack bits halt)) (none, .neg) (none, 0)
    | .work q => timedAction (universalInterpreter.tr q inp (fun i => ws (i.castAdd 2)))
    | .clockBack bits halt =>
        if ws 4 = none then timedAdmin (some (.borrow bits halt true)) (none, .pos) (none, 0)
        else timedAdmin (some (.clockBack bits halt)) (none, .neg) (none, 0)
    | .borrow bits halt carry => match ws 4 with
        | some b => timedAdmin (some (.borrow bits halt (carry && !b)))
            (some (some (Bool.xor b carry)), .pos) (none, 0)
        | none => if carry then timedAdmin none (none, 0) (none, 0) (some false)
            else timedAdmin (some (.execute bits halt)) (none, 0) (none, 0)
    | .execute bits halt =>
        timedAction (universalInterpreter.tr (.applyRecord bits halt) inp (fun i => ws (i.castAdd 2)))
    | .emitStart => timedAdmin (some .emitBack) (none, 0) (none, .neg)
    | .emitBack =>
        if ws 5 = none then timedAdmin (some .flush) (none, 0) (none, .pos) (some true)
        else timedAdmin (some .emitBack) (none, 0) (none, .neg)
    | .flush => match ws 5 with
        | some b => timedAdmin (some .flush) (none, 0) (none, .pos) (some b)
        | none => timedAdmin none (none, 0) (none, 0)

/-- The original output is represented on the buffer tape; no native emission
has occurred in a simulated checkpoint or during a table lookup. -/
private def timedLift {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) : Cfg 6 Bool TimedControl x :=
  ⟨some ((cfg.state.map TimedControl.work).getD .emitStart), cfg.inputPos,
    timedSix cfg.workTapes (bufferTape clock) (bufferTape cfg.output),
    timedSix cfg.workTapePos clock.length cfg.output.length, []⟩

/-- A non-record state is unaffected by the stopped-interpreter modification. -/
private lemma timedCut_regular (q : UniversalControl)
    (hq : ∀ bits halt, q ≠ .applyRecord bits halt) (inp : Option Bool)
    (ws : Fin 4 → Option Bool) :
    timedCutInterpreter.tr q inp ws = universalInterpreter.tr q inp ws := by
  cases q <;> first | rfl | exact (hq _ _ rfl).elim

/-- A live endpoint of the stopped interpreter excludes every earlier stop.
The same absorption argument also excludes earlier native halts. -/
private lemma timedCut_live_before {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    {s t : ℕ} (hst : s ≤ t) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    (timedCutInterpreter.runFrom cfg s).state ≠ none := by
  intro hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs] at ht
  exact ht hs

/-- Every transition strictly before a live endpoint avoids record application. -/
private lemma timedCut_no_record {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    {s t : ℕ} (hst : s < t) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    ∀ bits halt, (timedCutInterpreter.runFrom cfg s).state ≠ some (.applyRecord bits halt) := by
  intro bits halt hs
  have hl := timedCut_live_before cfg (show s + 1 ≤ t by omega) ht
  apply hl
  rw [MultiTapeTM.runFrom_succ_eq_step']
  simp only [MultiTapeTM.step, hs, timedCutInterpreter, Action.apply]

/-- The six lanes expose their four source reads and two auxiliary reads. -/
private lemma timedSix_core {A : Type} (a : Fin 4 → A) (b c : A) (i : Fin 4) :
    timedSix a b c (i.castAdd 2) = a i := by fin_cases i <;> rfl

/-- Applying a lifted source action captures even an emission on its halt transition. -/
private lemma timedAction_apply {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (a : Action 4 Bool UniversalControl) :
    (timedAction a).apply (timedLift cfg clock) = timedLift (a.apply cfg) clock := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    fin_cases i <;> cases ho : a.output <;>
      simp [timedAction, timedLift, timedSix, Action.apply, ho, bufferTape_append]
  · funext i
    fin_cases i <;> cases ho : a.output <;>
      simp [timedAction, timedLift, timedSix, Action.apply, ho]

/-- Every ordinary interpreter step replays in one physical timed-machine step.

**Proof sketch.** Exclude the pending-action state, so both controllers select
the same native action. The action-lifting identity preserves the four simulated
tapes, keeps the clock fixed, and captures any emission on the buffer. -/
private lemma timed_regular_step {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (hs : cfg.state ≠ none)
    (hq : ∀ bits halt, cfg.state ≠ some (.applyRecord bits halt)) :
    timedInterpreter.step (timedLift cfg clock) = timedLift (timedCutInterpreter.step cfg) clock := by
  cases he : cfg.state with
  | none => exact (hs he).elim
  | some q =>
    have hq' : ∀ bits halt, q ≠ .applyRecord bits halt := by
      intro bits halt hh; apply hq bits halt; simpa [hh] using he
    have hr : (fun i => (timedLift cfg clock).workTapeSymbols (i.castAdd 2)) =
        cfg.workTapeSymbols := by
      funext i; fin_cases i <;> rfl
    have hi : (timedLift cfg clock).inputSymbol = cfg.inputSymbol := rfl
    have htr : timedInterpreter.tr (.work q) (timedLift cfg clock).inputSymbol
        (timedLift cfg clock).workTapeSymbols =
        timedAction (universalInterpreter.tr q cfg.inputSymbol cfg.workTapeSymbols) := by
      cases q <;> first
        | exact (hq' _ _ rfl).elim
        | simp only [timedInterpreter, hr, hi]
    have hstate : (timedLift cfg clock).state = some (.work q) := by simp [timedLift, he]
    conv_lhs => unfold MultiTapeTM.step; rw [hstate]; dsimp only
    rw [htr, timedAction_apply]
    simp only [MultiTapeTM.step, he, timedCut_regular q hq']

/-- A stopped lookup with a live endpoint can be replayed unchanged. No countdown
or output phase is visited in its interior. -/
private lemma timed_replay {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (t : ℕ) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    timedInterpreter.runFrom (timedLift cfg clock) t =
      timedLift (timedCutInterpreter.runFrom cfg t) clock := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (timedCut_live_before cfg (by omega) ht),
      timed_regular_step _ clock (timedCut_live_before cfg (by omega) ht)
        (timedCut_no_record cfg (by omega) ht), MultiTapeTM.runFrom_succ_eq_step']

/-- A single active tape lane, with every inactive tape taken from a base
configuration. This supports exact setup transductions in a multi-tape machine. -/
private def timed_laneCfg {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) : Cfg k A S x :=
  ⟨q, base.inputPos, Function.update base.workTapes lane (FinTM.sweepTape z l r),
    Function.update base.workTapePos lane z, base.output⟩

/-- An action that writes and moves just one lane, leaving input and output
stationary. -/
private def timed_laneAction {A S : Type} {k : ℕ} (lane : Fin k) (q : S)
    (s : Option A) (d : SignType) : Action k A S :=
  ⟨0, Function.update (fun _ => (none, 0)) lane (some s, d), none, some q⟩

/-- The active lane reads the first unprocessed zipper entry. -/
private lemma timed_laneCfg_read {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) :
    (timed_laneCfg base lane q z l r).workTapeSymbols lane = r.head?.join := by
  simp only [timed_laneCfg, Cfg.workTapeSymbols, Function.update_self, FinTM.sweepTape_read]

/-- The right-moving zipper identity lifts to one lane of any machine. -/
private lemma timed_laneCfg_right {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S) (q' : S)
    (z : ℤ) (l r : List (Option A)) (a b : Option A) :
    (timed_laneAction lane q' b .pos).apply (timed_laneCfg base lane q z l (a :: r)) =
      timed_laneCfg base lane (some q') (z + 1) (b :: l) r := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    by_cases hi : i = lane
    · subst i
      simp only [timed_laneAction, timed_laneCfg, Action.apply, Function.update_self]
      exact FinTM.sweepTape_right z l r a b
    · simp only [timed_laneAction, timed_laneCfg, Action.apply, Function.update_of_ne hi]
  · funext i
    by_cases hi : i = lane
    · subst i
      simp [timed_laneAction, timed_laneCfg]
    · simp [timed_laneAction, timed_laneCfg, hi]
  · exact List.append_nil _

/-- A finite forward transduction on one lane has exact cost equal to its word
length, without changing inactive tapes.
**Proof sketch.** The first entry supplies the local transition hypothesis.
One write-and-right step moves it into the left zipper stack, and induction
processes the remaining word. The full resulting configuration is retained. -/
private lemma timed_lane_run {A S R C : Type} {k : ℕ} {x : List A}
    (tm : MultiTapeTM k A S) (lane : Fin k)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s c inp ws, ws lane = some (symbol c) →
      tm.tr (state s) inp ws = timed_laneAction lane (state (visit s c).1)
        (some (symbol (visit s c).2)) .pos)
    (base : Cfg k A S x) (as : List C) (s : R)
    (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (timed_laneCfg base lane (some (state s)) z l
      (as.map (fun c => some (symbol c)) ++ r)) as.length =
    timed_laneCfg base lane (some (state (FinTM.sweepFold visit s as).1)) (z + as.length)
      (((FinTM.sweepFold visit s as).2.map (fun c => some (symbol c))).reverse ++ l) r := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, MultiTapeTM.runFrom_zero,
      FinTM.sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (timed_laneCfg base lane (some (state s)) z l
        (some (symbol a) :: (as.map (fun c => some (symbol c)) ++ r))).workTapeSymbols lane =
        some (symbol a) := timed_laneCfg_read _ _ _ _ _ _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [htr s a _ _ hr, timed_laneCfg_right, ih]
    simp only [FinTM.sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega


/-- A focused clock write agrees with the generic one-lane transducer action. -/
private lemma timedAdmin_clock (q : TimedControl) (b : Option Bool) (d : SignType) :
    timedAdmin (some q) (some b, d) (none, 0) = timed_laneAction (4 : Fin 6) q b d := by
  unfold timedAdmin timed_laneAction
  congr 1
  funext i
  fin_cases i <;> rfl

/-- A borrow sweep is the same local fold as the fixed-width arithmetic function. -/
private lemma timedBorrow_fold (carry : Bool) (bs : List Bool) :
    sweepFold (fun carry b => (carry && !b, Bool.xor b carry)) carry bs = timedBorrow carry bs := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [sweepFold, timedBorrow, ih]

/-- Exact borrow transduction; neither source tapes nor buffered output are touched. -/
private lemma timed_borrow_run {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt carry : Bool) (bs : List Bool)
    (z : ℤ) (l r : List (Option Bool)) :
    timedInterpreter.runFrom
      (timed_laneCfg base 4 (some (.borrow bits halt carry)) z l (bs.map some ++ r)) bs.length =
    timed_laneCfg base 4 (some (.borrow bits halt (timedBorrow carry bs).1))
      (z + bs.length) (((timedBorrow carry bs).2.map some).reverse ++ l) r := by
  have h := timed_lane_run timedInterpreter (4 : Fin 6) (TimedControl.borrow bits halt)
    (fun b : Bool => b) (fun carry b => (carry && !b, Bool.xor b carry))
    (by
      intro carry b inp ws hw
      simp only [timedInterpreter, hw]
      exact timedAdmin_clock _ _ _) base bs carry z l r
  simpa only [timedBorrow_fold] using h

/-- Moving the frontier of a finite zipper does not change its tape. -/
private lemma timed_sweep_shift (z : ℤ) (l w r : List (Option Bool)) :
    sweepTape z l (w ++ r) = sweepTape (z + w.length) (w.reverse ++ l) r := by
  induction w generalizing z l with
  | nil => simp
  | cons a w ih =>
    have hs : Function.update (FinTM.sweepTape z l (a :: (w ++ r))) z a =
        FinTM.sweepTape z l (a :: (w ++ r)) := by
      funext p
      by_cases hp : p = z
      · subst p
        simp [FinTM.sweepTape_read]
      · exact Function.update_of_ne hp _ _
    have hm := FinTM.sweepTape_right z l (w ++ r) a a
    rw [hs] at hm
    simp only [List.cons_append, List.length_cons, List.reverse_cons]
    rw [hm, ih]
    simp only [List.append_assoc, List.singleton_append]
    congr 1
    omega

/-- A Boolean buffer is a zipper with an empty left stack. -/
private lemma timed_buffer_zipper (bs : List Bool) :
    bufferTape bs = sweepTape 0 [] (bs.map some) := by
  funext z
  by_cases h : 0 ≤ z
  · simp only [bufferTape, if_pos h, sweepTape, not_lt.mpr h, ↓reduceIte, sub_zero,
      List.getElem?_map]
    cases bs[z.toNat]? <;> rfl
  · simp [bufferTape, sweepTape, h, show z < 0 by omega]

/-- At the right blank the full buffer occupies the reversed left zipper stack. -/
private lemma timed_buffer_zipper_end (bs : List Bool) :
    bufferTape bs = sweepTape bs.length (bs.map some).reverse [] := by
  rw [timed_buffer_zipper]
  have h := timed_sweep_shift 0 [] (bs.map some) []
  simpa using h

/-- A clock phase overrides only the clock lane and the finite control. -/
private def timedClockCfg {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (q : TimedControl) (bs : List Bool) (p : ℤ) : Cfg 6 Bool TimedControl x :=
  { base with
    state := some q
    workTapes := Function.update base.workTapes 4 (bufferTape bs)
    workTapePos := Function.update base.workTapePos 4 p }

/-- A stationary-input clock action has an explicit one-lane effect. -/
private lemma timedClock_step {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (q q' : TimedControl) (bs : List Bool) (p : ℤ) (d : SignType)
    (htr : ∀ inp ws, ws 4 = bufferTape bs p →
      timedInterpreter.tr q inp ws = timedAdmin (some q') (none, d) (none, 0)) :
    timedInterpreter.step (timedClockCfg base q bs p) = timedClockCfg base q' bs (p + d) := by
  change (timedInterpreter.tr q _ _).apply _ = _
  rw [htr _ _ (by simp [timedClockCfg, Cfg.workTapeSymbols])]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [timedAdmin, timedSix, timedClockCfg, Action.apply]

/-- Rewind from the last clock bit to the left blank, then enter the borrow pass. -/
private lemma timed_clock_back {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt : Bool) (bs : List Bool) :
    ∀ j, j ≤ bs.length →
    timedInterpreter.runFrom (timedClockCfg base (.clockBack bits halt) bs (j - 1)) (j + 1) =
      timedClockCfg base (.borrow bits halt true) bs 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have h := timedClock_step base (.clockBack bits halt) (.borrow bits halt true) bs (-1) .pos
      (by intro inp ws hw; simp [timedInterpreter, hw])
    simpa using h
  | succ j ih =>
    intro hj
    have hr : bufferTape bs (j : ℤ) = some bs[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have h := timedClock_step base (.clockBack bits halt) (.clockBack bits halt) bs j .neg
      (by intro inp ws hw; simp [timedInterpreter, hw, hr])
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = j by omega, h]
    simpa using ih (by omega)

/-- Borrowing rewrites the clock in exactly one pass and preserves its width. -/
private lemma timed_clock_borrow {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt carry : Bool) (bs : List Bool) :
    timedInterpreter.runFrom (timedClockCfg base (.borrow bits halt carry) bs 0) bs.length =
    timedClockCfg base (.borrow bits halt (timedBorrow carry bs).1)
      (timedBorrow carry bs).2 bs.length := by
  have h := timed_borrow_run base bits halt carry bs 0 [] []
  have hstart : timed_laneCfg base 4 (some (.borrow bits halt carry)) 0 []
      (bs.map some ++ []) = timedClockCfg base (.borrow bits halt carry) bs 0 := by
    simp only [List.append_nil, timed_laneCfg, timedClockCfg, ← timed_buffer_zipper]
  have hend : timed_laneCfg base 4 (some (.borrow bits halt (timedBorrow carry bs).1))
      (0 + (bs.length : ℤ)) (((timedBorrow carry bs).2.map some).reverse ++ []) [] =
      timedClockCfg base (.borrow bits halt (timedBorrow carry bs).1)
        (timedBorrow carry bs).2 bs.length := by
    simp only [zero_add, List.append_nil, timed_laneCfg, timedClockCfg]
    rw [← timedBorrow_length carry bs, ← timed_buffer_zipper_end]
  rw [hstart, hend] at h
  exact h

/-- The selected action enters the clock rewind without applying a source transition. -/
private lemma timed_clock_start {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.step (timedLift cfg bs) =
    timedClockCfg (timedLift cfg bs) (.clockBack bits halt) bs (bs.length - 1) := by
  have hstate : (timedLift cfg bs).state = some (.work (.applyRecord bits halt)) := by
    simp [timedLift, hs]
  unfold MultiTapeTM.step
  rw [hstate]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i; fin_cases i <;> simp [timedInterpreter, timedAdmin, timedLift, timedSix, timedClockCfg, Action.apply]
  · funext i; fin_cases i <;> simp [timedInterpreter, timedAdmin, timedLift, timedSix, timedClockCfg, Action.apply, sub_eq_add_neg]

/-- A ready action reaches the completed borrow pass in `2w+2` transitions. -/
private lemma timed_clock_pass {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 2) =
    timedClockCfg (timedLift cfg bs) (.borrow bits halt (timedBorrow true bs).1)
      (timedBorrow true bs).2 bs.length := by
  have h0 : timedInterpreter.runFrom (timedLift cfg bs) 1 =
      timedClockCfg (timedLift cfg bs) (.clockBack bits halt) bs (bs.length - 1) := by
    exact timed_clock_start cfg bs bits halt hs
  have h1 := timed_clock_back (timedLift cfg bs) bits halt bs bs.length (le_refl _)
  have h2 := timed_clock_borrow (timedLift cfg bs) bits halt true bs
  have h := timedCut_run_join timedInterpreter (timedCut_run_join timedInterpreter h0 h1) h2
  simpa only [show 1 + (bs.length + 1) + bs.length = 2 * bs.length + 2 by omega] using h

/-- After a successful borrow, the retained action executes once. -/
private lemma timed_execute {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.step { timedLift cfg bs with state := some (.execute bits halt) } =
      timedLift (universalInterpreter.step cfg) bs := by
  have hr : (fun i => (timedLift cfg bs).workTapeSymbols (i.castAdd 2)) =
      cfg.workTapeSymbols := by funext i; fin_cases i <;> rfl
  change (timedAction (universalInterpreter.tr (.applyRecord bits halt) cfg.inputSymbol
    (fun i => (timedLift cfg bs).workTapeSymbols (i.castAdd 2)))).apply
      { timedLift cfg bs with state := some (.execute bits halt) } = _
  rw [hr]
  have h := timedAction_apply cfg bs (universalInterpreter.tr (.applyRecord bits halt)
    cfg.inputSymbol cfg.workTapeSymbols)
  simpa only [MultiTapeTM.step, hs, Action.apply] using h

/-- A positive budget is decremented exactly once before the selected source action.

**Proof sketch.** Rewind the clock and run the fixed-width borrow sweep. Positive
value rules out a remaining carry at the right blank; one transition selects
execution and the next applies the source action through the buffering wrapper. -/
private lemma timed_clock_success {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) (hv : 0 < timedValue bs) :
    timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 4) =
      timedLift (universalInterpreter.step cfg) (timedBorrow true bs).2 := by
  have hf : (timedBorrow true bs).1 = false := by
    cases h : (timedBorrow true bs).1
    · rfl
    · have hz := (timedBorrow_underflow bs).mp h; omega
  let after := timedClockCfg (timedLift cfg bs) (.borrow bits halt false) (timedBorrow true bs).2 bs.length
  have hr : after.workTapeSymbols 4 = none := by
    simp only [after, timedClockCfg, Cfg.workTapeSymbols, Function.update_self]
    rw [← timedBorrow_length true bs, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
  have he : timedInterpreter.step after =
      { timedLift cfg (timedBorrow true bs).2 with state := some (.execute bits halt) } := by
    change (timedInterpreter.tr (.borrow bits halt false) after.inputSymbol after.workTapeSymbols).apply after = _
    simp only [timedInterpreter, hr, Bool.false_eq_true, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i; fin_cases i <;> simp [after, timedAdmin, timedClockCfg, timedLift, timedSix, Action.apply]
    · funext i; fin_cases i <;> simp [after, timedAdmin, timedClockCfg, timedLift, timedSix, Action.apply, timedBorrow_length]
  rw [show 2 * bs.length + 4 = (2 * bs.length + 2) + 1 + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timed_clock_pass cfg bs bits halt hs, hf]
  rw [he, timed_execute cfg _ bits halt hs]

/-- A zero budget halts with only the timeout tag, even if source emissions were buffered. -/
private lemma timed_clock_timeout {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) (hv : timedValue bs = 0) :
    let dst := timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 3)
    dst.state = none ∧ dst.output = [false] := by
  dsimp only
  have hf := (timedBorrow_underflow bs).mpr hv
  rw [show 2 * bs.length + 3 = (2 * bs.length + 2) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', timed_clock_pass cfg bs bits halt hs, hf]
  have hr : (timedClockCfg (timedLift cfg bs) (.borrow bits halt true)
      (timedBorrow true bs).2 bs.length).workTapeSymbols 4 = none := by
    simp only [timedClockCfg, Cfg.workTapeSymbols, Function.update_self]
    rw [← timedBorrow_length true bs, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
  let after := timedClockCfg (timedLift cfg bs) (.borrow bits halt true)
    (timedBorrow true bs).2 bs.length
  have he : timedInterpreter.step after = (timedAdmin none (none, 0) (none, 0) (some false)).apply after := by
    change (timedInterpreter.tr (.borrow bits halt true) after.inputSymbol after.workTapeSymbols).apply after = _
    simp only [timedInterpreter, show after.workTapeSymbols 4 = none from hr, ↓reduceIte]
  change (timedInterpreter.step after).state = none ∧ (timedInterpreter.step after).output = [false]
  rw [he]
  exact ⟨rfl, rfl⟩

/-- Output-phase configurations retain all simulation and clock tapes. -/
private def timedOutputCfg {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (q : Option TimedControl) (p : ℤ) (out : List Bool) : Cfg 6 Bool TimedControl x :=
  { timedLift cfg bs with
    state := q
    workTapePos := Function.update (timedLift cfg bs).workTapePos 5 p
    output := out }

/-- A buffer scan moves only the output-buffer head and appends its designated bit. -/
private lemma timed_output_step {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (q : TimedControl) (q' : Option TimedControl) (p : ℤ)
    (out : List Bool) (d : SignType) (emit : Option Bool)
    (htr : ∀ inp ws, ws 5 = bufferTape cfg.output p →
      timedInterpreter.tr q inp ws = timedAdmin q' (none, 0) (none, d) emit) :
    timedInterpreter.step (timedOutputCfg cfg bs (some q) p out) =
      timedOutputCfg cfg bs q' (p + d) (out ++ emit.toList) := by
  change (timedInterpreter.tr q _ _).apply _ = _
  rw [htr _ _ (by simp [timedOutputCfg, timedLift, timedSix, Cfg.workTapeSymbols])]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [timedOutputCfg, timedLift, timedSix, timedAdmin, Action.apply]

/-- Rewinding the buffer emits the success tag at the left blank, before any data bit. -/
private lemma timed_output_back {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs out : List Bool) : ∀ j, j ≤ cfg.output.length →
    timedInterpreter.runFrom (timedOutputCfg cfg bs (some .emitBack) (j - 1) out) (j + 1) =
      timedOutputCfg cfg bs (some .flush) 0 (out ++ [true]) := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have h := timed_output_step cfg bs .emitBack (some .flush) (-1) out .pos (some true)
      (by intro inp ws hw; simp [timedInterpreter, hw])
    simpa using h
  | succ j ih =>
    intro hj
    have hr : bufferTape cfg.output (j : ℤ) = some cfg.output[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have h := timed_output_step cfg bs .emitBack (some .emitBack) j out .neg none
      (by intro inp ws hw; simp [timedInterpreter, hw, hr])
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = j by omega, h]
    simpa using ih (by omega)

/-- Flushing emits each remaining buffer bit once, then halts at the right blank.

**Proof sketch.** Induct on the unread buffer suffix. A symbol is emitted while
the buffer head advances; after the final symbol, the right blank produces the
halting transition without another emission. -/
private lemma timed_output_forward {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (r : List Bool) : ∀ l out, cfg.output = l ++ r →
    timedInterpreter.runFrom (timedOutputCfg cfg bs (some .flush) l.length out) (r.length + 1) =
      timedOutputCfg cfg bs none cfg.output.length (out ++ r) := by
  induction r with
  | nil =>
    intro l out hr
    have he : cfg.output = l := by simpa using hr
    have hread : bufferTape cfg.output (l.length : ℤ) = none := by
      rw [he, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
    have h := timed_output_step cfg bs .flush none l.length out 0 none
      (by intro inp ws hw; simp [timedInterpreter, hw, hread])
    simpa [he] using h
  | cons b r ih =>
    intro l out hr
    have hread : bufferTape cfg.output (l.length : ℤ) = some b := by
      rw [hr]; exact universal_table_read l r b
    have h := timed_output_step cfg bs .flush (some .flush) l.length out .pos (some b)
      (by intro inp ws hw; simp [timedInterpreter, hw, hread])
    rw [show (b :: r).length + 1 = (r.length + 1) + 1 by simp,
      MultiTapeTM.runFrom_succ_eq_step, h]
    have hh := ih (l ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hr)
    simpa only [SignType.pos_eq_one, SignType.coe_one, Option.toList_some,
      List.length_append, List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one,
      List.append_assoc, List.singleton_append] using hh

/-- Source halting is followed by the success tag and exactly the buffered output. -/
private lemma timed_flush {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (hs : cfg.state = none) :
    let dst := timedInterpreter.runFrom (timedLift cfg bs) (2 * cfg.output.length + 3)
    dst.state = none ∧ dst.output = true :: cfg.output := by
  dsimp only
  have hcfg : timedLift cfg bs = timedOutputCfg cfg bs (some .emitStart) cfg.output.length [] := by
    refine Cfg.ext ?_ rfl rfl ?_ rfl
    · simp [timedLift, timedOutputCfg, hs]
    · funext i; fin_cases i <;> rfl
  have h0 := timed_output_step cfg bs .emitStart (some .emitBack) cfg.output.length [] .neg none
    (by intros; rfl)
  have h1 := timed_output_back cfg bs [] cfg.output.length (le_refl _)
  have h2 := timed_output_forward cfg bs cfg.output [] [true] (by simp)
  have hstart : timedInterpreter.runFrom (timedLift cfg bs) 1 =
      timedOutputCfg cfg bs (some .emitBack) (cfg.output.length - 1) [] := by
    rw [hcfg]
    simpa using h0
  have h := timedCut_run_join timedInterpreter (timedCut_run_join timedInterpreter hstart h1) h2
  have ht : 1 + (cfg.output.length + 1) + (cfg.output.length + 1) = 2 * cfg.output.length + 3 := by omega
  rw [ht] at h
  rw [h]
  exact ⟨rfl, rfl⟩

/-- The parser is live immediately before consuming the final separator cell. -/
private lemma timedPrefix_penultimate (bs α x : List Bool) :
    (timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 2 * α.length + 5)).state ≠ none := by
  have hlen := timed_input_length bs α x
  have h0 := timedPrefix_advance bs α x bs α .codeFirst (some (.codeSecond false)) none
    (4 * bs.length + 4 + 2 * α.length) (by omega) false
    (by rw [timed_code_get]; exact (timed_pair_separator α x).1) (by intro ws; rfl)
  rw [show 4 * bs.length + 2 * α.length + 5 =
      (4 * bs.length + 4 + 2 * α.length) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', timedPrefix_code bs α x α.length (le_refl _),
    List.take_length, h0]
  exact Option.some_ne_none _

/-- No earlier parser step can halt, since halting is absorbing. -/
private lemma timedPrefix_live (bs α x : List Bool) (s : ℕ)
    (hs : s < 4 * bs.length + 2 * α.length + 6) :
    (timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x)) s).state ≠ none := by
  intro h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show s ≤ 4 * bs.length + 2 * α.length + 5 by omega)
  have hp := timedPrefix_penultimate bs α x
  rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ h] at hp
  exact hp h

/-- Only the extracted code is supplied to the scheme's canonizer. -/
private def timedCanonTM (c : EffectiveMachineCode) : FinTM Bool :=
  bufferedCompTM timedPrefixTM c.canonizer

/-- The parser's unique work tape remains the clock lane of the composed canonizer. -/
private def timedCanonClock (c : EffectiveMachineCode) : Fin (timedCanonTM c).k :=
  Fin.castAdd (1 + c.canonizer.k) (0 : Fin 1)

/-- Exact prefix-local canonizer entry retains the entire clock word unchanged. -/
private lemma timedCanon_start (c : EffectiveMachineCode) (bs α x : List Bool) :
    (timedCanonTM c).tm.runFrom ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8) =
    bufferedSecondCfg timedPrefixTM c.canonizer (c.canonizer.tm.initCfg α) true
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
      (fun _ => bufferTape bs) (fun _ => bs.length) := by
  change (bufferedCompTM timedPrefixTM c.canonizer).tm.runFrom _ _ = _
  rw [show 4 * bs.length + 3 * α.length + 8 =
      (4 * bs.length + 2 * α.length + 6) + (α.length + 2) by omega,
    MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run timedPrefixTM c.canonizer _ _ (fun s hs => timedPrefix_live bs α x s hs),
    timedPrefix_complete]
  exact bufferedFirstCfg_rewind timedPrefixTM c.canonizer _ rfl

/-- Canonization uses virtual input `α`; physical input and clock remain stationary. -/
private lemma timedCanon_run (c : EffectiveMachineCode) (bs α x : List Bool) (t : ℕ) :
    ∃ b, (timedCanonTM c).tm.runFrom
      ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8 + t) =
    bufferedSecondCfg timedPrefixTM c.canonizer
      (c.canonizer.tm.runFrom (c.canonizer.tm.initCfg α) t) b
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
      (fun _ => bufferTape bs) (fun _ => bs.length) := by
  rw [MultiTapeTM.runFrom_add, timedCanon_start]
  obtain ⟨b, -, he⟩ := bufferedSecondCfg_run timedPrefixTM c.canonizer
    (c.canonizer.tm.initCfg α) true
    (by constructor <;> intro h <;> simp_all [VirtualTag])
    (x := pairEncode (pairEncode bs α) x)
    ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
    (fun _ => bufferTape bs) (fun _ => bs.length) t
  exact ⟨b, he⟩

/-- Canonizer completion identifies the table, parked input, and preserved clock. -/
private lemma timedCanon_complete (c : EffectiveMachineCode) (bs α x : List Bool) :
    let cfg := (timedCanonTM c).tm.runFrom
      ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8 + c.canonizerTime α.length)
    cfg.state = none ∧ cfg.output = (c.decode α).serialize ∧
      cfg.inputPos.val = 4 * bs.length + 2 * α.length + 7 ∧
      cfg.workTapes (timedCanonClock c) = bufferTape bs ∧
      cfg.workTapePos (timedCanonClock c) = bs.length := by
  dsimp only
  obtain ⟨b, he⟩ := timedCanon_run c bs α x (c.canonizerTime α.length)
  rw [he]
  have hc := (computesInTime_iff _ _ _ _).mp (c.canonizer_computes α)
  refine ⟨?_, hc.2, rfl, ?_, ?_⟩
  · simp only [bufferedSecondCfg, hc.1, Option.map_none]
  · simp [bufferedSecondCfg, timedCanonClock]
  · simp [bufferedSecondCfg, timedCanonClock]

/-- The exact deadline-inclusive answer of a source configuration. -/
private def timedAnswer (M : CodeTM) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (t : ℕ) : List Bool :=
  let dst := M.tm.runFrom src t
  if dst.state = none then true :: dst.output else [false]

/-- The timed interpreter finishes from every checkpoint, within a uniform ledger.

**Proof sketch.** Induct on the remaining numeric budget. Already-halted sources
flush immediately. Otherwise the stopped lookup reaches a pending action; a zero
budget times out without applying it, while a positive budget borrows once and
applies it. The recursive call is made on the successor, including its halting
state. Thus halting on the final allowed transition reaches the success branch.
The emission-length increment is at most one, leaving two units of slack per
transition in the displayed bound. -/
private lemma timed_interpret_finishes (M : CodeTM) (α : List Bool) {x : List Bool}
    (r : ℕ) : ∀ (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (p : ℕ) (bs : List Bool),
    p ≤ M.serialize.length → timedValue bs = r →
    ∃ d, d ≤ (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8) * (r + 1) +
        2 * src.output.length ∧
      let dst := timedInterpreter.runFrom (timedLift (universalSimulationCfg M α src p) bs) d
      dst.state = none ∧ dst.output = timedAnswer M src r := by
  induction r with
  | zero =>
    intro src p bs hp hv
    by_cases hs : src.state = none
    · refine ⟨2 * src.output.length + 3, by omega, ?_⟩
      have h := timed_flush (universalSimulationCfg M α src p) bs
        (by simp [universalSimulationCfg, hs])
      simpa only [universalSimulationCfg, timedAnswer, MultiTapeTM.runFrom_zero, hs, ↓reduceIte] using h
    · obtain ⟨d, p', ready, hd, hp', ⟨bits, halt, hready⟩, he, ha⟩ := timedCut_live_block M α src p hp hs
      have hreplay := timed_replay (universalSimulationCfg M α src p) bs d (by rw [he, hready]; simp)
      rw [he] at hreplay
      have htimeout := timed_clock_timeout ready bs bits halt hready hv
      refine ⟨d + (2 * bs.length + 3), by omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, hreplay]
      simpa only [timedAnswer, MultiTapeTM.runFrom_zero, if_neg hs] using htimeout
  | succ r ih =>
    intro src p bs hp hv
    by_cases hs : src.state = none
    · have hpos : 3 ≤
          (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8) * (r + 1 + 1) := by
        have h := Nat.mul_le_mul_left
          (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8)
          (show 1 ≤ r + 1 + 1 by omega)
        omega
      refine ⟨2 * src.output.length + 3, by omega, ?_⟩
      have h := timed_flush (universalSimulationCfg M α src p) bs
        (by simp [universalSimulationCfg, hs])
      simpa only [universalSimulationCfg, timedAnswer, MultiTapeTM.runFrom_of_halt _ hs, hs, ↓reduceIte] using h
    · obtain ⟨d, p', ready, hd, hp', ⟨bits, halt, hready⟩, he, ha⟩ := timedCut_live_block M α src p hp hs
      have hreplay := timed_replay (universalSimulationCfg M α src p) bs d (by rw [he, hready]; simp)
      rw [he] at hreplay
      have hc := timed_clock_success ready bs bits halt hready (by omega)
      rw [ha] at hc
      have hv' : timedValue (timedBorrow true bs).2 = r := by
        have h := timedBorrow_value bs (by omega); omega
      obtain ⟨d', hd', hfinish⟩ := ih (M.tm.step src) p' (timedBorrow true bs).2 hp' hv'
      have hlength : (M.tm.step src).output.length ≤ src.output.length + 1 := by
        rw [MultiTapeTM.step_output, List.length_append]
        cases M.tm.outputSymbol src <;> simp
      rw [timedBorrow_length] at hd'
      refine ⟨d + (2 * bs.length + 4) + d', ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hreplay, hc]
        simpa only [timedAnswer, MultiTapeTM.runFrom_succ_eq_step] using hfinish

/-- The binary clock's width is bounded even at deadline zero. -/
private lemma timed_bits_length (t : ℕ) : t.bits.length ≤ t := by
  induction t using Nat.binaryRec' with
  | zero => simp
  | bit b t ht ih =>
    rw [Nat.bits_append_bit t b ht, List.length_cons]
    cases b with
    | false =>
      have hn : t ≠ 0 := by intro h; have hh := ht h; cases hh
      simp only [Nat.bit_val]
      omega
    | true => change t.bits.length + 1 ≤ 2 * t + 1; omega

/-- The five fresh lanes are table, state, simulated work, input marker, and output. -/
private def timedFive {A : Type} (core : Fin 4 → A) (buffer : A) : Fin 5 → A :=
  fun i => if i = 0 then core 0 else if i = 1 then core 1 else
    if i = 2 then core 2 else if i = 3 then core 3 else buffer

/-- Interpreter actions reuse the parser's clock lane and five fresh lanes. -/
private def timedFrameAction (M : FinTM Bool) (clock : Fin M.k)
    (a : Action 6 Bool TimedControl) : Action (M.k + 5) Bool (Option M.State ⊕ TimedControl) :=
  ⟨a.inputTape, Fin.addCases
    (Function.update (fun _ => (none, 0)) clock (a.workTapes 4))
    (timedFive (fun i => a.workTapes (i.castAdd 2)) (a.workTapes 5)),
    a.output, a.state.map Sum.inr⟩

/-- Capture the canonizer's table, then run the timed interpreter with the retained clock. -/
private def timedCaptureTM (M : FinTM Bool) (clock : Fin M.k) : FinTM Bool where
  k := M.k + (1 + 4)
  State := Option M.State ⊕ TimedControl
  tm :=
    { q₀ := .inl (some M.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M.tm.tr q inp (fun i => work (Fin.castAdd 5 i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none => controlAction 0 (some (.inr timedInterpreter.q₀))
        | .inr q => timedFrameAction M clock (timedInterpreter.tr q inp
            (timedSix (fun i => work (Fin.natAdd M.k (i.castAdd 1)))
              (work (clock.castAdd 5)) (work (Fin.natAdd M.k (4 : Fin 5))))) }

/-- Complete first-phase configuration of the output-capture wrapper. -/
private def timedCaptureCfg (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x where
  state := some (.inl cfg.state)
  inputPos := cfg.inputPos
  workTapes := tapeBlocks cfg.workTapes (bufferTape cfg.output) (fun _ _ => none)
  workTapePos := tapeBlocks cfg.workTapePos cfg.output.length (fun _ => 0)
  output := []

/-- The capture wrapper starts with a blank table and blank interpreter tapes. -/
private lemma timedCapture_init (M : FinTM Bool) (clock : Fin M.k) (x : List Bool) :
    (timedCaptureTM M clock).tm.initCfg x =
      timedCaptureCfg M clock (M.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [timedCaptureCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [timedCaptureCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [timedCaptureCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [timedCaptureCfg, tapeBlocks]

/-- One live transition captures every emitted bit, including a bit emitted on
the source machine's halting transition. Administrative states remain live.

**Proof sketch.** The original work block and physical input move in lockstep.
An emission writes precisely the table's right blank and advances its head; the
buffer-append identity gives its new contents. No real output is emitted, and
the four later simulation and output-buffer tapes remain untouched. -/
private lemma timedCapture_step (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (hs : cfg.state ≠ none) :
    (timedCaptureTM M clock).tm.step (timedCaptureCfg M clock cfg) =
      timedCaptureCfg M clock (M.tm.step cfg) := by
  unfold MultiTapeTM.step
  cases hq : cfg.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (timedCaptureCfg M clock cfg).state = some (.inl (some q)) := by
      simp [timedCaptureCfg, hq]
    rw [hs']
    dsimp only [timedCaptureTM]
    have hr : (fun i => (timedCaptureCfg M clock cfg).workTapeSymbols
        (Fin.castAdd 5 i)) = cfg.workTapeSymbols := by
      funext i
      simp [timedCaptureCfg, Cfg.workTapeSymbols, tapeBlocks]
    have hi : (timedCaptureCfg M clock cfg).inputSymbol = cfg.inputSymbol := rfl
    rw [hr, hi]
    let a := M.tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M.k + (1 + 4)) Bool _).apply _ = timedCaptureCfg M clock (a.apply cfg)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [timedCaptureCfg, tapeBlocks, Action.apply, ho, bufferTape_append]
        · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [timedCaptureCfg, tapeBlocks, Action.apply, ho]
        · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
    · simp [timedCaptureCfg, tapeBlocks, Action.apply]

/-- Lockstep capture through the first halting transition. -/
private lemma timedCapture_run (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (t : ℕ)
    (h : ∀ s, s < t → (M.tm.runFrom cfg s).state ≠ none) :
    (timedCaptureTM M clock).tm.runFrom (timedCaptureCfg M clock cfg) t =
      timedCaptureCfg M clock (M.tm.runFrom cfg t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      timedCapture_step M clock _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Interpreter entry retains the halted canonizer's work and captured table.
Its clock lane becomes active again during interpretation. -/
private def timedCapturedCfg (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x :=
  { timedCaptureCfg M clock cfg with state := some (.inr timedInterpreter.q₀) }

/-- A halted source configuration transfers to the live interpreter entry state. -/
private lemma timedCapture_transfer (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (h : cfg.state = none) :
    (timedCaptureTM M clock).tm.step (timedCaptureCfg M clock cfg) =
      timedCapturedCfg M clock cfg := by
  unfold MultiTapeTM.step
  simp only [timedCaptureCfg, h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · rfl
  · funext i; exact add_zero _
  · rfl

/-- Every completed source computation reaches the interpreter with the table
captured in at most one extra transition.

**Proof sketch.** Choose the first source halting time. Lockstep capture holds
through that transition; one live administrative transition enters the interpreter.
Absorbing source halting identifies this first halted configuration with the one
at the supplied time bound, so all its fields (including parked input position)
are retained, not merely its completed output. -/
private lemma timedCapture_start (M : FinTM Bool) (clock : Fin M.k) (x : List Bool) (T : ℕ)
    (h : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    ∃ t, t ≤ T + 1 ∧
      (timedCaptureTM M clock).tm.runFrom ((timedCaptureTM M clock).tm.initCfg x) t =
        timedCapturedCfg M clock (M.tm.runFrom (M.tm.initCfg x) T) := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, h⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh h
  have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := Nat.find_spec hh
  have he : M.tm.runFrom (M.tm.initCfg x) T = M.tm.runFrom (M.tm.initCfg x) t := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs]
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', timedCapture_init,
    timedCapture_run M clock _ t (fun s hs => Nat.find_min hh hs),
    timedCapture_transfer M clock _ hs, he]


/-- A framed interpreter configuration shares precisely the retained clock lane. -/
private def timedFrame (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) : Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x :=
  ⟨cfg.state.map Sum.inr, cfg.inputPos,
    Fin.addCases (Function.update tapes clock (cfg.workTapes 4))
      (timedFive (fun i => cfg.workTapes (i.castAdd 2)) (cfg.workTapes 5)),
    Fin.addCases (Function.update heads clock (cfg.workTapePos 4))
      (timedFive (fun i => cfg.workTapePos (i.castAdd 2)) (cfg.workTapePos 5)), cfg.output⟩

/-- The active six reads of a frame are exactly the interpreter's reads. -/
private lemma timedFrame_reads (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) :
    timedSix (fun i => (timedFrame M clock cfg tapes heads).workTapeSymbols
      (Fin.natAdd M.k (i.castAdd 1)))
      ((timedFrame M clock cfg tapes heads).workTapeSymbols (clock.castAdd 5))
      ((timedFrame M clock cfg tapes heads).workTapeSymbols (Fin.natAdd M.k (4 : Fin 5))) =
    cfg.workTapeSymbols := by
  funext i
  fin_cases i <;> simp [timedFrame, timedSix, timedFive, Cfg.workTapeSymbols]

/-- A framed action changes only the six active lanes. Inactive canonizer data remains framed.

**Proof sketch.** Compare configuration fields. Split tape indices into the old
canonizer block and the five fresh lanes, then distinguish the retained clock
inside the old block. Each active read, write, and head move agrees with its
six-lane counterpart; the other old lanes are unchanged. -/
private lemma timedFrame_apply (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) (a : Action 6 Bool TimedControl) :
    (timedFrameAction M clock a).apply (timedFrame M clock cfg tapes heads) =
      timedFrame M clock (a.apply cfg) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j
        simp only [timedFrameAction, timedFrame, Action.apply, Fin.addCases_left, Function.update_self]
      · simp [timedFrameAction, timedFrame, Action.apply, hj, Function.update_of_ne]
    · intro j
      fin_cases j <;> simp [timedFrameAction, timedFrame, timedFive, Action.apply]
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j
        simp only [timedFrameAction, timedFrame, Action.apply, Fin.addCases_left, Function.update_self]
      · simp [timedFrameAction, timedFrame, Action.apply, hj, Function.update_of_ne]
    · intro j
      fin_cases j <;> simp [timedFrameAction, timedFrame, timedFive, Action.apply]

/-- Every interpreter transition lifts to the assembled machine, including final halting. -/
private lemma timedFrame_step (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) :
    (timedCaptureTM M clock).tm.step (timedFrame M clock cfg tapes heads) =
      timedFrame M clock (timedInterpreter.step cfg) tapes heads := by
  cases hs : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs,
      MultiTapeTM.step_of_halt (show (timedFrame M clock cfg tapes heads).state = none by simp [timedFrame, hs])]
  | some q =>
    have hstate : (timedFrame M clock cfg tapes heads).state = some (.inr q) := by simp [timedFrame, hs]
    conv_lhs => unfold MultiTapeTM.step; rw [hstate]; dsimp only [timedCaptureTM]
    have hi : (timedFrame M clock cfg tapes heads).inputSymbol = cfg.inputSymbol := rfl
    rw [timedFrame_reads, hi, timedFrame_apply]
    simp only [MultiTapeTM.step, hs]

/-- Full interpreter runs lift without changing the inactive frame. -/
private lemma timedFrame_run (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) (t : ℕ) :
    (timedCaptureTM M clock).tm.runFrom (timedFrame M clock cfg tapes heads) t =
      timedFrame M clock (timedInterpreter.runFrom cfg t) tapes heads := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih, timedFrame_step, MultiTapeTM.runFrom_succ_eq_step']

/-- Capturing a completed canonizer yields the initial six-lane interpreter frame.

**Proof sketch.** Compare the five configuration fields, splitting old and fresh
lanes. At the retained clock, use the parser completion identities for its contents
and head; the remaining lanes are the captured table and fresh blank tapes. -/
private lemma timedCaptured_frame (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (src : Cfg M.k Bool M.State x) (bs : List Bool)
    (ht : src.workTapes clock = bufferTape bs) (hh : src.workTapePos clock = bs.length) :
    timedCapturedCfg M clock src =
      timedFrame M clock (timedLift (timedCut_InterpreterInitial src.inputPos src.output) bs)
        src.workTapes src.workTapePos := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j; simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, ht]
      · simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hj]
    · intro j
      fin_cases j <;> simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift,
        timedSix, timedFive, timedCut_InterpreterInitial, universalFour, tapeBlocks] <;> rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j; simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hh]
      · simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hj]
    · intro j
      fin_cases j <;> simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift,
        timedSix, timedFive, timedCut_InterpreterInitial, universalFour, tapeBlocks] <;> rfl

/-- The complete timed universal machine has finite control and finitely many tapes. -/
private def timedUniversalTM (c : EffectiveMachineCode) : FinTM Bool :=
  timedCaptureTM (timedCanonTM c) (timedCanonClock c)

/-- The part of startup depending only on the code representation. -/
private def timedStartupBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
    2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16

/-- The canonical header endpoint is inside the complete serialization. -/
private lemma timed_header_bound (M : CodeTM) :
    2 * (Nat.bits M.numStates).length + 2 + M.tm.q₀.val + 1 ≤ M.serialize.length := by
  obtain ⟨records, hr⟩ := universal_serialization_header M
  rw [hr, universal_pair_length]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Full startup retains the binary deadline, canonizes `α` alone, and reaches
an initialized source checkpoint within `4|bits|` plus a code-only constant.

**Proof sketch.** Run the prefix-local canonizer and capture its serialization.
Transfer to the framed interpreter, replay the stopped initialization gadgets,
and identify the initialized source checkpoint using the nested-pair length.
Add the canonizer, transfer, and header-initialization costs. -/
private lemma timed_initialized (c : EffectiveMachineCode) (bs α x : List Bool) :
    ∃ (t : ℕ) (tapes : Fin (timedCanonTM c).k → ℤ → Option Bool)
      (heads : Fin (timedCanonTM c).k → ℤ),
      t ≤ 4 * bs.length + timedStartupBound c α ∧
      (timedUniversalTM c).tm.runFrom
        ((timedUniversalTM c).tm.initCfg (pairEncode (pairEncode bs α) x)) t =
      timedFrame (timedCanonTM c) (timedCanonClock c)
        (timedLift (universalSimulationCfg (c.decode α) (pairEncode bs α)
          ((c.decode α).tm.initCfg x)
          (2 * (Nat.bits (c.decode α).numStates).length + 2 + (c.decode α).tm.q₀.val + 1)) bs)
        tapes heads := by
  let T := 4 * bs.length + 3 * α.length + 8 + c.canonizerTime α.length
  let src := (timedCanonTM c).tm.runFrom
    ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x)) T
  have hc := timedCanon_complete c bs α x
  obtain ⟨t, ht, he⟩ := timedCapture_start (timedCanonTM c) (timedCanonClock c)
    (pairEncode (pairEncode bs α) x) T hc.1
  obtain ⟨records, hrecords⟩ := universal_serialization_header (c.decode α)
  have hinit := timedCut_Interpreter_initialize src.inputPos (c.decode α).serialize
    (Nat.bits (c.decode α).numStates) records (c.decode α).tm.q₀.val hrecords
  let d := (c.decode α).serialize.length + 2 * (Nat.bits (c.decode α).numStates).length +
    2 * (c.decode α).tm.q₀.val + 7
  have hi := timed_replay (timedCut_InterpreterInitial src.inputPos (c.decode α).serialize) bs d
    (by rw [hinit]; exact Option.some_ne_none _)
  rw [hinit] at hi
  refine ⟨t + d, src.workTapes, src.workTapePos, ?_, ?_⟩
  · dsimp only [timedStartupBound, d, T] at *; omega
  · change (timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ _ = _
    rw [MultiTapeTM.runFrom_add, he, timedCaptured_frame _ _ _ bs hc.2.2.2.1 hc.2.2.2.2]
    have ho : src.output = (c.decode α).serialize := hc.2.1
    rw [ho, timedFrame_run, hi]
    congr 2
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      have hp : src.inputPos.val = 4 * bs.length + 2 * α.length + 7 := hc.2.2.1
      simp only [universalEvalCfg, timedCut_InterpreterBase, universalSimulationCfg,
        universalInputPos, MultiTapeTM.initCfg, Fin.val_mk]
      change src.inputPos.val = 2 * (pairEncode bs α).length + 2 + 1
      have hlen := universal_pair_length bs α
      omega
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [universalEvalCfg, timedCut_InterpreterBase,
        universalSimulationCfg, universalFour, Nat.cast_add]
    · rfl

/-- Absorb clock-width work and fixed startup into a code-only quadratic coefficient.

**Proof sketch.** Write n = t + 1. Both the clock width and n are at most n squared.
Bound startup by (S + 4) n squared, and the interpreter coefficient by (B + 10) n;
its multiplication by n supplies the remaining quadratic term. -/
private lemma timed_cost_bound (S B t w s d : ℕ) (hw : w ≤ t)
    (hs : s ≤ 4 * w + S) (hd : d ≤ (B + 2 * w + 8) * (t + 1)) :
    s + d ≤ (S + B + 14) * (t + 1) ^ 2 := by
  have hn : 1 ≤ t + 1 := by omega
  have hsq : t + 1 ≤ (t + 1) ^ 2 := by
    calc t + 1 = (t + 1) * 1 := by omega
      _ ≤ (t + 1) * (t + 1) := Nat.mul_le_mul_left _ hn
      _ = (t + 1) ^ 2 := by ring
  have hs' : s ≤ (S + 4) * (t + 1) ^ 2 := by
    have hw' := Nat.mul_le_mul_left 4 (show w ≤ (t + 1) ^ 2 by omega)
    have hS := Nat.mul_le_mul_left S (show 1 ≤ (t + 1) ^ 2 by omega)
    calc s ≤ 4 * w + S := hs
      _ ≤ 4 * (t + 1) ^ 2 + S * (t + 1) ^ 2 := by omega
      _ = (S + 4) * (t + 1) ^ 2 := by ring
  have hb : B + 2 * w + 8 ≤ (B + 10) * (t + 1) := by
    have hB := Nat.mul_le_mul_left (B + 8) hn
    have hw' := Nat.mul_le_mul_left 2 (show w ≤ t + 1 by omega)
    calc B + 2 * w + 8 ≤ (B + 8) * (t + 1) + 2 * (t + 1) := by omega
      _ = (B + 10) * (t + 1) := by ring
  calc s + d ≤ (S + 4) * (t + 1) ^ 2 + (B + 2 * w + 8) * (t + 1) :=
      Nat.add_le_add hs' hd
    _ ≤ (S + 4) * (t + 1) ^ 2 + ((B + 10) * (t + 1)) * (t + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hb) _
    _ = (S + B + 14) * (t + 1) ^ 2 := by ring

/-- The assembled finite machine computes the exact bounded answer uniformly in the input.

**Proof sketch.** Join the initialized outer run to the bounded inner run, lifting
the latter through the inactive canonizer frame. Its halted state and exact answer
give a completed computation; the clock-width estimate and cost ledger enlarge
the time bound to the stated code-dependent quadratic budget. -/
private lemma timed_computes (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) :
    (timedUniversalTM c).ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t)
      ((timedStartupBound c α + universalBlockBound c α + 14) * (t + 1) ^ 2) := by
  obtain ⟨s, tapes, heads, hs, hstart⟩ := timed_initialized c (Nat.bits t) α x
  obtain ⟨d, hd, hfinish⟩ := timed_interpret_finishes (c.decode α) (pairEncode (Nat.bits t) α) t
    ((c.decode α).tm.initCfg x)
    (2 * (Nat.bits (c.decode α).numStates).length + 2 + (c.decode α).tm.q₀.val + 1)
    (Nat.bits t) (timed_header_bound (c.decode α)) (timedValue_bits t)
  have htime : s + d ≤
      (timedStartupBound c α + universalBlockBound c α + 14) * (t + 1) ^ 2 := by
    apply timed_cost_bound _ _ _ _ _ _ (timed_bits_length t) hs
    simpa only [universalBlockBound, MultiTapeTM.initCfg, Cfg.init, List.length_nil,
      Nat.mul_zero, Nat.add_zero] using hd
  have hcompute : (timedUniversalTM c).ComputesInTime
      (pairEncode (pairEncode (Nat.bits t) α) x)
      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t) (s + d) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    change ((timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ d).state = none ∧
      ((timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ d).output = _
    rw [timedFrame_run]
    exact ⟨by simp only [timedFrame, hfinish.1, Option.map_none], hfinish.2⟩
  exact hcompute.mono htime

/-- **The time-bounded universal machine** [AB09, §1.4.1, "Universal TM with time
bound"]: a single machine that, given `⟨⟨⌞t⌟, α⟩, x⟩` (clock and code first, input
last), simulates the machine `α` denotes on `x` for at most `t` steps, reporting
success (`true :: output`) or timeout (`[false]`).

**Proof sketch.** Extend the simulation of `Turing.universal` with a binary
countdown clock on a further work tape, initialized from `⌞t⌟ = Nat.bits t` (parsed
from the doubled-bit region; cost `O(t + 1)`, within budget). Each simulated step
costs an additional `O((Nat.bits t).length + 1)` for the decrement, whence the
quadratic budget; `M`'s emissions are buffered on a work tape rather than emitted
(their total length is at most `t`, by `Turing.MultiTapeTM.output_length_le`).
Halting is checked after each simulated transition, **including the `t`-th**: if the
simulated machine has halted by the time the clock expires — deadline included —
`U` emits `true` and flushes the buffer; otherwise it emits `false`. At `t = 0` no
initialized machine has halted (`Turing.FinTM.not_computesInTime_zero`), and the
timeout branch applies (audit finding 6). The two cases below are exhaustive:
either some output witnesses halting within `t`, or every output fails to. -/
theorem timed_universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output) (C * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false] (C * (t + 1) ^ 2)) := by
  refine ⟨timedUniversalTM c, fun α =>
    ⟨timedStartupBound c α + universalBlockBound c α + 14, ?_⟩⟩
  intro x t
  have hu := timed_computes c α x t
  constructor
  · intro output hsource
    obtain ⟨hh, ho⟩ := (computesInTime_iff _ _ _ _).mp hsource
    simpa only [timedAnswer, hh, if_pos, ho] using hu
  · intro hsource
    have hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
      intro hhalt
      exact hsource _ ((computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩)
    simpa only [timedAnswer, if_neg hh] using hu

end Turing
