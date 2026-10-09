/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the bounded loop

The control centerpiece of the machine-construction library
(`machine-library-design.md` §5, L; loop redesign §9b, configuration
export §9c): a bounded loop with tape-resident round state, specified at
four granularities.

* `Turing.loop_run` is the **summation lemma**: given a family of round
  configurations with an accept-or-advance contract, the run from round 0
  halts within the summed budget with the loop's single verdict bit. It is
  the generic form of the Chapter-2 enumerator's proved private
  `enumLoop_run`, whose proof is the harvest template. (Round-1 audit:
  Pass.)
* `Turing.FinTM.exists_loopCfgTM` is the **configuration-level
  combinator** (added per round-2 finding 1): its conclusion exposes the
  host machine's round-configuration family, bounded startup, per-round
  accept-or-advance segments, and halted exhaustion terminal — the shape
  the frozen Chapter-2 `enumMachine_contracts` consumes, which the
  final-answer conclusion below provably cannot supply (the round-2 audit
  exhibits a final-answer-correct machine violating every per-round
  bound).
* `Turing.FinTM.exists_loopTM` is the **decision form**: one finite
  machine answers the Boolean "some orbit point accepts". At fill time it
  is a corollary of the configuration form through an
  already-halted-terminal summation lemma (the shape of the enumerator's
  `enumLoop_run`; the frozen `Turing.loop_run` requires an empty-output
  terminal, which the exported family's `[false]` terminal deliberately
  is not — round-3 finding R3-1), with startup absorbed by monotonicity.
* `Turing.FinTM.exists_loopFindTM` is the **result-bearing form**: the
  accepting round delivers a payload, and the machine outputs the first
  accepting orbit point's payload (`[]` on exhaustion) — the form the
  split search (catalog P10) and the reduction emitters instantiate.

**Status: proved; the statements are the round-2 repair.** The round-1 audit
(`audits/ch1-infra-findings.md`) refuted the previous combinator: finding
1 (blocker) exhibited a zero-step "advance" (`stepF = id`, `t = 0`) that
made the hypotheses vacuously satisfiable and the conclusion contradict
the input-head information bound; finding 2 (major) showed the round
hypothesis quantified over *all* state words at the budget `T |x|`, which
no body can satisfy for width-growing rounds and which excludes the
intended customers. This revision repairs both:

* every round takes **positive time** (`0 < t`), and
* rounds are required only on **admissible** state words, via an
  input-indexed invariant `Inv x s` that the startup word satisfies
  (`hInv0`) and the advance step preserves (`hInvStep`); customers choose
  `Inv` to pin the state-word width to the input (instantiation tables in
  `machine-library-design.md` §9b).

`stepF`, `acceptF`, and the payload take the input as an explicit first
argument (finding 2's repair guidance): the enumerator's acceptance runs
the verifier on `x ++ s`.

## The round discipline

Round state is one word on the body's tape 0; every other body tape is
scratch, blank at both seam ends of a round (body-restores-scratch, frozen
design decision 9.2). A round either **accepts** — halts with its declared
output, nothing emitted earlier — or **advances** to the seam carrying the
stepped state word, in positive time, and in both cases without re-entering
the anchor state strictly between the seam and that endpoint (the host
detects round boundaries as entries into the embedded anchor; the clause is
load-bearing, round-1 attestation 7 and finding 1).

**Countdown discipline** (corrected per round-1 finding 4): the counter is
loaded from the fuel machine's output `Nat.bits (R |x|)`; the **initial
anchor entry is free**, and debiting starts with the second entry, so the
rounds completed before borrow-overflow are exactly `0, …, R |x|` — at
`R |x| = 0` (`Nat.bits 0 = []`) the single orbit point `s0 x` is still
checked before the empty counter overflows. Decrement cost is amortized
(the borrow lengths over a full countdown telescope to `O(R)`, and the
counter width is at most `T |x|` by `Turing.MultiTapeTM.output_length_le`
on the fuel machine), which is what keeps the stated budget at
`(T + 1) · (R + 2)` with no logarithmic factor — the round-1 audit
validated this budget strategy (finding 4, second half).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the clocked-loop discipline is
  the folklore engine of the enumeration and diagonalization arguments,
  §2.1 / §3.1–3.2.)

**Fill checkpoint (batch L).** `loop_run` is proved. The three finite-machine
exports are derived from the single admitted private `loopHost_contracts`.
The concrete controller, source-body simulation, fixed-width counter,
input rewind, capture instances, payload replay, and both terminal summation
lemmas are supplied below. Controller-level phase assembly and its uniform
budget remain the continuation frontier; this file is not an admission-free
completion of the loop combinators.

**Fill completion (batch L2).** The historical checkpoint above is now
closed: the actual fuel, startup, body-return, counter, and payload phases
are proved and assembled in `loopHost_contracts`, with uniform coefficient
`loopHost_bound = 10`. The canonical seams retain the completed fuel residue
and fixed-width debit iterates. Underflow and its final emission are inside
the last rejecting segment; an accepting last candidate has an arbitrary
unreachable rejection terminal. The entire file has no admissions, including
the capture helpers now that batch W's `capture_run` proof is integrated.
-/

namespace Turing

/-- Round state on tape 0, scratch blank: the standard word assignment for
a loop body's seam configurations. -/
def stateWord (k : ℕ) (s : List Bool) : Fin k → List Bool :=
  fun i => if (i : ℕ) = 0 then s else []

/-- **The loop summation lemma** (spec, fill pending — the generic form of
the enumerator's proved `enumLoop_run`, which is the harvest template;
round-1 audit verdict: Pass, including `N = 0`).
Given round configurations `cfg 0, …, cfg N` of one machine with empty
outputs, such that each round `j < N` within budget `B` either halts with
the verdict `[true]` (when `accept j`) or reaches `cfg (j+1)`, and the
exhaustion round `cfg N` halts with `[false]` within `B`: the run from
`cfg 0` halts within `(N + 1) · B` steps with the single verdict bit
`(List.range N).any accept`.

**Proof sketch.** Induction on the first accepting round (or `N` when none
accepts), composing the advance segments with
`Turing.MultiTapeTM.runFrom_add` and absorbing halted tails with
`Turing.MultiTapeTM.runFrom_of_halt`; empty round outputs make the final
output exactly the one emitted verdict. -/
theorem loop_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hout : ∀ j ≤ N, (cfg j).output = [])
    (hend : ∃ t ≤ B, (tm.runFrom (cfg N) t).state = none ∧
      (tm.runFrom (cfg N) t).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ (N + 1) * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  induction N generalizing cfg accept with
  | zero => simpa using hend
  | succ N ih =>
    obtain ⟨t, ht, hc⟩ := hround 0 (by omega)
    have hany : (List.range (N + 1)).any accept =
        (accept 0 || (List.range N).any (fun j => accept (j + 1))) := by
      simp [List.range_succ_eq_map, List.any_map, Function.comp_def]
    by_cases hb : accept 0 = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · exact Nat.le_mul_of_pos_left B (by omega)
      · simpa [hany, hb] using hc.2
    · simp only [hb] at hc
      -- Shift the round family by one, retaining the same terminal segment.
      obtain ⟨s, hs, hhalt, hout'⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1))
        (fun j hj => hout (j + 1) (by omega)) hend
        (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [hany, hb] using hout'

end Turing

namespace Turing.FinTM

/-- A live endpoint rules out a halt anywhere in its preceding run. -/
private lemma loop_live_prefix {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom cfg t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom cfg u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom cfg t = tm.runFrom cfg u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- Replace a possibly padded halting-time witness by its first halt,
retaining the entire endpoint configuration.
**Proof sketch.** Choose the least halting time. Minimality supplies the
strict liveness guard; the absorbing-halt law identifies its endpoint
with the original, possibly later, witness. -/
private lemma loop_first_halt {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧
      (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      (tm.runFrom cfg u).state = none ∧ tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, ?_, hu, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · intro v hv
    exact Nat.find_min h hv
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hu]

/-- The declared invariant holds at each orbit word, including unreachable
rounds after an earlier acceptance. -/
private lemma loop_orbit_inv (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool) (s0 : List Bool → List Bool)
    (hInv0 : ∀ x, Inv x (s0 x))
    (hInvStep : ∀ x s, Inv x s → Inv x (stepF x s)) (x : List Bool) (i : ℕ) :
    Inv x ((stepF x)^[i] (s0 x)) := by
  induction i with
  | zero => exact hInv0 x
  | succ i ih => rw [Function.iterate_succ_apply']; exact hInvStep x _ ih

/-- The fuel run bounds the fixed counter width on each actual input. -/
private lemma loop_fuel_width (F : FinTM Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    (Nat.bits (R x.length)).length ≤ T x.length := by
  obtain ⟨s, hhalt, hout, hspace⟩ := hF x
  simpa only [hout] using F.tm.output_length_le x (T x.length)

/-- One native input-head move increases its position by at most one. -/
private lemma loop_input_move_le {n : ℕ} (p : Fin (n + 2)) (m : SignType) :
    (moveInputPos p m).val ≤ p.val + 1 := by
  cases m with
  | zero => simp
  | neg => rw [moveInputPos_neg_val]; omega
  | pos =>
    by_cases hp : p.val = n + 1
    · have he : p = ⟨n + 1, by omega⟩ := Fin.ext hp
      rw [he]
      simp only [SignType.pos_eq_one, moveInputPos_rightBoundary]
      omega
    · rw [moveInputPos_pos_of_ne_right p hp]

/-- Input displacement is bounded by elapsed time, even for sublinear budgets. -/
private lemma loop_input_run_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).inputPos.val ≤ c.inputPos.val + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
    cases hd : d.state with
    | none => simp [MultiTapeTM.step, hd]
    | some q =>
      simpa only [MultiTapeTM.step, hd, Action.apply] using
        loop_input_move_le d.inputPos (tm.tr q d.inputSymbol d.workTapeSymbols).inputTape
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- A run appends at most one output bit per step, from any seam configuration. -/
private lemma loop_output_length_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).output.length ≤ c.output.length + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).output.length ≤ d.output.length + 1 := by
    rw [MultiTapeTM.step_output, List.length_append]
    cases tm.outputSymbol d <;> simp
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- The input rewind has a bound in its starting position, so it can be
charged to the preceding run without scanning the entire input.
**Proof sketch.** Take the mandatory first left move and apply the proved
`rewind_scan` at the resulting position. Its exact scan time is position
plus one; the first left move never increases position. -/
private lemma loop_rewind_bounded {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t ≤ cfg.inputPos.val + 2,
      tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_, ?_⟩
  · simp only [c, hstep, moveInputPos_neg_val]
    omega
  · rw [MultiTapeTM.runFrom_add]
    have hfirst : tm.runFrom cfg 1 = c := rfl
    rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
    simp only [c, hstep]

/-- Fixed-width little-endian decrement and its success flag. Underflow
sets the existing cells to true and returns false, without extending the word. -/
private def loopDebit : List Bool → List Bool × Bool
  | [] => ([], false)
  | true :: bs => (false :: bs, true)
  | false :: bs => (true :: (loopDebit bs).1, (loopDebit bs).2)

/-- Number of low zero bits traversed by a borrow. -/
private def loopBorrowPos : List Bool → ℕ
  | false :: bs => loopBorrowPos bs + 1
  | _ => 0

/-- The borrow scan cannot cross more cells than the fixed width. -/
private lemma loopBorrowPos_le (u : List Bool) : loopBorrowPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [loopBorrowPos, List.length_cons] <;> omega

/-- Both successful decrements and underflow preserve the counter width. -/
private lemma loopDebit_length (u : List Bool) : (loopDebit u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [loopDebit, ih]

/-- Little-endian counter value; high zero cells contribute nothing. -/
private def loopValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * loopValue bs + if b then 1 else 0

/-- The fuel machine's binary word has its declared numerical value. -/
private lemma loopValue_bits (n : ℕ) : loopValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [loopValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [loopValue, ih, Nat.bit_val]

/-- A successful debit reduces value by one; underflow occurs only at zero.
**Proof sketch.** A low one is cleared immediately. A low zero becomes one
while the inductive debit reduces the higher part; doubling that equation
gives the successor equation for the full word. -/
private lemma loopDebit_value (u : List Bool) :
    if (loopDebit u).2 then loopValue (loopDebit u).1 + 1 = loopValue u
    else loopValue u = 0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | true => simp [loopDebit, loopValue]
    | false =>
      cases h : (loopDebit u).2 <;>
        simp only [loopDebit, h, Bool.false_eq_true, ↓reduceIte,
          loopValue, Nat.add_zero] at ih ⊢ <;> omega

/-- The borrow returns success exactly for positive counter values. -/
private lemma loopDebit_success (u : List Bool) :
    (loopDebit u).2 = true ↔ 0 < loopValue u := by
  have h := loopDebit_value u
  cases hb : (loopDebit u).2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    simp [h]
  · simp only [hb, ↓reduceIte] at h
    simp only [true_iff]
    omega

/-- Iterating debit retains the original fixed width at every index. -/
private lemma loopDebit_iterate_length (u : List Bool) (i : ℕ) :
    ((fun w => (loopDebit w).1)^[i] u).length = u.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', loopDebit_length, ih]

/-- Before exhaustion, the counter after `i` debits has value `R-i`.
**Proof sketch.** Start from the fuel word's value. Before the last debit
the induction hypothesis gives a positive value, so the success equation
reduces it by exactly one. No representation is shortened. -/
private lemma loopDebit_iterate_value (R i : ℕ) (hi : i ≤ R) :
    loopValue ((fun w => (loopDebit w).1)^[i] R.bits) = R - i := by
  induction i with
  | zero => simpa using loopValue_bits R
  | succ i ih =>
    have hv := ih (by omega)
    have hs : (loopDebit ((fun w => (loopDebit w).1)^[i] R.bits)).2 = true :=
      (loopDebit_success _).2 (by omega)
    have hd := loopDebit_value ((fun w => (loopDebit w).1)^[i] R.bits)
    simp only [hs, ↓reduceIte] at hd
    rw [Function.iterate_succ_apply']
    omega

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma loopBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma loopBuffer_write (pre bs : List Bool) (old new : Bool) :
    Function.update (bufferTape (pre ++ old :: bs)) (pre.length : ℤ) (some new) =
      bufferTape (pre ++ new :: bs) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold bufferTape
    by_cases hn : 0 ≤ z
    · simp only [if_pos hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
    · simp only [if_neg hn]

/-- Stop the body at the next anchor entry, distinguishing that return from
a genuine source halt on an extra one-cell flag tape. A true release bit
forces one source action, even at the anchor; every source successor clears
the release bit. The body's full output is retained for subsequent capture. -/
private def loopBodyTM (body : FinTM Bool) (anchor : body.State) : FinTM Bool where
  k := body.k + 1
  State := body.State × Bool
  tm :=
    { q₀ := (body.tm.q₀, false)
      tr := fun q inp work =>
        if q.1 = anchor ∧ q.2 = false then
          { inputTape := 0
            workTapes := fun i =>
              if (i : ℕ) < body.k then (none, 0) else (some (some false), 0)
            output := none
            state := none }
        else
          let a := body.tm.tr q.1 inp (fun i => work i.castSucc)
          { inputTape := a.inputTape
            workTapes := fun i =>
              if h : (i : ℕ) < body.k then a.workTapes ⟨i, h⟩
              else (if a.state = none then some (some true) else none, 0)
            output := a.output
            state := a.state.map (fun s => (s, false)) } }

/-- Embed a source configuration with its release bit and the one-cell
halt-kind flag. The flag head stays at the origin throughout a body call. -/
private def loopBodyCfg (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool) :
    Cfg (loopBodyTM body anchor).k Bool (loopBodyTM body anchor).State x where
  state := c.state.map (fun s => (s, release))
  inputPos := c.inputPos
  workTapes := fun i => if h : (i : ℕ) < body.k then c.workTapes ⟨i, h⟩
    else fun z => if z = 0 then flag else none
  workTapePos := fun i => if h : (i : ℕ) < body.k then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- At an unreleased anchor the stop wrapper takes one silent step and
records rejection, without changing the body's configuration data. -/
private lemma loopBody_stop (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (hc : c.state = some anchor) (flag : Option Bool) :
    (loopBodyTM body anchor).tm.step (loopBodyCfg body anchor c false flag) =
      loopBodyCfg body anchor {c with state := none} false (some false) := by
  unfold MultiTapeTM.step
  simp only [loopBodyCfg, hc, Option.map_some, loopBodyTM, and_self, ↓reduceIte]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hi : (i : ℕ) < body.k
    · simp [Action.apply, hi]
    · simp only [Action.apply, hi, ↓reduceIte]
      by_cases hz : z = 0 <;> simp [hz, hi, Function.update]
  · funext i
    by_cases hi : (i : ℕ) < body.k <;> simp [Action.apply, hi]
  · simp [Action.apply]

/-- Away from an unreleased anchor, the wrapper executes exactly one body
action and records a true flag precisely on a genuine halting transition. -/
private lemma loopBody_step (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (q : body.State) (release : Bool)
    (flag : Option Bool) (hc : c.state = some q)
    (hgo : ¬(q = anchor ∧ release = false)) :
    (loopBodyTM body anchor).tm.step (loopBodyCfg body anchor c release flag) =
      loopBodyCfg body anchor (body.tm.step c) false
        (if (body.tm.step c).state = none then some true else flag) := by
  let a := body.tm.tr q c.inputSymbol c.workTapeSymbols
  have hb : body.tm.step c = a.apply c := by simp only [MultiTapeTM.step, hc, a]
  rw [hb]
  unfold MultiTapeTM.step
  simp only [loopBodyCfg, hc, Option.map_some, loopBodyTM, hgo, ↓reduceIte]
  have hr : (fun i : Fin body.k =>
      (loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc) =
        c.workTapeSymbols := by
    funext i
    simp [loopBodyCfg, Cfg.workTapeSymbols, i.isLt]
  change (let a' : Action body.k Bool body.State :=
            body.tm.tr q c.inputSymbol (fun i : Fin body.k =>
              (loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc);
    ({
      inputTape := a'.inputTape
      workTapes := fun i => if h : (i : ℕ) < body.k then a'.workTapes ⟨i, h⟩
        else (if a'.state = none then some (some true) else none, 0)
      output := a'.output
      state := a'.state.map (fun s => (s, false)) } :
        Action (body.k + 1) Bool (body.State × Bool))).apply _ = _
  rw [hr]
  dsimp only
  dsimp only [a] at *
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : (i : ℕ) < body.k
    · simp [Action.apply, hi]
    · by_cases ha : (body.tm.tr q c.inputSymbol c.workTapeSymbols).state = none
      · simp only [Action.apply, hi, ↓reduceDIte, ha, ↓reduceIte]
        by_cases hz : z = 0 <;> simp [hz, hi, Function.update]
      · simp [Action.apply, hi, ha]
  · funext i
    by_cases hi : (i : ℕ) < body.k <;> simp [Action.apply, hi]

/-- Up to the first halt or anchor return, the stop wrapper simulates the
body exactly. The release flag is consumed by the first action.
**Proof sketch.** Induct on elapsed time. Strict liveness supplies a source
state; the no-anchor condition, except for the released first action,
enables the one-step lemma. Its flag update records a halting emission's
transition without discarding that emission. -/
private lemma loopBody_run (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none) t =
      loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
        (if (body.tm.runFrom c t).state = none then some true else none) := by
  induction t with
  | zero => simp [hc]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    rw [ih (fun u hu => hlive u (by omega)) (fun u hu => hanchor u (by omega))]
    have ht := hlive t (by omega)
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp ht
    have hgo : ¬(q = anchor ∧ (if t = 0 then release else false) = false) := by
      rcases hanchor t (by omega) with ⟨hz, hr⟩ | hn
      · simp [hz, hr]
      · rintro ⟨rfl, _⟩
        exact hn hq
    rw [if_neg ht, loopBody_step body anchor _ q _ none hq hgo]
    simp only [Nat.succ_ne_zero, ↓reduceIte, MultiTapeTM.runFrom_succ_eq_step']

/-- Disjoint finite control for fuel, body calls, and fourteen controller phases. -/
private abbrev LoopHostState (body F : FinTM Bool) :=
  F.State ⊕ ((Bool × (body.State × Bool)) ⊕ Fin 14)

/-- Relocate the fuel machine past the untouched body, flag, and counter tapes. -/
private def loopFuelSource (body F : FinTM Bool) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool F.State where
  q₀ := F.tm.q₀
  tr := fun q inp work =>
    rightAction (body.k + 1) id (rightAction 1 id
      (F.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1) (Fin.natAdd 1 i))))

/-- Extend the stopped body with a preserved counter and the fuel-phase residue. -/
private def loopBodySource (body F : FinTM Bool) (anchor : body.State) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) where
  q₀ := (body.tm.q₀, false)
  tr := fun q inp work => leftAction (1 + F.k) id
    ((loopBodyTM body anchor).tm.tr q inp fun i => work (Fin.castAdd (1 + F.k) i))

/-- A controller action touches only the flag, counter, and capture tapes. -/
private def loopControlAction (body F : FinTM Bool) (inp : SignType)
    (flag : Option (Option Bool)) (counter payload : Option (Option Bool) × SignType)
    (out : Option Bool) (next : Option (LoopHostState body F)) :
    Action (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) where
  inputTape := inp
  workTapes := fun i =>
    if (i : ℕ) = body.k then (flag, 0)
    else if (i : ℕ) = body.k + 1 then counter
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then payload
    else (none, 0)
  output := out
  state := next

/-- Concrete loop controller, with fixed-verdict and payload-replay modes.
Fuel is captured, rewound, copied into the fixed-width counter while the
capture tape is cleared, and both heads are rewound together. Two further
phases rewind the native input before starting the body. Body startup and
active rounds have disjoint return states; only an active rejection debits.
The release bit forces one body action before another anchor is recognized.

Control phases: 0/1 fuel rewind; 2 counter copy; 3 counter/capture rewind;
4/5 input rewind; 6 startup return; 7 round return; 8 borrow; 9/10 successful
and underflow rewinds; 11 exhaustion; 12/13 payload rewind and replay.
The fuel work tapes are never cleared or reused after the fuel phase. -/
private def loopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool where
  k := body.k + 1 + (1 + F.k) + 1
  State := LoopHostState body F
  tm :=
    { q₀ := .inl F.tm.q₀
      tr := fun q inp work =>
        let ctrl (j : Fin 14) : LoopHostState body F := .inr (.inr j)
        let call (startup : Bool) (s : body.State × Bool) : LoopHostState body F :=
          .inr (.inl (startup, s))
        let flag : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k, by omega⟩
        let counter : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k + 1, by omega⟩
        let payload := Fin.last (body.k + 1 + (1 + F.k))
        let act := loopControlAction body F
        match q with
        | .inl s => captureAction Sum.inl (ctrl 0)
            ((loopFuelSource body F).tr s inp fun i => work i.castSucc)
        | .inr (.inl (startup, s)) =>
            captureAction (call startup) (ctrl (if startup then 6 else 7))
              ((loopBodySource body F anchor).tr s inp fun i => work i.castSucc)
        | .inr (.inr phase) =>
            if phase = 0 then act 0 none (none, 0) (none, .neg) none (some (ctrl 1))
            else if phase = 1 then
              match work payload with
              | some _ => act 0 none (none, 0) (none, .neg) none (some (ctrl 1))
              | none => act 0 none (none, 0) (none, .pos) none (some (ctrl 2))
            else if phase = 2 then
              match work payload with
              | some b => act 0 none (some (some b), .pos) (some none, .pos) none
                  (some (ctrl 2))
              | none => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))
            else if phase = 3 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))
              | none => act 0 none (none, .pos) (none, .pos) none (some (ctrl 4))
            else if phase = 4 then act .neg none (none, 0) (none, 0) none (some (ctrl 5))
            else if phase = 5 then
              match inp with
              | some _ => act .neg none (none, 0) (none, 0) none (some (ctrl 5))
              | none => act .pos none (none, 0) (none, 0) none
                  (some (call true (body.tm.q₀, false)))
            else if phase = 6 then act 0 (some none) (none, 0) (none, 0) none
              (some (call false (anchor, true)))
            else if phase = 7 then
              if work flag = some true then
                if findMode then act 0 none (none, 0) (none, .neg) none (some (ctrl 12))
                else act 0 none (none, 0) (none, 0) (some true) none
              else act 0 (some none) (none, 0) (none, 0) none (some (ctrl 8))
            else if phase = 8 then
              match work counter with
              | some false => act 0 none (some (some true), .pos) (none, 0) none
                  (some (ctrl 8))
              | some true => act 0 none (some (some false), .neg) (none, 0) none
                  (some (ctrl 9))
              | none => act 0 none (none, .neg) (none, 0) none (some (ctrl 10))
            else if phase = 9 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, 0) none (some (ctrl 9))
              | none => act 0 none (none, .pos) (none, 0) none
                  (some (call false (anchor, true)))
            else if phase = 10 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, 0) none (some (ctrl 10))
              | none => act 0 none (none, .pos) (none, 0) none (some (ctrl 11))
            else if phase = 11 then
              act 0 none (none, 0) (none, 0) (if findMode then none else some false) none
            else if phase = 12 then
              match work payload with
              | some _ => act 0 none (none, 0) (none, .neg) none (some (ctrl 12))
              | none => act 0 none (none, 0) (none, .pos) none (some (ctrl 13))
            else
              match work payload with
              | some b => act 0 none (none, 0) (none, .pos) (some b) (some (ctrl 13))
              | none => act 0 none (none, 0) (none, 0) none none }

/-- The concrete host's body states agree with W1 on the entire source table;
startup and active calls return to distinct controller phases. -/
private lemma loopHost_body_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) (t : ℕ)
    (hlive : ∀ u < t, ¬((loopBodySource body F anchor).runFrom c u).Halted) :
    (loopHost body F anchor findMode).tm.runFrom
        (captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
          (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] [] c) t =
      captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
        (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
        ((loopBodySource body F anchor).runFrom c t) := by
  exact capture_run (loopBodySource body F anchor) (loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel states capture all fuel emissions directly in the concrete host. -/
private lemma loopHost_fuel_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool F.State x) (t : ℕ)
    (hlive : ∀ u < t, ¬((loopFuelSource body F).runFrom c u).Halted) :
    (loopHost body F anchor findMode).tm.runFrom
        (captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] c) t =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).runFrom c t) := by
  exact capture_run (loopFuelSource body F) (loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel capture starts at the host's genuine blank initial configuration. -/
private lemma loopHost_init (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) :
    (loopHost body F anchor findMode).tm.initCfg x =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).initCfg x) := by
  rw [initCfg_ofWords, initCfg_ofWords]
  simp [Cfg.ofWords, captureCfg, loopHost, loopFuelSource]

/-- With no track operations, a controller action is the standard input-only action. -/
private lemma loopControl_idle (body F : FinTM Bool) (inp : SignType)
    (next : Option (LoopHostState body F)) :
    loopControlAction body F inp none (none, 0) (none, 0) none next =
      controlAction inp next := by
  simp [loopControlAction, controlAction]

/-- Host phases 4 and 5 rewind the native input in bounded time, retaining
all tapes, heads, and output, then dispatch to genuine body startup. -/
private lemma loopHost_input_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (cfg : Cfg (loopHost body F anchor findMode).k Bool (loopHost body F anchor findMode).State x)
    (hs : cfg.state = some (.inr (.inr (4 : Fin 14)))) :
    ∃ t ≤ cfg.inputPos.val + 2,
      (loopHost body F anchor findMode).tm.runFrom cfg t =
        {cfg with state := some (.inr (.inl (true, (body.tm.q₀, false)))), inputPos := 1} := by
  apply loop_rewind_bounded (loopHost body F anchor findMode).tm
    (.inr (.inr 4)) (.inr (.inr 5)) (.some (.inr (.inl (true, (body.tm.q₀, false)))))
    ?_ ?_ cfg hs
  · intro inp work
    exact loopControl_idle body F .neg _
  · intro inp work
    cases inp <;> exact loopControl_idle body F _ _

/-- A controller configuration with arbitrary preserved body/fuel residue.
Only the flag, counter, and capture tracks are replaced by the parameters. -/
private def loopFrame (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x where
  state := q
  inputPos := p
  workTapes := fun i =>
    if (i : ℕ) = body.k then flag
    else if (i : ℕ) = body.k + 1 then counter
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then payload
    else base.workTapes i
  workTapePos := fun i =>
    if (i : ℕ) = body.k then 0
    else if (i : ℕ) = body.k + 1 then ch
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then ph
    else base.workTapePos i
  output := out

/-- Optional writes update exactly their current cell. -/
private def loopWrite (tape : ℤ → Option Bool) (head : ℤ) :
    Option (Option Bool) → ℤ → Option Bool
  | none => tape
  | some symbol => Function.update tape head symbol

/-- Controller actions preserve the inactive frame and perform precisely
the three declared track operations. -/
private lemma loopControl_apply (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool)
    (inp : SignType) (fw : Option (Option Bool))
    (ca pa : Option (Option Bool) × SignType) (emit : Option Bool)
    (next : Option (LoopHostState body F)) :
    (loopControlAction body F inp fw ca pa emit next).apply
        (loopFrame body F base q p flag counter payload ch ph out) =
      loopFrame body F base next (moveInputPos p inp)
        (loopWrite flag 0 fw) (loopWrite counter ch ca.1) (loopWrite payload ph pa.1)
        (ch + ca.2) (ph + pa.2) (out ++ emit.toList) := by
  have hcf : body.k + 1 ≠ body.k := by omega
  have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  have hpc : body.k + 1 + (1 + F.k) ≠ body.k + 1 := by omega
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp only [Action.apply, loopControlAction, loopFrame, hf, ↓reduceIte]
      cases fw <;> rfl
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp only [Action.apply, loopControlAction, loopFrame, hc, hcf, ↓reduceIte]
        cases ca.1 <;> rfl
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · simp only [Action.apply, loopControlAction, loopFrame, hp, hpf, hpc, ↓reduceIte]
          cases pa.1 <;> rfl
        · simp [Action.apply, loopControlAction, loopFrame, hf, hc, hp]
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp [Action.apply, loopControlAction, loopFrame, hf]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [Action.apply, loopControlAction, loopFrame, hc]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k) <;>
          simp [Action.apply, loopControlAction, loopFrame, hf, hc, hp, hpf]

/-- One-tape payload replay: emit each stored bit, then halt on the right blank. -/
private def loopReplayTM : FinTM Bool where
  k := 1
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ _ work => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some ()⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Replay configuration with arbitrary input position and output prefix. -/
private def loopReplayCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Unit) (z : ℤ) (word out : List Bool) : Cfg 1 Bool Unit x :=
  ⟨q, p, fun _ => bufferTape word, fun _ => z, out⟩

/-- A replay step emits the current bit without modifying the captured word;
at the right blank it halts without an additional bit. -/
private lemma loopReplay_step (x : List Bool) (p : Fin (x.length + 2))
    (pre rest out : List Bool) :
    loopReplayTM.tm.step (loopReplayCfg x p (some ()) pre.length (pre ++ rest) out) =
      match rest with
      | [] => loopReplayCfg x p none pre.length pre out
      | b :: bs => loopReplayCfg x p (some ()) (pre.length + 1) (pre ++ b :: bs) (out ++ [b]) := by
  unfold MultiTapeTM.step
  change (loopReplayTM.tm.tr () _ _).apply _ = _
  simp only [loopReplayTM, loopReplayCfg, Cfg.workTapeSymbols, loopBuffer_read]
  cases rest with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ ?_
    · simp
    · funext i; simp [Action.apply]
    · simp [Action.apply]
  | cons b rest =>
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]

/-- Replay emits exactly the remaining payload in its length plus one steps,
including an empty payload.
**Proof sketch.** Induct on the unprocessed suffix. The step lemma emits
one bit and moves the frontier; the empty suffix supplies the final blank
test. Concatenation associativity preserves the exact output order. -/
private lemma loopReplay_run (x : List Bool) (p : Fin (x.length + 2))
    (rest : List Bool) : ∀ pre out : List Bool,
    loopReplayTM.tm.runFrom (loopReplayCfg x p (some ()) pre.length (pre ++ rest) out)
        (rest.length + 1) =
      loopReplayCfg x p none (pre ++ rest).length (pre ++ rest) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out
    simpa [MultiTapeTM.runFrom_succ_eq_step] using loopReplay_step x p pre [] out
  | cons b rest ih =>
    intro pre out
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step, loopReplay_step]
    simpa [List.append_assoc, List.length_append, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using ih (pre ++ [b]) (out ++ [b])

/-- A payload-only controller action is the right-block action extension. -/
private lemma loopControl_payload (body F : FinTM Bool) (d : SignType)
    (out : Option Bool) (next : Option (LoopHostState body F)) :
    loopControlAction body F 0 none (none, 0) (none, d) out next =
      rightAction (body.k + 1 + (1 + F.k)) id
        (⟨0, fun _ : Fin 1 => (none, d), out, next⟩ : Action 1 Bool (LoopHostState body F)) := by
  simp only [loopControlAction, rightAction, Option.map_id]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
    simp [hj]
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
    simp [hf]

/-- Phase 13 replays the captured payload in the actual host, preserving
the arbitrary completed body/fuel tapes. -/
private lemma loopHost_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) (p : Fin (x.length + 2)) (word out : List Bool)
    (tapes : Fin (body.k + 1 + (1 + F.k)) → ℤ → Option Bool)
    (heads : Fin (body.k + 1 + (1 + F.k)) → ℤ) :
    (loopHost body F anchor findMode).tm.runFrom
        (rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (loopReplayCfg x p (some ()) 0 word out) tapes heads) (word.length + 1) =
      rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
        (loopReplayCfg x p none word.length word (out ++ word)) tapes heads := by
  have htr : ∀ q inp work,
      (loopHost body F anchor findMode).tm.tr (.inr (.inr (13 : Fin 14))) inp work =
        rightAction (body.k + 1 + (1 + F.k))
          (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (loopReplayTM.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1 + (1 + F.k)) i)) := by
    intro q inp work
    cases q
    change (match work (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => loopControlAction body F 0 none (none, 0) (none, .pos) (some b)
          (some (.inr (.inr 13)))
      | none => loopControlAction body F 0 none (none, 0) (none, 0) none none) = _
    cases hw : work (Fin.last (body.k + 1 + (1 + F.k)))
    · simpa only [loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        loopControl_payload body F 0 none none
    · simpa only [loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        loopControl_payload body F .pos _ _
  refine (rightCfg_run (k := body.k + 1 + (1 + F.k)) (l := 1)
    loopReplayTM.tm (loopHost body F anchor findMode).tm
    (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) htr
    (loopReplayCfg x p (some ()) 0 word out) tapes heads (word.length + 1)).trans ?_
  have hr := loopReplay_run x p word [] out
  simpa using congrArg
    (fun c => rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) c tapes heads) hr

/-- The fuel configuration on its relocated block, with the body, flag, and
counter still blank. The completed fuel residue is retained by this embedding. -/
private def loopFuelCfg (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool F.State x :=
  rightCfg id (rightCfg id c (fun (_ : Fin 1) _ => none) (fun _ => 0))
    (fun (_ : Fin (body.k + 1)) _ => none) (fun _ => 0)

/-- Relocating fuel through the counter and body blocks preserves every run.
**Proof sketch.** Apply the right-block simulation twice. Each inactive block
has its own blank tapes and origin heads, retained throughout the source run. -/
private lemma loopFuel_run (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (t : ℕ) :
    (loopFuelSource body F).runFrom (loopFuelCfg body F c) t =
      loopFuelCfg body F (F.tm.runFrom c t) := by
  let pad : MultiTapeTM (1 + F.k) Bool F.State :=
    { q₀ := F.tm.q₀
      tr := fun q inp work => rightAction 1 id
        (F.tm.tr q inp (fun i => work (Fin.natAdd 1 i))) }
  unfold loopFuelCfg
  rw [rightCfg_run pad (loopFuelSource body F) id (fun _ _ _ => rfl),
    rightCfg_run F.tm pad id (fun _ _ _ => rfl)]

/-- The relocated fuel source begins at its genuine blank configuration. -/
private lemma loopFuel_init (body F : FinTM Bool) (x : List Bool) :
    (loopFuelSource body F).initCfg x = loopFuelCfg body F (F.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]

/-- The capture track of a frame reads precisely its parameterized tape. -/
private lemma loopFrame_payload (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        (Fin.last (body.k + 1 + (1 + F.k))) = payload ph := by
  have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  simp [loopFrame, Cfg.workTapeSymbols, hf]

/-- The counter track of a frame reads precisely its parameterized tape. -/
private lemma loopFrame_counter (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k + 1, by omega⟩ = counter ch := by
  simp [loopFrame, Cfg.workTapeSymbols]

/-- Fuel-rewind phase 1 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma loopHost_fuel_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 2))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 1))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 1)))
      | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 2)))).apply _ = _
    rw [loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [loopControl_apply]
    simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 1)))
        | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 2)))).apply _ = _
      rw [loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [loopControl_apply]
      simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- During fuel copying, the processed prefix of the capture tape is blank. -/
private def loopCopyTape (pre rest : List Bool) (z : ℤ) : Option Bool :=
  if z < pre.length then none else bufferTape (pre ++ rest) z

/-- The copying frontier reads the first bit of the remaining suffix. -/
private lemma loopCopy_read (pre rest : List Bool) :
    loopCopyTape pre rest pre.length = rest.head? := by
  simp only [loopCopyTape, lt_self_iff_false, ↓reduceIte, loopBuffer_read]

/-- Clearing one fuel cell extends the already-cleared prefix by that bit. -/
private lemma loopCopy_erase (pre rest : List Bool) (b : Bool) :
    Function.update (loopCopyTape pre (b :: rest)) (pre.length : ℤ) none =
      loopCopyTape (pre ++ [b]) rest := by
  funext z
  by_cases hz : z = pre.length
  · subst z; simp [loopCopyTape]
  · rw [Function.update_of_ne hz]
    have hlt : z < (pre.length : ℤ) ↔ z < ((pre ++ [b]).length : ℤ) := by
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    simp only [loopCopyTape, hlt, List.append_assoc, List.singleton_append]

/-- Before copying begins the capture tape is the original fuel buffer. -/
private lemma loopCopy_initial (word : List Bool) :
    loopCopyTape [] word = bufferTape word := by
  funext z
  by_cases hz : z < 0
  · simp [loopCopyTape, bufferTape, hz, show ¬0 ≤ z by omega]
  · simp [loopCopyTape, hz]

/-- After copying ends the capture tape is completely blank. -/
private lemma loopCopy_final (word : List Bool) :
    loopCopyTape word [] = bufferTape [] := by
  funext z
  by_cases hz : z < word.length
  · simp [loopCopyTape, hz]
  · have hn : 0 ≤ z := by omega
    simp [loopCopyTape, hz, bufferTape, hn]

/-- Phase 2 copies the remaining fuel bits to the counter, clearing each
captured bit, then starts the synchronized rewind.
**Proof sketch.** Induct on the uncopied suffix. A nonempty suffix writes
its head at the counter's right blank, clears the corresponding payload
cell, and advances both heads. The empty suffix detects the right blank
and moves both heads left once, including when the original word is empty. -/
private lemma loopHost_fuel_copy (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (out : List Bool)
    (rest : List Bool) : ∀ pre,
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre rest) pre.length pre.length out) (rest.length + 1) =
      loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape (pre ++ rest))
        (bufferTape []) ((pre ++ rest).length - 1) ((pre ++ rest).length - 1) out := by
  induction rest with
  | nil =>
    intro pre
    rw [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
        (loopCopyTape pre []) pre.length pre.length out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => loopControlAction body F 0 none (some (some b), .pos)
          (some none, .pos) none (some (.inr (.inr 2)))
      | none => loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))).apply _ = _
    rw [loopFrame_payload, loopCopy_read]
    dsimp only [List.head?]
    rw [loopControl_apply]
    simp [loopWrite, loopCopy_final, sub_eq_add_neg]
  | cons b rest ih =>
    intro pre
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre (b :: rest)) pre.length pre.length out) =
        loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape (pre ++ [b]))
          (loopCopyTape (pre ++ [b]) rest) (pre ++ [b]).length (pre ++ [b]).length out := by
      change (match (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre (b :: rest)) pre.length pre.length out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some bit => loopControlAction body F 0 none (some (some bit), .pos)
            (some none, .pos) none (some (.inr (.inr 2)))
        | none => loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))).apply _ = _
      rw [loopFrame_payload, loopCopy_read]
      dsimp only [List.head?]
      rw [loopControl_apply]
      simp [loopWrite, loopCopy_erase, bufferTape_append]
    rw [hs]
    simpa [List.append_assoc] using ih (pre ++ [b])

/-- Phase 3 rewinds counter and cleared capture heads together.
**Proof sketch.** Induct on the number of counter cells to the left. Both
heads take the same moves; only the counter is read, so the already-cleared
capture tape stays blank. The final left-blank test moves both heads to zero. -/
private lemma loopHost_fuel_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
        (bufferTape []) ((0 : ℤ) - 1) ((0 : ℤ) - 1) out).workTapeSymbols
          ⟨body.k + 1, by omega⟩ with
      | some _ => loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))
      | none => loopControlAction body F 0 none (none, .pos) (none, .pos) none
          (some (.inr (.inr 4)))).apply _ = _
    rw [loopFrame_counter]
    simp only [zero_sub, bufferTape_left]
    rw [loopControl_apply]
    simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out) =
        loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out := by
      change (match (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            ⟨body.k + 1, by omega⟩ with
        | some _ => loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))
        | none => loopControlAction body F 0 none (none, .pos) (none, .pos) none
            (some (.inr (.inr 4)))).apply _ = _
      rw [loopFrame_counter]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [loopControl_apply]
      simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Fuel setup phases 0--3 copy the complete fuel word to the counter,
clear the capture track, and return both heads to zero in exactly `3|word|+4`
steps. This includes the empty word, with no counter debit.
**Proof sketch.** Compose the mandatory left move, the fuel rewind, the
copy/clear scan, and the synchronized rewind. Their costs are respectively
one and three copies of the word length plus one. -/
private lemma loopHost_fuel_setup (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
          (bufferTape word) 0 word.length out) (3 * word.length + 4) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  have hs : (loopHost body F anchor findMode).tm.step
      (loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
        (bufferTape word) 0 word.length out) =
      loopFrame body F base (some (.inr (.inr 1))) p flag (bufferTape [])
        (bufferTape word) 0 ((word.length : ℤ) - 1) out := by
    change (loopControlAction body F 0 none (none, 0) (none, .neg) none
      (some (.inr (.inr 1)))).apply _ = _
    rw [loopControl_apply]
    simp [loopWrite, sub_eq_add_neg]
  rw [show 3 * word.length + 4 =
      ((word.length + 1) + (word.length + 1) + (word.length + 1)) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs]
  rw [MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add (a := word.length + 1) (b := word.length + 1),
    loopHost_fuel_rewind body F anchor findMode base p flag (bufferTape []) 0 word out
      word.length (le_refl _)]
  have hc := loopHost_fuel_copy body F anchor findMode base p flag out word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, loopCopy_initial] at hc
  rw [hc, loopHost_fuel_return body F anchor findMode base p flag word out
    word.length (le_refl _)]

/-- The host's captured fuel endpoint, retaining all completed fuel residue. -/
private def loopFuelCaptured (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x :=
  captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] (loopFuelCfg body F c)

/-- The prepared startup configuration: fuel copied, capture blank, input
and active heads at their origins, and completed fuel work retained. -/
private def loopReady (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x :=
  loopFrame body F (loopFuelCaptured body F c)
    (some (.inr (.inl (true, (body.tm.q₀, false))))) 1
    (bufferTape []) (bufferTape c.output) (bufferTape []) 0 0 []

/-- At a genuine fuel halt the capture endpoint has the frame expected by
phase 0, with the flag and counter still blank.
**Proof sketch.** Split the physical tape index into capture, body/flag,
counter, and fuel blocks. The three active controller tracks agree with
their explicit parameters; every inactive track is retained from the base. -/
private lemma loopFuelCaptured_frame (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (hc : c.state = none) :
    loopFuelCaptured body F c =
      loopFrame body F (loopFuelCaptured body F c) (some (.inr (.inr 0))) c.inputPos
        (bufferTape []) (bufferTape []) (bufferTape c.output) 0 c.output.length [] := by
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, hc]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, hf]
    · intro j
      have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [loopFrame, hbf, Nat.ne_of_lt b.isLt]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [loopFuelCaptured, captureCfg, loopFuelCfg, rightCfg, loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [loopFrame, hbf, Nat.ne_of_lt b.isLt]

/-- Fuel execution, setup, and input rewind reach prepared body startup
within `5*T+7` steps, retaining the actual fuel endpoint.
**Proof sketch.** Replace the supplied padded fuel run by its first halt,
relocate it twice, and capture it in the actual host. Setup costs `3L+4`,
where `L ≤ T`; the input rewind costs at most the first run's displacement
plus two, hence at most `T+3`. No bound in the input length is used. -/
private lemma loopHost_prepare (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (loopHost body F anchor findMode).tm.runFrom
        ((loopHost body F anchor findMode).tm.initCfg x) t = loopReady body F c := by
  obtain ⟨space, hhalt, hout, hspace⟩ := hF x
  obtain ⟨u, hu, hut, hlive, huh, hue⟩ :=
    loop_first_halt F.tm (F.tm.initCfg x) (T x.length) (by simp [MultiTapeTM.initCfg, Cfg.init]) hhalt
  let c := F.tm.runFrom (F.tm.initCfg x) u
  have hc : c.state = none := huh
  have ho : c.output = Nat.bits (R x.length) := by dsimp only [c]; rw [hue]; exact hout
  have hcap : (loopHost body F anchor findMode).tm.runFrom
      ((loopHost body F anchor findMode).tm.initCfg x) u = loopFuelCaptured body F c := by
    rw [loopHost_init, loopFuel_init]
    rw [loopHost_fuel_capture]
    · rw [loopFuel_run]; rfl
    · intro v hv
      rw [loopFuel_run]
      simpa [Cfg.Halted, loopFuelCfg, rightCfg] using hlive v hv
  let prepared := loopFrame body F (loopFuelCaptured body F c)
    (some (.inr (.inr 4))) c.inputPos (bufferTape []) (bufferTape c.output)
    (bufferTape []) 0 0 []
  have hsetup : (loopHost body F anchor findMode).tm.runFrom
      (loopFuelCaptured body F c) (3 * c.output.length + 4) = prepared := by
    conv_lhs => arg 1; rw [loopFuelCaptured_frame body F c hc]
    exact loopHost_fuel_setup body F anchor findMode _ _ _ _ _
  obtain ⟨v, hv, hrew⟩ := loopHost_input_rewind body F anchor findMode prepared rfl
  have hw : c.output.length ≤ T x.length := by rw [ho]; exact loop_fuel_width F R T hF x
  have hp : c.inputPos.val ≤ 1 + u := loop_input_run_le F.tm (F.tm.initCfg x) u
  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_⟩
  · change v ≤ c.inputPos.val + 2 at hv
    omega
  · rw [MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew]
    rfl

/-- The stopped body's padded source configuration, preserving the counter
word and the complete fuel residue through every call. -/
private def loopBodyPadded (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x :=
  leftCfg id (loopBodyCfg body anchor c release flag)
    (Fin.addCases (fun (_ : Fin 1) => bufferTape word) fuel.workTapes)
    (Fin.addCases (fun (_ : Fin 1) => 0) fuel.workTapePos)

/-- A body call viewed inside the concrete capturing host. A halted stopped
body is represented by the corresponding startup/active return phase. -/
private def loopCall (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (startup : Bool) (c : Cfg body.k Bool body.State x) (release : Bool)
    (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x :=
  captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
    (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
    (loopBodyPadded body F anchor c release flag word fuel)

/-- The padded body source simulates the stopped body with arbitrary inactive
counter and fuel tracks. -/
private lemma loopBodySource_run (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool}
    (c : Cfg (body.k + 1) Bool (body.State × Bool) x)
    (tapes : Fin (1 + F.k) → ℤ → Option Bool) (heads : Fin (1 + F.k) → ℤ) (t : ℕ) :
    (loopBodySource body F anchor).runFrom (leftCfg id c tapes heads) t =
      leftCfg id ((loopBodyTM body anchor).tm.runFrom c t) tapes heads :=
  leftCfg_run (loopBodyTM body anchor).tm (loopBodySource body F anchor)
    id (fun _ _ _ => rfl) c tapes heads t

/-- A live anchor endpoint is captured after one additional stop step.
The exact endpoint keeps every inactive tape and carries the false stop flag.
**Proof sketch.** The live endpoint rules out earlier halts. Use the source
wrapper simulation up to that endpoint, take its silent anchor-stop step,
and lift the resulting run through the padded source and actual host capture.
The guard at time zero is supplied by the release bit for active calls. -/
private lemma loopHost_anchor_return (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hend : (body.tm.runFrom c t).state = some anchor)
    (hreleased : t = 0 → release = false)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor startup c release none word fuel) (t + 1) =
      loopCall body F anchor startup {body.tm.runFrom c t with state := none}
        false (some false) word fuel := by
  have hlive : ∀ u ≤ t, (body.tm.runFrom c u).state ≠ none :=
    loop_live_prefix body.tm c t (by rw [hend]; simp)
  have hc : c.state ≠ none := by simpa using hlive 0 (Nat.zero_le _)
  have hr : (loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none) t =
      loopBodyCfg body anchor (body.tm.runFrom c t) false none := by
    rw [loopBody_run body anchor c release hc t
      (fun u hu => hlive u (by omega)) hanchor]
    have hn := hlive t (le_refl _)
    rw [if_neg hn]
    by_cases ht : t = 0
    · rw [if_pos ht, hreleased ht]
    · rw [if_neg ht]
  have hstop : (loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none)
      (t + 1) =
      loopBodyCfg body anchor {body.tm.runFrom c t with state := none} false (some false) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hr, loopBody_stop body anchor _ hend]
  unfold loopCall loopBodyPadded
  rw [loopHost_body_capture]
  · rw [loopBodySource_run, hstop]
  · intro u hu
    rw [loopBodySource_run, loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, leftCfg, loopBodyCfg] using hlive u (by omega)

/-- Prepared fuel startup is the canonical captured body call on blank body
tapes; the counter and fuel residue are exactly the padded inactive block.
**Proof sketch.** Compare the four physical tape blocks. The input head and
all active heads are at their origins; only the completed fuel bank has
arbitrary contents and head positions. -/
private lemma loopReady_call (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (fuel : Cfg F.k Bool F.State x) :
    loopReady body F fuel =
      loopCall body F anchor true (body.tm.initCfg x) false none fuel.output fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [loopReady, loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg,
        loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [loopReady, loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg,
          loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, loopFuelCaptured, loopFuelCfg,
          rightCfg, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [loopReady, loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg,
            loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hb : (b : ℕ) < F.k := b.isLt
          simp [loopReady, loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg,
            loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, loopFuelCaptured, loopFuelCfg,
            rightCfg, hbf, hb, Nat.ne_of_lt hb, Fin.addCases]

/-- Phase 6 clears startup's false flag and releases the first anchor for
free. It changes no body, counter, or fuel data.
**Proof sketch.** The captured stopped body is in phase 6. Its sole write
clears the flag's origin cell. Comparing tape blocks identifies the result
with the active released call on the same body data. -/
private lemma loopHost_release (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    (loopHost body F anchor findMode).tm.step
        (loopCall body F anchor true {c with state := none} false (some false) word fuel) =
      loopCall body F anchor false {c with state := some anchor} true none word fuel := by
  change (loopControlAction body F 0 (some none) (none, 0) (none, 0) none
    (some (.inr (.inl (false, (anchor, true)))))).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hf : (i : ℕ) = body.k
    · have hi : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
        leftCfg, loopBodyCfg, hf, hi, Fin.addCases, Function.update]
    · by_cases hb : (i : ℕ) < body.k + 1
      · have hi : (i : ℕ) < body.k := by omega
        simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
          leftCfg, loopBodyCfg, hf, Fin.addCases, hb, hi]
      · simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
          leftCfg, loopBodyCfg, hf, Fin.addCases, hb]
  · funext i
    by_cases hf : (i : ℕ) = body.k <;>
      simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
        leftCfg, loopBodyCfg, hf]
  · simp [Action.apply, loopControlAction, loopCall, captureCfg]

/-- Genuine body startup reaches the released first candidate in at most
its source startup time plus two host steps.
**Proof sketch.** The no-anchor prefix includes time zero, so startup is
captured without a premature stop. Its live endpoint yields the false flag;
one stop step and phase 6's flag-clear step release the initial candidate. -/
private lemma loopHost_start (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s : List Bool) (t : ℕ)
    (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s)) :
    (loopHost body F anchor findMode).tm.runFrom (loopReady body F fuel) (t + 2) =
      loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
        true none fuel.output fuel := by
  rw [loopReady_call body F anchor, show t + 2 = (t + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step']
  rw [loopHost_anchor_return body F anchor findMode true (body.tm.initCfg x) false t
    fuel.output fuel (by rw [hend]; rfl) (fun _ => rfl) (fun u hu => Or.inr (hguard u hu))]
  rw [hend, loopHost_release body F anchor findMode _ _ _]
  rfl

/-- A genuine first halt returns to phase 7 with the true stop flag and the
entire source output captured, including its halting emission.
**Proof sketch.** Simulate the released body through its first halting action.
Strict liveness permits actual-host capture throughout; the positive duration
consumes the release bit and the halting action sets the true flag. -/
private lemma loopHost_halt_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (t : ℕ) (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (ht : 0 < t) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u, 0 < u → u < t → (body.tm.runFrom c u).state ≠ some anchor)
    (hend : (body.tm.runFrom c t).state = none) :
    (loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor false c true none word fuel) t =
      loopCall body F anchor false (body.tm.runFrom c t) false (some true) word fuel := by
  have hc : c.state ≠ none := by simpa using hlive 0 ht
  have hg : ∀ u < t, (u = 0 ∧ true = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor := by
    intro u hu
    by_cases hz : u = 0
    · exact Or.inl ⟨hz, rfl⟩
    · exact Or.inr (hanchor u (by omega) hu)
  unfold loopCall loopBodyPadded
  rw [loopHost_body_capture]
  · rw [loopBodySource_run, loopBody_run body anchor c true hc t hlive hg]
    simp [hend, Nat.ne_of_gt ht]
  · intro u hu
    rw [loopBodySource_run, loopBody_run body anchor c true hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hg v (by omega))]
    simpa [Cfg.Halted, leftCfg, loopBodyCfg] using hlive u hu

/-- A captured body call has the explicit flag, counter, and payload tracks
used by the controller frame, with arbitrary inactive body and fuel residue. -/
private lemma loopCall_frame (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    loopCall body F anchor startup c release flag word fuel =
      loopFrame body F (loopCall body F anchor startup c release flag word fuel)
        (loopCall body F anchor startup c release flag word fuel).state c.inputPos
        (fun z => if z = 0 then flag else none) (bufferTape word) (bufferTape c.output)
        0 c.output.length [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hp, hpf]
        · simp [loopFrame, hf, hc, hp]

/-- Reframing a body call changes precisely its control, flag, and counter.
**Proof sketch.** The source configuration changes only in state. Thus all
inactive body and fuel data coincide; compare the three explicitly replaced
tracks and retain every other physical tape and head. -/
private lemma loopCall_reframe (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (c : Cfg body.k Bool body.State x)
    (startup startup' release release' : Bool) (flag flag' : Option Bool)
    (word word' : List Bool) (fuel : Cfg F.k Bool F.State x) (q : Option body.State) :
    loopFrame body F (loopCall body F anchor startup c release flag word fuel)
        (loopCall body F anchor startup' {c with state := q} release' flag' word' fuel).state
        c.inputPos (fun z => if z = 0 then flag' else none) (bufferTape word')
        (bufferTape c.output) 0 c.output.length [] =
      loopCall body F anchor startup' {c with state := q} release' flag' word' fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hp, hpf]
        · by_cases hb : (i : ℕ) < body.k + 1
          · have hi : (i : ℕ) < body.k := by omega
            simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hi]
          · have hn : (i : ℕ) - (body.k + 1) ≠ 0 := by omega
            simp [loopFrame, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hn]

/-- One actual-host borrow step changes only the counter, recording success
or underflow in the rewind phase. -/
private lemma loopHost_borrow_step (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (pre rest : List Bool) :
    (loopHost body F anchor findMode).tm.step
      (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
        (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []) =
      match rest with
      | [] => loopFrame body F base (some (.inr (.inr 10))) p (bufferTape [])
          (bufferTape pre) (bufferTape []) (pre.length - 1) 0 []
      | true :: us => loopFrame body F base (some (.inr (.inr 9))) p (bufferTape [])
          (bufferTape (pre ++ false :: us)) (bufferTape []) (pre.length - 1) 0 []
      | false :: us => loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ true :: us)) (bufferTape []) (pre.length + 1) 0 [] := by
  change (match (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
      (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []).workTapeSymbols
        ⟨body.k + 1, by omega⟩ with
    | some false => loopControlAction body F 0 none (some (some true), .pos) (none, 0)
        none (some (.inr (.inr 8)))
    | some true => loopControlAction body F 0 none (some (some false), .neg) (none, 0)
        none (some (.inr (.inr 9)))
    | none => loopControlAction body F 0 none (none, .neg) (none, 0) none
        (some (.inr (.inr 10)))).apply _ = _
  rw [loopFrame_counter, loopBuffer_read]
  cases rest with
  | nil =>
    simp only [List.head?]
    rw [loopControl_apply]
    simp [loopWrite, sub_eq_add_neg]
  | cons b rest =>
    cases b <;> simp only [List.head?]
    all_goals rw [loopControl_apply]; simp [loopWrite, loopBuffer_write, sub_eq_add_neg]

/-- The actual host performs the borrow scan in the standalone scan's exact
time, preserving all non-counter tracks.
**Proof sketch.** Induct on the remaining word. Each false bit advances the
processed prefix. A true bit or the right blank starts the appropriate
rewind phase; no cell outside the original counter width is written. -/
private lemma loopHost_borrow_run (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) : ∀ pre,
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ word)) (bufferTape []) pre.length 0 [])
        (loopBorrowPos word + 1) =
      loopFrame body F base (some (.inr (.inr (if (loopDebit word).2 then 9 else 10)))) p
        (bufferTape []) (bufferTape (pre ++ (loopDebit word).1)) (bufferTape [])
        ((pre.length : ℤ) + loopBorrowPos word - 1) 0 [] := by
  induction word with
  | nil =>
    intro pre
    simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      loopHost_borrow_step body F anchor findMode base p pre []
  | cons b word ih =>
    intro pre
    cases b with
    | true =>
      simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        loopHost_borrow_step body F anchor findMode base p pre (true :: word)
    | false =>
      simp only [loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, loopHost_borrow_step]
      simpa [loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- The host's success/underflow rewind returns the counter head to zero.
Success releases the next anchor; underflow enters phase 11 without yet
emitting. Both paths retain all inactive residue.
**Proof sketch.** Induct on the number of counter cells to the left. The
left-blank test dispatches according to the stored success bit. -/
private lemma loopHost_borrow_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) (success : Bool) :
    ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 []) (j + 1) =
      loopFrame body F base
        (some (if success then .inr (.inl (false, (anchor, true))) else .inr (.inr 11))) p
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    cases success <;>
      (change (match (loopFrame body F base _ p (bufferTape []) (bufferTape word)
          (bufferTape []) ((0 : ℤ) - 1) 0 []).workTapeSymbols ⟨body.k + 1, by omega⟩ with
        | some _ => loopControlAction body F 0 none (none, .neg) (none, 0) none _
        | none => loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
    all_goals
      rw [loopFrame_counter]
      simp only [zero_sub, bufferTape_left]
      rw [loopControl_apply]
      simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []) =
        loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 [] := by
      cases success <;>
        (change (match (loopFrame body F base _ p (bufferTape []) (bufferTape word)
            (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []).workTapeSymbols
              ⟨body.k + 1, by omega⟩ with
          | some _ => loopControlAction body F 0 none (none, .neg) (none, 0) none _
          | none => loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
      all_goals
        rw [loopFrame_counter, show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
          bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
        rw [loopControl_apply]
        simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- The complete actual-host counter operation has the fixed-width
worst-case bound `2|word|+2`, covering underflow and width zero. -/
private lemma loopHost_borrow (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) :
    2 * loopBorrowPos word + 2 ≤ 2 * word.length + 2 ∧
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape word) (bufferTape []) 0 0 []) (2 * loopBorrowPos word + 2) =
      loopFrame body F base
        (some (if (loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) p
        (bufferTape []) (bufferTape (loopDebit word).1) (bufferTape []) 0 0 [] := by
  refine ⟨by have := loopBorrowPos_le word; omega, ?_⟩
  have hr := loopHost_borrow_run body F anchor findMode base p word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * loopBorrowPos word + 2 =
      (loopBorrowPos word + 1) + (loopBorrowPos word + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact loopHost_borrow_rewind body F anchor findMode base p (loopDebit word).1
    (loopDebit word).2 _ (by rw [loopDebit_length]; exact loopBorrowPos_le word)

/-- The flag read is at its fixed origin, independently of inactive residue. -/
private lemma loopFrame_flag (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (q : Option (LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k, by omega⟩ = flag 0 := by
  simp [loopFrame, Cfg.workTapeSymbols]

/-- Clearing the only flag cell leaves a completely blank flag tape. -/
private lemma loopFlag_clear (flag : Option Bool) :
    loopWrite (fun z : ℤ => if z = 0 then flag else none) 0 (some none) = bufferTape [] := by
  funext z
  by_cases hz : z = 0 <;> simp [loopWrite, Function.update, hz]

/-- A rejecting stopped call clears its flag, debits in worst-case width
time, and either releases the next anchor or emits exhaustion and halts.
Underflow and its emission are included in this same segment.
**Proof sketch.** Phase 7 clears the false flag in one step. The proved host
borrow takes `2j+2` steps. Success is the reframed next body seam; underflow
takes one additional phase-11 step, for at most `2|word|+4` steps in total. -/
private lemma loopHost_reject (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.state = none) (ho : c.output = []) :
    ∃ t ≤ 2 * word.length + 4,
      if (loopDebit word).2 then
        (loopHost body F anchor findMode).tm.runFrom
            (loopCall body F anchor false c false (some false) word fuel) t =
          loopCall body F anchor false {c with state := some anchor} true none (loopDebit word).1 fuel
      else
        ((loopHost body F anchor findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).output =
            (if findMode then [] else [false]) := by
  let base := loopCall body F anchor false c false (some false) word fuel
  have hs : base.state = some (.inr (.inr (7 : Fin 14))) := by
    simp [base, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hc]
  have hf : base = loopFrame body F base (some (.inr (.inr 7))) c.inputPos
      (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 [] := by
    have h := loopCall_frame body F anchor false c false (some false) word fuel
    have hstate : (loopCall body F anchor false c false (some false) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := hs
    simpa only [hstate, ho, List.length_nil, Nat.cast_zero] using h
  have hstep : (loopHost body F anchor findMode).tm.step base =
      loopFrame body F base (some (.inr (.inr 8))) c.inputPos
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
    conv_lhs => arg 1; rw [hf]
    change (if (loopFrame body F base (some (.inr (.inr 7))) c.inputPos
        (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [loopFrame_flag]
    change (loopControlAction body F 0 (some none) (none, 0) (none, 0) none
      (some (.inr (.inr 8)))).apply _ = _
    rw [loopControl_apply, loopFlag_clear]
    simp [loopWrite]
  have hrun : (loopHost body F anchor findMode).tm.runFrom base (2 * loopBorrowPos word + 3) =
      loopFrame body F base
        (some (if (loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) c.inputPos
        (bufferTape []) (bufferTape (loopDebit word).1) (bufferTape []) 0 0 [] := by
    rw [show 2 * loopBorrowPos word + 3 = (2 * loopBorrowPos word + 2) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact (loopHost_borrow body F anchor findMode base c.inputPos word).2
  have hw := loopBorrowPos_le word
  by_cases hb : (loopDebit word).2 = true
  · refine ⟨2 * loopBorrowPos word + 3, by omega, ?_⟩
    simp only [hb, if_true] at hrun ⊢
    rw [hrun]
    have h := loopCall_reframe body F anchor c false false false true (some false) none
      word (loopDebit word).1 fuel (some anchor)
    simpa [base, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, ho] using h
  · refine ⟨2 * loopBorrowPos word + 4, by omega, ?_⟩
    simp only [hb] at hrun ⊢
    have hh : (loopHost body F anchor findMode).tm.runFrom base (2 * loopBorrowPos word + 4) =
        loopFrame body F base none c.inputPos (bufferTape []) (bufferTape (loopDebit word).1)
          (bufferTape []) 0 0 (if findMode then [] else [false]) := by
      rw [show 2 * loopBorrowPos word + 4 = (2 * loopBorrowPos word + 3) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step', hrun]
      change (loopControlAction body F 0 none (none, 0) (none, 0)
        (if findMode then none else some false) none).apply _ = _
      rw [loopControl_apply]
      cases findMode <;> simp [loopWrite]
    rw [hh]
    exact ⟨rfl, rfl⟩

/-- Accepting-payload phase 12 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma loopHost_payload_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (loopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 13))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 12))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 12)))
      | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 13)))).apply _ = _
    rw [loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [loopControl_apply]
    simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (loopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 12)))
        | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 13)))).apply _ = _
      rw [loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [loopControl_apply]
      simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Phase 13 replays a framed payload, retaining arbitrary inactive tracks.
**Proof sketch.** Express the frame as the right-block replay configuration
using its own inactive tape and head projections, then apply the already
proved actual-host replay correspondence. -/
private lemma loopHost_frame_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool) (ch : ℤ) (word : List Bool) :
    let c := loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
    ((loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).state = none ∧
    ((loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).output = word := by
  dsimp only
  let c := loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
  let tapes := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapes i.castSucc
  let heads := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapePos i.castSucc
  have he : c = rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
      (loopReplayCfg x p (some ()) 0 word []) tapes heads := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    all_goals
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [rightCfg, Fin.addCases_left, tapes, heads]
        congr 1
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
        simp [c, rightCfg, loopReplayCfg, loopFrame, hf]
  change ((loopHost body F anchor findMode).tm.runFrom c _).state = _ ∧
    ((loopHost body F anchor findMode).tm.runFrom c _).output = _
  rw [he, loopHost_replay]
  exact ⟨rfl, rfl⟩

/-- An accepting stopped call emits its fixed verdict or replays its full
captured payload, including the empty payload, within `2|output|+3` steps.
**Proof sketch.** The true stop flag dispatches acceptance independently of
payload length. Decision mode emits immediately. Find mode takes one left
move, the length-plus-one rewind, and the length-plus-one replay. -/
private lemma loopHost_accept (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state = none) :
    ∃ t ≤ 2 * c.output.length + 3,
      ((loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor false c false (some true) word fuel) t).state = none ∧
      ((loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor false c false (some true) word fuel) t).output =
          (if findMode then c.output else [true]) := by
  let base := loopCall body F anchor false c false (some true) word fuel
  let flag := fun z : ℤ => if z = 0 then some true else none
  have hf : base = loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
      (bufferTape word) (bufferTape c.output) 0 c.output.length [] := by
    have hstate : (loopCall body F anchor false c false (some true) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := by
      simp [loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hc]
    simpa only [hstate] using loopCall_frame body F anchor false c false (some true) word fuel
  have hstep : (loopHost body F anchor findMode).tm.step base =
      if findMode then
        loopFrame body F base (some (.inr (.inr 12))) c.inputPos flag
          (bufferTape word) (bufferTape c.output) 0 (c.output.length - 1) []
      else loopFrame body F base none c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length [true] := by
    conv_lhs => arg 1; rw [hf]
    change (if (loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [loopFrame_flag]
    change (if findMode then
      loopControlAction body F 0 none (none, 0) (none, .neg) none (some (.inr (.inr 12)))
      else loopControlAction body F 0 none (none, 0) (none, 0) (some true) none).apply _ = _
    cases findMode <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [loopControl_apply] <;> simp [loopWrite, sub_eq_add_neg]
  cases findMode with
  | false =>
    refine ⟨1, by omega, ?_⟩
    change ((loopHost body F anchor false).tm.step base).state = none ∧
      ((loopHost body F anchor false).tm.step base).output = [true]
    rw [hstep]
    exact ⟨rfl, rfl⟩
  | true =>
    refine ⟨2 * c.output.length + 3, le_refl _, ?_⟩
    have hrun : (loopHost body F anchor true).tm.runFrom base (2 * c.output.length + 3) =
        (loopHost body F anchor true).tm.runFrom
          (loopFrame body F base (some (.inr (.inr 13))) c.inputPos flag
            (bufferTape word) (bufferTape c.output) 0 0 []) (c.output.length + 1) := by
      rw [show 2 * c.output.length + 3 =
          ((c.output.length + 1) + (c.output.length + 1)) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step, hstep]
      simp only [if_true]
      rw [MultiTapeTM.runFrom_add, loopHost_payload_rewind body F anchor true base
        c.inputPos flag (bufferTape word) 0 c.output [] c.output.length (le_refl _)]
    change ((loopHost body F anchor true).tm.runFrom base _).state = _ ∧
      ((loopHost body F anchor true).tm.runFrom base _).output = _
    rw [hrun]
    exact loopHost_frame_replay body F anchor true base c.inputPos flag (bufferTape word) 0 c.output

/-- One body round plus all controller work has a uniform local bound.
Acceptance returns the exact payload/verdict; rejection either reaches the
decremented next seam or finishes underflow within the same segment.
**Proof sketch.** For acceptance, replace a padded endpoint by its first
halt, capture every emission, and use the accepting dispatch bound. At most
one symbol is emitted per source step. For rejection, the live seam supplies
the anchor-stop capture; append the complete width-bounded counter dispatch. -/
private lemma loopHost_round (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s next payload : List Bool) (accepted : Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (t : ℕ) (ht : 0 < t)
    (hanchor : ∀ u, 0 < u → u < t →
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u).state ≠ some anchor)
    (hend : if accepted then
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = payload
      else body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
        Cfg.ofWords anchor (stateWord body.k next)) :
    ∃ v ≤ 3 * t + 2 * word.length + 5,
      let start := loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel
      if accepted then
        ((loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then payload else [true])
      else if (loopDebit word).2 then
        (loopHost body F anchor findMode).tm.runFrom start v =
          loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k next))
            true none (loopDebit word).1 fuel
      else ((loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then [] else [false]) := by
  dsimp only
  let start := Cfg.ofWords (input := x) anchor (stateWord body.k s)
  by_cases ha : accepted = true
  · simp only [ha, if_true] at hend ⊢
    obtain ⟨u, hu, hut, hlive, hhalt, he⟩ := loop_first_halt body.tm start t (by simp [start, Cfg.ofWords]) hend.1
    have hcap := loopHost_halt_return body F anchor findMode start u word fuel hu hlive
      (fun v hv hvu => hanchor v hv (by omega)) hhalt
    obtain ⟨v, hv, hstop, hout⟩ := loopHost_accept body F anchor findMode (body.tm.runFrom start u) word fuel hhalt
    have hw : (body.tm.runFrom start u).output.length ≤ u := by
      simpa [start, Cfg.ofWords] using loop_output_length_le body.tm start u
    refine ⟨u + v, by omega, ?_⟩
    change ((loopHost body F anchor findMode).tm.runFrom
      (loopCall body F anchor false start true none word fuel) (u + v)).state = _ ∧ _
    rw [MultiTapeTM.runFrom_add, hcap]
    refine ⟨hstop, ?_⟩
    rw [hout, he, hend.2]
  · simp only [ha] at hend ⊢
    have hguard : ∀ u < t, (u = 0 ∧ true = true) ∨ (body.tm.runFrom start u).state ≠ some anchor := by
      intro u hu
      by_cases hz : u = 0
      · exact Or.inl ⟨hz, rfl⟩
      · exact Or.inr (hanchor u (by omega) hu)
    have hcap := loopHost_anchor_return body F anchor findMode false start true t word fuel
      (by rw [hend]; rfl)
      (by intro hz; omega) hguard
    change (loopHost body F anchor findMode).tm.runFrom _ (t + 1) = _ at hcap
    have hr : body.tm.runFrom start t = Cfg.ofWords anchor (stateWord body.k next) := hend
    rw [hr] at hcap
    obtain ⟨v, hv, hfinish⟩ := loopHost_reject body F anchor findMode
      {Cfg.ofWords (input := x) anchor (stateWord body.k next) with state := none} word fuel rfl rfl
    refine ⟨(t + 1) + v, by omega, ?_⟩
    change (if (loopDebit word).2 then
      (loopHost body F anchor findMode).tm.runFrom
        (loopCall body F anchor false start true none word fuel) ((t + 1) + v) = _
      else _)
    rw [MultiTapeTM.runFrom_add, hcap]
    exact hfinish

/-- The audit's single maximum: startup coefficient nine, body coefficient
three, counter coefficient two, and dispatch allowance five. -/
private def loopHost_bound : ℕ := max 1 (max 9 (3 + 2 + 5))

/-- Configuration contracts for the concrete controller in both output modes.
**Continuation frontier: unproved.** The public corollaries below are conditional
on this one machine-construction obligation; this is not a closed batch.

**Proof sketch.** Run the relocated fuel source to its first halt using
`loopHost_fuel_capture`. Phases 0--5 copy and retain its binary fuel, clear
the capture tape, and rewind the two work heads and the input head. Run
startup with `loopHost_body_capture`; phase 6 clears the flag and releases
the initial seam without a debit. Define each candidate seam using the
iterated body word and `loopDebit` word, retaining the fuel work residue.
`loop_orbit_inv` supplies every local body premise. The body simulation and
first-halt lemmas identify the first stop; W1 preserves its full payload.
Phase 7 either emits/replays that payload or starts the width-bounded
borrow. The host performs the counter borrow and rewind
in phases 8--10. Final zero underflow and phase 11 belong to the
last rejecting segment. If the last candidate accepts, choose any halted
false/empty terminal. Sum the phase constants with the audit's maximum
ledger. The missing proof is precisely the controller-level lifting and
assembly of these phase contracts, including startup and replay bounds. -/
/- Batch L2 closure: the preceding continuation docstring is retained as
historical evidence. Its listed obligations are discharged below by the phase
lemmas and the canonical family; there is no remaining construction admission. -/
private lemma loopHost_contracts (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool) (findMode : Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ c : ℕ, ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg (loopHost body F anchor findMode).k Bool
          (loopHost body F anchor findMode).State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        (loopHost body F anchor findMode).tm.runFrom
          ((loopHost body F anchor findMode).tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = (if findMode then [] else [false]) ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            ((loopHost body F anchor findMode).tm.runFrom (cfg i) t).state = none ∧
            ((loopHost body F anchor findMode).tm.runFrom (cfg i) t).output =
              (if findMode then out x ((stepF x)^[i] (s0 x)) else [true])
          else (loopHost body F anchor findMode).tm.runFrom (cfg i) t = cfg (i + 1)) := by
  classical
  refine ⟨loopHost_bound, ?_⟩
  intro x
  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare⟩ :=
    loopHost_prepare body F anchor findMode R T hF x
  obtain ⟨btime, hbt, hbguard, hbend⟩ := hstart x
  let words (i : ℕ) := (fun w => (loopDebit w).1)^[i] (Nat.bits (R x.length))
  let orbit (i : ℕ) := (stepF x)^[i] (s0 x)
  let candidate (i : ℕ) := loopCall body F anchor false
    (Cfg.ofWords (input := x) anchor (stateWord body.k (orbit i))) true none (words i) fuel
  have hwidth (i : ℕ) : (words i).length ≤ T x.length := by
    dsimp only [words]
    rw [loopDebit_iterate_length]
    exact loop_fuel_width F R T hF x
  have hsuccess (i : ℕ) (hi : i ≤ R x.length) :
      (loopDebit (words i)).2 = true ↔ i < R x.length := by
    rw [loopDebit_success]
    dsimp only [words]
    rw [loopDebit_iterate_value _ _ hi]
    omega
  -- Each specified seam has its own local contract, including unreachable
  -- seams following an earlier accepting candidate.
  have hlocal : ∀ i ≤ R x.length, ∃ t ≤ loopHost_bound * (T x.length + 1),
      if acceptF x (orbit i) then
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (loopHost body F anchor findMode).tm.runFrom (candidate i) t = candidate (i + 1)
      else
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then [] else [false]) := by
    intro i hi
    obtain ⟨t, htpos, ht, hguard, hend⟩ := hround x (orbit i)
      (loop_orbit_inv Inv stepF s0 hInv0 hInvStep x i)
    obtain ⟨v, hv, hsegment⟩ := loopHost_round body F anchor findMode
      (orbit i) (stepF x (orbit i)) (out x (orbit i)) (acceptF x (orbit i))
      (words i) fuel t htpos hguard hend
    refine ⟨v, ?_, ?_⟩
    · have hw := hwidth i
      change v ≤ 10 * (T x.length + 1)
      omega
    · simpa only [candidate, words, orbit, Function.iterate_succ_apply', hsuccess i hi] using hsegment
  -- Fix one segment witness per seam so the last rejecting segment's actual
  -- endpoint, including underflow and emission, is the chosen terminal.
  let time (i : ℕ) := if hi : i ≤ R x.length then (hlocal i hi).choose else 0
  have htime (i : ℕ) (hi : i ≤ R x.length) :
      time i ≤ loopHost_bound * (T x.length + 1) ∧
      if acceptF x (orbit i) then
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (loopHost body F anchor findMode).tm.runFrom (candidate i) (time i) = candidate (i + 1)
      else
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then [] else [false]) := by
    simpa only [time, dif_pos hi] using (hlocal i hi).choose_spec
  have hlast := htime (R x.length) (le_refl _)
  let terminal := if acceptF x (orbit (R x.length)) then
      {candidate (R x.length + 1) with state := none, output := if findMode then [] else [false]}
    else (loopHost body F anchor findMode).tm.runFrom (candidate (R x.length))
      (time (R x.length))
  have hterminal : terminal.state = none ∧ terminal.output = (if findMode then [] else [false]) := by
    dsimp only [terminal]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i ha
      simpa only [ha, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl] using hlast.2
  let cfg (i : ℕ) := if i ≤ R x.length then candidate i else terminal
  have hcfg (i : ℕ) (hi : i ≤ R x.length) : cfg i = candidate i := if_pos hi
  refine ⟨cfg, ftime + (btime + 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ftime + (btime + 2) ≤ 10 * (T x.length + 1)
    omega
  · rw [hcfg 0 (Nat.zero_le _), MultiTapeTM.runFrom_add, hprepare,
      loopHost_start body F anchor findMode (s0 x) btime fuel hbguard hbend]
    simp only [candidate, words, orbit, Function.iterate_zero_apply, hfo]
  · intro i hi
    rw [hcfg i hi]
    rfl
  · simpa only [cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)] using hterminal.1
  · simpa only [cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)] using hterminal.2
  · intro i hi
    have h := htime i hi
    refine ⟨time i, h.1, ?_⟩
    rw [hcfg i hi]
    change (if acceptF x (orbit i) then _ else _)
    by_cases ha : acceptF x (orbit i) = true
    · simp only [ha, if_true] at h ⊢
      simpa only [orbit] using h.2
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hlt : i < R x.length
      · rw [hcfg (i + 1) (by omega)]
        simpa only [if_pos hlt] using h.2
      · have he : i = R x.length := by omega
        subst i
        rw [show cfg (R x.length + 1) = terminal from if_neg (by omega)]
        simp only [terminal, ha, Bool.false_eq_true, ↓reduceIte]

/-- **The configuration-level loop combinator** (spec, fill pending;
added per round-2 finding 1 — the final-answer conclusion below cannot
discharge a configuration contract: the round-2 audit exhibits a machine
that answers correctly after a deliberate exponential delay, satisfying
the final-answer form while violating every per-round bound). Same
hypotheses as `exists_loopTM`; the conclusion instead exposes, for every
input, the host's **round-configuration family**: a bounded startup
reaching `cfg 0`, empty output at every round configuration, a per-round
accept-or-advance segment within a uniform constant multiple of
`T |x| + 1` — acceptance halting with `[true]`, advance reaching
`cfg (i + 1)` — and the halted `[false]` exhaustion terminal at index
`R |x| + 1`. This is the generic shape of the frozen Chapter-2
`enumMachine_contracts` (`machine-library-design.md` §9c gives the index
and budget translation). The decision form below is a corollary through
an already-halted-terminal summation lemma; the find form shares the
host construction with the payload surfaced, and is not claimed as a
`Turing.loop_run` corollary (round-3 finding R3-1).

**Proof sketch.** The intended host of `exists_loopTM` already *has* this
family: `cfg i` is the host image of the body's seam at the `i`-th orbit
point together with the counter state after `i` debits (initial entry
free), and `cfg (R |x| + 1)` is the halted configuration after the borrow
underflow and the `[false]` emission. Startup is the fuel phase plus the
body startup; each segment is one captured body round plus counter work
bounded **worst-case** by the counter width: the fuel word has length at
most `T |x|` (`Turing.MultiTapeTM.output_length_le` on the fuel machine)
and never grows, so every debit, rewind, and the final
underflow-plus-`[false]`-emission each cost a constant multiple of
`T |x| + 1` — the per-segment bound needs no amortization (round-3
finding R3-2; the amortized aggregate remains true but is not read off
per segment). -/
theorem exists_loopCfgTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = [false] ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            (E.tm.runFrom (cfg i) t).state = none ∧
            (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1)) := by
  obtain ⟨c, hc⟩ := loopHost_contracts body F anchor Inv stepF acceptF
    (fun _ _ => [true]) false s0 R T hF hInv0 hInvStep hstart hround
  exact ⟨loopHost body F anchor false, c, by simpa using hc⟩

/-- Summation with an already-halted exhaustion terminal. Unlike `loop_run`,
this lemma requires no empty output at that terminal and charges no final
extra segment.
**Proof sketch.** Induct on the remaining candidates, as in `enumLoop_run`.
An accepting round ends the run; a rejecting round composes with the
shifted induction hypothesis. Zero candidates use the halted terminal at
time zero, with its already-written false verdict. -/
private lemma loop_halted_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hend : (cfg N).state = none ∧ (cfg N).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ N * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  induction N generalizing cfg accept with
  | zero => exact ⟨0, by simp, by simpa using hend⟩
  | succ N ih =>
    obtain ⟨t, ht, hc⟩ := hround 0 (by omega)
    have hany : (List.range (N + 1)).any accept =
        (accept 0 || (List.range N).any (fun j => accept (j + 1))) := by
      simp [List.range_succ_eq_map, List.any_map, Function.comp_def]
    by_cases hb : accept 0 = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · exact Nat.le_mul_of_pos_left B (by omega)
      · simpa [hany, hb] using hc.2
    · simp only [hb] at hc
      obtain ⟨s, hs, hhalt, hout⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1)) hend
        (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [hany, hb] using hout

/-- **The decision loop combinator** (spec, fill pending; repaired per
round-1 findings 1, 2, and 4 — see the module docstring). Hypotheses:

* `hF`: the fuel machine writes `Nat.bits (R |x|)` within `T |x|`.
* `hInv0`, `hInvStep`: the admissibility invariant holds at the initial
  state word and is preserved by the step, so every orbit point the
  conclusion mentions is admissible.
* `hstart`: the body reaches the initial seam within `T |x|` without
  visiting the anchor state earlier.
* `hround`: on every **admissible** state word, the body takes **positive**
  time `t ≤ T |x|`, does not re-enter the anchor strictly before `t`, and
  either halts with the verdict `[true]` (acceptance) or sits at the seam
  carrying the stepped word (advance).

Conclusion: one finite machine answers, within a constant multiple of
`(T |x| + 1) · (R |x| + 2)`, whether some orbit point
`(stepF x)^[i] (s0 x)` with `i ≤ R |x|` is accepted.

At fill time this is a corollary of `exists_loopCfgTM` through an
already-halted-terminal summation lemma — the frozen `Turing.loop_run`
additionally requires an empty-output terminal, which the exported
`[false]` terminal is not (round-3 finding R3-1) — with startup absorbed
by `ComputesInTime.mono`.

**Proof sketch.** The combinator machine runs the fuel machine
relocated-and-captured to lay `Nat.bits (R |x|)` on a counter tape,
rewinds, and embeds the body via the W1 capture discipline of
`TCSlib.Complexity.TuringMachine.Build.Wrappers` (the body's verdict is
captured, never physically emitted until the end). The initial anchor
entry is free; each subsequent entry debits the binary counter in place —
per-segment cost bounded worst-case by the counter width (the proved
estimate below at the borrow lemmas; the amortized aggregate also holds
but is not used per segment), exhaustion exactly at borrow-overflow, so
rounds `0, …, R |x|` run before the exhaustion rejection `[false]`.
Acceptance surfaces as the captured halt and emits `[true]`. The private
already-halted-terminal summation lemma `loop_halted_run` sums the seam
family (the frozen `Turing.loop_run` does not apply to the `[false]`
terminal — fill-audit minor 1's documentation correction, maintainer
closing sweep); the invariant hypotheses confine every round to
admissible words, and positive round duration makes each anchor entry a
genuine round boundary. Phase overheads are absorbed into `c`. -/
theorem exists_loopTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF x ((stepF x)^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  obtain ⟨E, c, hc⟩ := exists_loopCfgTM body F anchor Inv stepF acceptF s0 R T
    hF hInv0 hInvStep hstart hround
  refine ⟨E, c, fun x => ?_⟩
  obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments⟩ := hc x
  obtain ⟨t, ht, hhalt, houtput⟩ := loop_halted_run E.tm cfg
    (fun i => acceptF x ((stepF x)^[i] (s0 x))) (c * (T x.length + 1))
    (R x.length + 1) ⟨hend, hout⟩ (fun j hj => hsegments j (by omega))
  have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
  rw [hinit] at hrun
  have hcompute : E.ComputesInTime x
      [(List.range (R x.length + 1)).any
        (fun i => acceptF x ((stepF x)^[i] (s0 x)))] (startup + t) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun]; exact hhalt
    · rw [hrun]; exact houtput
  apply hcompute.mono
  calc startup + t ≤ c * (T x.length + 1) +
        (R x.length + 1) * (c * (T x.length + 1)) := Nat.add_le_add hs ht
    _ = c * (T x.length + 1) * (R x.length + 2) := by
      rw [Nat.mul_comm (R x.length + 1)]
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
      omega

/-- The first accepting segment returns its own payload; an already-halted
empty-output terminal supplies exhaustion.
**Proof sketch.** Induct on the ordered candidate range. Acceptance at its
head terminates immediately. Otherwise compose the advance with the shifted
induction hypothesis; `find?_map` shifts the selected index back by one.
Thus the payload is tied to the least accepting candidate, including when
that payload is empty. -/
private lemma loop_find_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (payload : ℕ → List Bool) (B N : ℕ)
    (hend : (cfg N).state = none ∧ (cfg N).output = [])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = payload j
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ N * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output =
        (match (List.range N).find? accept with | some i => payload i | none => []) := by
  induction N generalizing cfg accept payload with
  | zero => exact ⟨0, by simp, by simpa using hend⟩
  | succ N ih =>
    obtain ⟨t, ht, hc⟩ := hround 0 (by omega)
    by_cases hb : accept 0 = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · exact Nat.le_mul_of_pos_left B (by omega)
      · simpa [List.range_succ_eq_map, hb] using hc.2
    · simp only [hb] at hc
      obtain ⟨s, hs, hhalt, hout⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1))
        (fun j => payload (j + 1)) hend (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc, hout, List.range_succ_eq_map]
        simp only [List.find?_cons_of_neg hb, List.find?_map, Function.comp_def]
        cases (List.range N).find? (fun j => accept (j + 1)) <;> rfl

/-- **The result-bearing loop combinator** (spec, fill pending; added per
round-1 finding 3 — the decision form exposes only a Boolean, which cannot
express the split search's or the reduction emitters' outputs). Identical
skeleton to `exists_loopTM`, except the accepting round halts with the
declared payload `out x s`, and the machine outputs the **first** accepting
orbit point's payload — `[]` on fuel exhaustion, the library's threaded
rejection value. `List.range.find?` returns the least accepting index, which
is exactly the round at which the iterated body first halts.

**Proof sketch.** As `exists_loopTM`, with one change at the surface: on
the captured halt the host replays the entire capture tape (the payload)
as its output instead of the fixed verdict — the W1 core captures the
full output word precisely so that this variant costs nothing extra. A
payload may be `[]`; the conclusion's function is well-defined regardless,
and consumers that need to distinguish success from exhaustion use
nonempty payloads (the split search's `pairEncode` outputs are always
nonempty). -/
theorem exists_loopFindTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
          | some i => out x ((stepF x)^[i] (s0 x))
          | none => [])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  obtain ⟨c, hc⟩ := loopHost_contracts body F anchor Inv stepF acceptF out true s0 R T
    hF hInv0 hInvStep hstart hround
  let E := loopHost body F anchor true
  refine ⟨E, c, fun x => ?_⟩
  obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments⟩ := hc x
  obtain ⟨t, ht, hhalt, houtput⟩ := loop_find_run E.tm cfg
    (fun i => acceptF x ((stepF x)^[i] (s0 x)))
    (fun i => out x ((stepF x)^[i] (s0 x))) (c * (T x.length + 1)) (R x.length + 1)
    ⟨hend, by simpa using hout⟩
    (fun j hj => by simpa using hsegments j (by omega))
  have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
  rw [hinit] at hrun
  have hcompute : E.ComputesInTime x
      (match (List.range (R x.length + 1)).find?
          (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
        | some i => out x ((stepF x)^[i] (s0 x))
        | none => []) (startup + t) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun]; exact hhalt
    · rw [hrun]; exact houtput
  apply hcompute.mono
  calc startup + t ≤ c * (T x.length + 1) +
        (R x.length + 1) * (c * (T x.length + 1)) := Nat.add_le_add hs ht
    _ = c * (T x.length + 1) * (R x.length + 2) := by
      rw [Nat.mul_comm (R x.length + 1)]
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
      omega

/-! ### Clean-call phase machinery

Adapted in-file from the proved `e3c*` track/clear and prepared-evaluation
family in `ClassNP/Nondeterminism.lean` (batch A continuation). The original
private declarations are templates only, never dependencies. These phases
preserve the complete tape/head configuration and dispatch at observed
completion; numerical deadlines occur only in the analysis. -/

/-- A zero-tape placeholder supplies only the empty inactive bank of the
virtual-input wrapper. Its own transition is never entered by this phase. -/
private def emCallIdleTM : FinTM Bool where
  k := 0
  State := Unit
  tm := ⟨(), fun _ _ _ => controlAction 0 none⟩

/-- The candidate evaluator is the guarded virtual-input phase of the proved
buffered simulator, wrapped by the capture transformer. Its completed state
is a live return state; no evaluated bit reaches the physical output. -/
private def emCallEvalTM (M : FinTM Bool) : FinTM Bool where
  k := (bufferedCompTM emCallIdleTM M).k + 1
  State := (bufferedCompTM emCallIdleTM M).State ⊕ Unit
  tm := {
    q₀ := .inl (bufferedCompTM emCallIdleTM M).tm.q₀
    tr := fun q inp work => match q with
      | .inl q => captureAction Sum.inl (.inr ())
          ((bufferedCompTM emCallIdleTM M).tm.tr q inp (fun i => work i.castSucc))
      | .inr () => controlAction 0 (some (.inr ())) }

/-- Exact evaluator configuration: the preserved candidate occupies tape zero,
the source work bank follows it, and the final tape captures every source
emission, including the halting emission. The original input head is fixed. -/
private def emCallEvalCfg (M : FinTM Bool) {w s : List Bool}
    (c : Cfg M.k Bool M.State s) (b : Bool) (p : Fin (w.length + 2)) :
    Cfg (emCallEvalTM M).k Bool (emCallEvalTM M).State w :=
  captureCfg Sum.inl (.inr ()) [] []
    (bufferedSecondCfg emCallIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0))

/-- Guarded virtual simulation and capture commute through every live source
prefix. The completed configuration, rather than a time bound, selects return.
**Proof sketch.** The public virtual-input theorem supplies a valid arrival
tag and the exact source configuration at each time. Its live prefixes meet
the capture theorem's guard, so the latter captures exactly that same run. -/
private lemma emCall_eval_run (M : FinTM Bool) {w s : List Bool}
    (c : Cfg M.k Bool M.State s) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (w.length + 2)) (t : ℕ)
    (hlive : ∀ j < t, (M.tm.runFrom c j).state ≠ none) :
    ∃ b', VirtualTag (M.tm.runFrom c t).inputPos b' ∧
      (emCallEvalTM M).tm.runFrom (emCallEvalCfg M c b p) t =
        emCallEvalCfg M (M.tm.runFrom c t) b' p := by
  have hvirtual (j : ℕ) := bufferedSecondCfg_run emCallIdleTM M c b hb p
    (fun i => i.elim0) (fun i => i.elim0) j
  have hguard : ∀ j < t, ¬((bufferedCompTM emCallIdleTM M).tm.runFrom
      (bufferedSecondCfg emCallIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0)) j).Halted := by
    intro j hj
    obtain ⟨tag, _, he⟩ := hvirtual j
    rw [he]
    simpa only [Cfg.Halted, bufferedSecondCfg, Option.map_eq_none_iff] using hlive j hj
  have hcap := capture_run (bufferedCompTM emCallIdleTM M).tm (emCallEvalTM M).tm
    Sum.inl (.inr ()) (fun _ _ _ => rfl) [] []
    (bufferedSecondCfg emCallIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0)) t hguard
  obtain ⟨tag, htag, he⟩ := hvirtual t
  rw [he] at hcap
  exact ⟨tag, htag, hcap⟩

/-- A prepared candidate with blank source work and an empty capture tape is
exactly the library state-word seam at the evaluator's initial virtual state.
**Proof sketch.** Compare all configuration fields. Split a tape index into the candidate,
source bank, and capture slot; all work heads start at zero. -/
private lemma emCall_eval_initial (M : FinTM Bool) (w s : List Bool) :
    emCallEvalCfg (w := w) M (M.tm.initCfg s) true 1 =
      Cfg.ofWords (.inl (.inr (.inr (M.tm.q₀, true))))
        (stateWord (emCallEvalTM M).k s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    change (if h : i.val < 0 + (1 + M.k) then
      tapeBlocks (fun j : Fin 0 => j.elim0) (bufferTape s)
        (fun _ : Fin M.k => fun _ => none) ⟨i.val, h⟩
      else bufferTape []) = bufferTape (if i.val = 0 then s else [])
    by_cases hi : i.val < 0 + (1 + M.k)
    · rw [dif_pos hi]
      by_cases hz : i.val = 0
      · simp [tapeBlocks, Fin.addCases, hz]
      · have h1 : ¬ i.val < 1 := by omega
        simp [tapeBlocks, Fin.addCases, hz, h1]
    · rw [dif_neg hi]
      have hz : i.val ≠ 0 := by omega
      simp [hz]
  · funext i
    dsimp only [emCallEvalCfg, captureCfg, bufferedSecondCfg,
      MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords]
    simp only [Fin.val_one, Nat.cast_one, sub_self, List.nil_append, List.length_nil, Nat.cast_zero]
    split
    · simp [tapeBlocks, Fin.addCases, emCallIdleTM]
    · rfl

/-- A timed evaluator reaches the actual first source halt, with no earlier
visit to the live return state and with the exact complete capture buffer.
**Proof sketch.** Take the least halting time justified by totality. Absorption
identifies the output there with the specified output at the deadline. Apply
captured virtual lockstep through that time and through every earlier prefix.
The deadline is used only for the inequality, never as a native clock. -/
private lemma emCall_eval_first (M : FinTM Bool) (w s out : List Bool) (T : ℕ)
    (hM : M.ComputesInTime s out T) :
    ∃ t ≤ T, ∃ b,
      VirtualTag (M.tm.runFrom (M.tm.initCfg s) t).inputPos b ∧
      (M.tm.runFrom (M.tm.initCfg s) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg s) t).output = out ∧
      (∀ j < t, ((emCallEvalTM M).tm.runFrom
        (emCallEvalCfg (w := w) M (M.tm.initCfg s) true 1) j).state ≠ some (.inr ())) ∧
      (emCallEvalTM M).tm.runFrom
        (emCallEvalCfg (w := w) M (M.tm.initCfg s) true 1) t =
          emCallEvalCfg (w := w) M (M.tm.runFrom (M.tm.initCfg s) t) b 1 := by
  classical
  have hspec := (computesInTime_iff M s out T).mp hM
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg s) t).state = none := ⟨T, hspec.1⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hspec.1
  have hh : (M.tm.runFrom (M.tm.initCfg s) t).state = none := Nat.find_spec hex
  have hlive : ∀ j < t, (M.tm.runFrom (M.tm.initCfg s) j).state ≠ none :=
    fun j hj => Nat.find_min hex hj
  have hout : (M.tm.runFrom (M.tm.initCfg s) t).output = out :=
    ((computesInTime_iff M s _ t).mpr ⟨hh, rfl⟩).output_unique hM
  have htag : VirtualTag (M.tm.initCfg s).inputPos true := by
    simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]
  obtain ⟨b, hb, hr⟩ := emCall_eval_run M (M.tm.initCfg s) true htag
    (1 : Fin (w.length + 2)) t hlive
  refine ⟨t, ht, b, hb, hh, hout, ?_, hr⟩
  intro j hj
  obtain ⟨b', _, hr'⟩ := emCall_eval_run M (M.tm.initCfg s) true htag
    (1 : Fin (w.length + 2)) j (fun l hl => hlive l (by omega))
  rw [hr']
  cases hs : (M.tm.runFrom (M.tm.initCfg s) j).state with
  | none => exact False.elim (hlive j hj hs)
  | some q =>
    dsimp only [emCallEvalCfg, captureCfg, bufferedSecondCfg]
    rw [hs]
    simp

/-- A contiguous visited interval, marked independently of the simulated data.
The bounds are proof data; the cleaner reads only the marker tape. -/
private def emCallInterval (left : ℤ) (width : ℕ) (z : ℤ) : Option Bool :=
  if left ≤ z ∧ z < left + width then some true else none

/-- Erase the first `j` cells of a visited interval without changing any other
cell. This describes the cleaner's successive physical tape contents. -/
private def emCallCleared (data : ℤ → Option Bool) (left : ℤ) (j : ℕ) (z : ℤ) : Option Bool :=
  if left ≤ z ∧ z < left + j then none else data z

/-- One native erasure enlarges the cleared interval by exactly one cell. -/
private lemma emCall_cleared_step (data : ℤ → Option Bool) (left : ℤ) (j : ℕ) :
    Function.update (emCallCleared data left j) (left + j) none =
      emCallCleared data left (j + 1) := by
  funext z
  by_cases hz : z = left + j
  · subst z; simp [emCallCleared]
  · rw [Function.update_of_ne hz]
    have hiff : (left ≤ z ∧ z < left + j) ↔
        (left ≤ z ∧ z < left + (j + 1 : ℕ)) := by omega
    simp only [emCallCleared, hiff]

/-- A marked finite work interval can be cleared natively despite arbitrary
blank holes in its data. Tape one marks the visited interval; tape two marks
only the origin. All three heads stay aligned. Return state three is silent. -/
private def emCallClearTM : FinTM Bool where
  k := 3
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q _ work => match q.val with
      | 0 => if work 1 = none then
          ⟨0, fun _ => (none, .pos), none, some 1⟩
        else ⟨0, fun _ => (none, .neg), none, some 0⟩
      | 1 => if work 1 = none then
          ⟨0, fun _ => (none, .neg), none, some 2⟩
        else ⟨0, fun i => (if i = 2 then none else some none, .pos), none, some 1⟩
      | 2 => if work 2 = none then
          ⟨0, fun _ => (none, .neg), none, some 2⟩
        else ⟨0, fun i => (if i = 2 then some none else none, 0), none, some 3⟩
      | _ => controlAction 0 (some 3) }

/-- The cleaner's three tapes hold data, the interval marker, and the origin
marker, respectively. The native input and physical output are untouched. -/
private def emCallClearCfg (w : List Bool) (p : Fin (w.length + 2)) (q : Fin 4)
    (data marks origin : ℤ → Option Bool) (h : ℤ) : Cfg 3 Bool emCallClearTM.State w :=
  ⟨some q, p, (fun i => match i.val with | 0 => data | 1 => marks | _ => origin), fun _ => h, []⟩

/-- The initial left scan reaches the marked interval's left end in `j+2`
steps, independently of blank holes in the data being cleared.
**Proof sketch.** Induct on the distance from the marked left endpoint. The marker,
independent of the data, forces every left move; its first blank triggers
the one-step return to the first marked cell. -/
private lemma emCall_clear_left (w : List Bool) (p : Fin (w.length + 2))
    (data : ℤ → Option Bool) (left : ℤ) (width : ℕ) :
    ∀ j, j < width →
      emCallClearTM.tm.runFrom
        (emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true]) (left + j))
        (j + 2) =
      emCallClearCfg w p 1 data (emCallInterval left width) (bufferTape [true]) left := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hmark : emCallInterval left width left = some true := by
      simp [emCallInterval]; omega
    have hblank : emCallInterval left width (left - 1) = none := by
      simp [emCallInterval]
    have hs : emCallClearTM.tm.step
        (emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true]) left) =
        emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true]) (left - 1) := by
      simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols,
        hmark, reduceCtorEq, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    have hs' : emCallClearTM.tm.step
        (emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true]) (left - 1)) =
        emCallClearCfg w p 1 data (emCallInterval left width) (bufferTape [true]) left := by
      simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols,
        hblank, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply]
    simpa only [Nat.cast_zero, add_zero] using
      show emCallClearTM.tm.step (emCallClearTM.tm.step
        (emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true]) left)) = _
        from by rw [hs, hs']
  | succ j ih =>
    intro hj
    have hmark : emCallInterval left width (left + (j + 1 : ℕ)) = some true := by
      simp [emCallInterval]; omega
    have hs : emCallClearTM.tm.step
        (emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true])
          (left + (j + 1 : ℕ))) =
        emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true]) (left + j) := by
      simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols,
        Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply]; omega
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Before any erasure, the data tape is unchanged. -/
private lemma emCall_cleared_zero (data : ℤ → Option Bool) (left : ℤ) :
    emCallCleared data left 0 = data := by
  funext z
  simp [emCallCleared]

/-- Clearing the full marked interval removes all data if there was no data
outside it. No assumption is made about holes or values inside the interval. -/
private lemma emCall_cleared_all (data : ℤ → Option Bool) (left : ℤ) (width : ℕ)
    (hdata : ∀ z, ¬(left ≤ z ∧ z < left + width) → data z = none) :
    emCallCleared data left width = fun _ => none := by
  funext z
  by_cases hz : left ≤ z ∧ z < left + width
  · simp [emCallCleared, hz]
  · simp [emCallCleared, hz, hdata z hz]

/-- The right scan clears data and its interval marker in lockstep while
leaving the separate origin marker intact.
**Proof sketch.** Induct on the number of remaining marked cells. Each transition clears
one data cell and its marker, advances both heads, and preserves the origin. -/
private lemma emCall_clear_scan (w : List Bool) (p : Fin (w.length + 2))
    (data : ℤ → Option Bool) (left : ℤ) (width : ℕ) :
    ∀ j, j ≤ width →
      emCallClearTM.tm.runFrom
        (emCallClearCfg w p 1 data (emCallInterval left width) (bufferTape [true]) left) j =
      emCallClearCfg w p 1 (emCallCleared data left j)
        (emCallCleared (emCallInterval left width) left j) (bufferTape [true]) (left + j) := by
  intro j
  induction j with
  | zero => intro _; simp [emCall_cleared_zero]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hmark : emCallCleared (emCallInterval left width) left j (left + j) = some true := by
      simp [emCallCleared, emCallInterval]; omega
    simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM,
      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hmark,
      reduceCtorEq, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      fin_cases i
      · simpa [Action.apply] using emCall_cleared_step data left j
      · simpa [Action.apply] using emCall_cleared_step (emCallInterval left width) left j
      · simp [Action.apply]
    · funext i; simp [Action.apply]; omega

/-- Removing the only origin marker makes its entire tape blank. -/
private lemma emCall_origin_erase :
    Function.update (bufferTape [true]) 0 none = fun _ => none := by
  funext z
  by_cases hz : z = 0
  · subst z; simp
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hn : 0 < z.toNat := by omega
      simp [bufferTape, h0, List.getElem?_eq_none (by simp; omega : [true].length ≤ z.toNat)]
    · simp [bufferTape, h0]

/-- Once the interval is erased, the surviving origin marker returns all
three heads to zero and is itself erased on the final transition.
**Proof sketch.** Induct on the distance to zero. The singleton origin marker distinguishes
the stopping cell; that transition erases the marker and retains all heads there. -/
private lemma emCall_clear_origin (w : List Bool) (p : Fin (w.length + 2)) :
    ∀ n : ℕ, emCallClearTM.tm.runFrom
      (emCallClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n) (n + 1) =
      emCallClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
  intro n
  induction n with
  | zero =>
    change (⟨0, (fun i : Fin 3 => (if i = 2 then some none else none, 0)),
      none, some (3 : Fin 4)⟩ : Action 3 Bool (Fin 4)).apply
      (emCallClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) 0) = _
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      fin_cases i <;> simp [Action.apply, emCallClearCfg, emCall_origin_erase]
    · funext i; simp [Action.apply, emCallClearCfg]
  | succ n ih =>
    have hblank : bufferTape [true] ((n + 1 : ℕ) : ℤ) = none := by
      rw [bufferTape_nat]; simp
    have hs : emCallClearTM.tm.step
        (emCallClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) (n + 1 : ℕ)) =
        emCallClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
      simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols,
        Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih

/-- Native cleanup of a finite marked work interval returns three blank tapes
with all heads at zero in a positive, linear number of steps.
**Proof sketch.** Scan left to the interval boundary, clear the entire interval
while moving right, then use the untouched origin marker to rewind. That last
marker is erased only when the heads are already at zero. All dispatches use
observed tape symbols; the interval bounds occur solely in the proof. -/
private lemma emCall_clear_run (w : List Bool) (p : Fin (w.length + 2))
    (data : ℤ → Option Bool) (left : ℤ) (width j : ℕ)
    (hleft : left ≤ 0) (hright : 0 < left + width) (hj : j < width)
    (hdata : ∀ z, ¬(left ≤ z ∧ z < left + width) → data z = none) :
    ∃ t, 0 < t ∧ t ≤ 3 * width + 4 ∧
      emCallClearTM.tm.runFrom
        (emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true]) (left + j)) t =
      emCallClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
  let n := (left + width - 1).toNat
  have hn : (n : ℤ) = left + width - 1 := by dsimp [n]; omega
  have hnlt : n < width := by omega
  have hscan := emCall_clear_scan w p data left width width (le_refl _)
  rw [emCall_cleared_all data left width hdata,
    emCall_cleared_all (emCallInterval left width) left width
      (by intro z hz; simp [emCallInterval, hz])] at hscan
  have hturn : emCallClearTM.tm.step
      (emCallClearCfg w p 1 (fun _ => none) (fun _ => none)
        (bufferTape [true]) (left + width)) =
      emCallClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
    simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols,
      Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]; omega
  have hforward : emCallClearTM.tm.runFrom
      (emCallClearCfg w p 1 data (emCallInterval left width) (bufferTape [true]) left)
      (width + 1) =
      emCallClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hscan, hturn]
  have hfirst : emCallClearTM.tm.runFrom
      (emCallClearCfg w p 0 data (emCallInterval left width) (bufferTape [true]) (left + j))
      ((j + 2) + (width + 1)) =
      emCallClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
    rw [MultiTapeTM.runFrom_add, emCall_clear_left w p data left width j hj, hforward]
  refine ⟨(j + 2) + (width + 1) + (n + 1), by omega, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, hfirst, emCall_clear_origin]

/-- A closed visited-cell interval; nonblank data may have arbitrary holes
inside this independently maintained marker. -/
private def emCallSpan (lo hi z : ℤ) : Option Bool :=
  if lo ≤ z ∧ z ≤ hi then some true else none

/-- Marking a cell at most one step outside a contiguous visited interval
extends exactly its appropriate endpoint. -/
private lemma emCall_span_extend (lo hi h : ℤ) (hord : lo ≤ hi)
    (hnear : lo - 1 ≤ h ∧ h ≤ hi + 1) :
    Function.update (emCallSpan lo hi) h (some true) = emCallSpan (min lo h) (max hi h) := by
  funext z
  by_cases hz : z = h
  · subst z
    simp [emCallSpan, min_le_right, le_max_right]
  · rw [Function.update_of_ne hz]
    have he : (lo ≤ z ∧ z ≤ hi) ↔ (min lo h ≤ z ∧ z ≤ max hi h) := by omega
    simp only [emCallSpan, he]

/-- Three separate banks hold simulated data, visited-cell markers, and
origin markers. Corresponding heads always move together. -/
private def emCallSlots {α : Type} {k : ℕ} (data marks origin : Fin k → α) :
    Fin (k + (k + k)) → α := Fin.addCases data (Fin.addCases marks origin)

/-- A tracked evaluator uses two native steps per source step. The first
performs the source action; the second marks the new head cells before
possibly halting. Initialization marks each origin in both marker banks.
Physical output remains the source output, ready for the capture wrapper. -/
private def emCallTrackTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + (M.k + M.k)
  State := M.State ⊕ (Option M.State ⊕ Unit)
  tm := {
    q₀ := .inr (.inr ())
    tr := fun q inp work => match q with
      | .inr (.inr ()) =>
        ⟨0, emCallSlots (fun _ => (none, 0))
          (fun _ => (some (some true), 0)) (fun _ => (some (some true), 0)),
          none, some (.inl M.tm.q₀)⟩
      | .inl q =>
        let a := M.tm.tr q inp (fun i => work (Fin.castAdd (M.k + M.k) i))
        ⟨a.inputTape, emCallSlots a.workTapes
          (fun i => (none, (a.workTapes i).2)) (fun i => (none, (a.workTapes i).2)),
          a.output, some (.inr (.inl a.state))⟩
      | .inr (.inl next) =>
        ⟨0, emCallSlots (fun _ => (none, 0))
          (fun _ => (some (some true), 0)) (fun _ => (none, 0)),
          none, next.map Sum.inl⟩ }

/-- A completed tracked source step, with source data unchanged and the
visited interval covering each current source head. -/
private def emCallTrackCfg (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) :
    Cfg (emCallTrackTM M).k Bool (emCallTrackTM M).State x :=
  ⟨c.state.map Sum.inl, c.inputPos,
    emCallSlots c.workTapes (fun i => emCallSpan (lo i) (hi i)) (fun _ => bufferTape [true]),
    emCallSlots c.workTapePos c.workTapePos c.workTapePos, c.output⟩

/-- The intermediate stamp state retains the previous interval markers while
the source data, input, heads, and emitted output already reflect its action. -/
private def emCallTrackMid (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) :
    Cfg (emCallTrackTM M).k Bool (emCallTrackTM M).State x :=
  { emCallTrackCfg M c lo hi with state := some (.inr (.inl c.state)) }

/-- The source-action microstep preserves the exact data simulation and moves
both marker heads by that same action. It includes any halting emission.
**Proof sketch.** Unfold the actual source action and compare all configuration fields.
Separate the three tape banks: data performs the source write, while both
marker banks move without writing and retain aligned heads. -/
private lemma emCall_track_action (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) (hc : c.state ≠ none) :
    (emCallTrackTM M).tm.step (emCallTrackCfg M c lo hi) =
      emCallTrackMid M (M.tm.step c) lo hi := by
  cases hs : c.state with
  | none => exact False.elim (hc hs)
  | some q =>
    have hin : (emCallTrackCfg M c lo hi).inputSymbol = c.inputSymbol := rfl
    have hwork : (fun i => (emCallTrackCfg M c lo hi).workTapeSymbols
        (Fin.castAdd (M.k + M.k) i)) = c.workTapeSymbols := by
      funext i
      simp [emCallTrackCfg, Cfg.workTapeSymbols, emCallSlots]
    have hs' : (emCallTrackCfg M c lo hi).state = some (.inl q) := by
      simp only [emCallTrackCfg, hs, Option.map_some]
    simp only [MultiTapeTM.step, hs', hs]
    change ((emCallTrackTM M).tm.tr (.inl q) _ _).apply _ = _
    dsimp only [emCallTrackTM]
    rw [hin, hwork]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [emCallTrackMid, emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [emCallTrackMid, emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [emCallTrackMid, emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [emCallTrackMid, emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat]

/-- The second microstep stamps every new current head, extending the
contiguous visited interval and halting only after those stamps are complete.
**Proof sketch.** Split the three tape banks. The source and origin tapes are unchanged;
writing the newly reached cell in the visited bank extends its interval
by the one-step head bound, before the stored successor state is dispatched. -/
private lemma emCall_track_stamp (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ)
    (hord : ∀ i, lo i ≤ hi i)
    (hnear : ∀ i, lo i - 1 ≤ c.workTapePos i ∧ c.workTapePos i ≤ hi i + 1) :
    (emCallTrackTM M).tm.step (emCallTrackMid M c lo hi) =
      emCallTrackCfg M c (fun i => min (lo i) (c.workTapePos i))
        (fun i => max (hi i) (c.workTapePos i)) := by
  simp only [MultiTapeTM.step, emCallTrackMid, emCallTrackTM]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j
        simpa [emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat] using
          emCall_span_extend (lo j) (hi j) (c.workTapePos j) (hord j) (hnear j)
      · intro j; simp [emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [emCallTrackCfg, emCallSlots, Action.apply, -Fin.natAdd_eq_addNat]
  · simp [emCallTrackCfg, Action.apply]

/-- Leftmost visited source-head position, including the initial origin. -/
private def emCallLo (M : FinTM Bool) (x : List Bool) : ℕ → Fin M.k → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun i => min (emCallLo M x t i)
      ((M.tm.runFrom (M.tm.initCfg x) (t + 1)).workTapePos i)

/-- Rightmost visited source-head position, including the initial origin. -/
private def emCallHi (M : FinTM Bool) (x : List Bool) : ℕ → Fin M.k → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun i => max (emCallHi M x t i)
      ((M.tm.runFrom (M.tm.initCfg x) (t + 1)).workTapePos i)

/-- The visited interval contains zero and the current head and has width
at most twice the elapsed source time plus one. -/
private lemma emCall_track_extent (M : FinTM Bool) (x : List Bool) :
    ∀ t (i : Fin M.k), emCallLo M x t i ≤ 0 ∧ 0 ≤ emCallHi M x t i ∧
      emCallLo M x t i ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ emCallHi M x t i ∧
      -(t : ℤ) ≤ emCallLo M x t i ∧ emCallHi M x t i ≤ t := by
  intro t
  induction t with
  | zero => intro i; simp [emCallLo, emCallHi, MultiTapeTM.initCfg, Cfg.init]
  | succ t ih =>
    intro i
    have hp := M.tm.workTapePos_step_le (M.tm.runFrom (M.tm.initCfg x) t) i
    rw [abs_le, ← MultiTapeTM.runFrom_succ_eq_step'] at hp
    have hh := ih i
    dsimp only [emCallLo, emCallHi]
    push_cast
    omega

/-- Every cell written by the source lies inside its visited interval.
The claim concerns actual writes and allows arbitrary blank cells inside it.
**Proof sketch.** Induct over the actual source trace. An unwritten cell retains its old
support bound; a newly written cell is the previous head, already in the
previous interval and therefore in the enlarged interval. -/
private lemma emCall_track_support (M : FinTM Bool) (x : List Bool) :
    ∀ t (i : Fin M.k) (z : ℤ),
      ¬(emCallLo M x t i ≤ z ∧ z ≤ emCallHi M x t i) →
        (M.tm.runFrom (M.tm.initCfg x) t).workTapes i z = none := by
  intro t
  induction t with
  | zero => intro i z hz; rfl
  | succ t ih =>
    intro i z hz
    have hb := emCall_track_extent M x t i
    have hz' : ¬(emCallLo M x t i ≤ z ∧ z ≤ emCallHi M x t i) := by
      dsimp only [emCallLo, emCallHi] at hz
      omega
    have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i := by omega
    rw [MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    cases hs : (M.tm.runFrom (M.tm.initCfg x) t).state with
    | none => exact ih i z hz'
    | some q =>
      dsimp only [Action.apply]
      cases hw : ((M.tm.tr q (M.tm.runFrom (M.tm.initCfg x) t).inputSymbol
        (M.tm.runFrom (M.tm.initCfg x) t).workTapeSymbols).workTapes i).1
      · exact ih i z hz'
      · dsimp only
        rw [Function.update_of_ne hne]
        exact ih i z hz'

/-- The singleton origin marker is the zero-width source trace's visited span. -/
private lemma emCall_span_zero : emCallSpan 0 0 = bufferTape [true] := by
  funext z
  by_cases hz : z = 0
  · subst z; rfl
  · have hspan : ¬(0 ≤ z ∧ z ≤ 0) := by omega
    by_cases hn : 0 ≤ z
    · have hlen : [true].length ≤ z.toNat := by simp; omega
      simp [emCallSpan, hspan, bufferTape, hn, List.getElem?_eq_none hlen]; omega
    · simp [emCallSpan, hspan, bufferTape, hn]

/-- A single native initialization step installs both origin markers while
leaving source work blank, the source input head at one, and output empty. -/
private lemma emCall_track_initial (M : FinTM Bool) (x : List Bool) :
    (emCallTrackTM M).tm.runFrom ((emCallTrackTM M).tm.initCfg x) 1 =
      emCallTrackCfg M (M.tm.initCfg x) (fun _ => 0) (fun _ => 0) := by
  change (emCallTrackTM M).tm.step ((emCallTrackTM M).tm.initCfg x) = _
  simp only [MultiTapeTM.step, MultiTapeTM.initCfg, Cfg.init, emCallTrackTM]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [Action.apply, emCallTrackCfg, emCallSlots, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simpa only [Action.apply, emCallTrackCfg, emCallSlots, Fin.addCases_left,
          Fin.addCases_right, emCall_span_zero, bufferTape_nil] using
            (bufferTape_append [] true).symm
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [Action.apply, emCallTrackCfg, emCallSlots, -Fin.natAdd_eq_addNat]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply, emCallTrackCfg, emCallSlots, -Fin.natAdd_eq_addNat]

/-- The tracked machine has the exact source configuration after two native
steps per source step, plus initialization. Its interval markers record the
actual trace, including after the source has halted.
**Proof sketch.** Initialization marks the origins. For a live source, its
action moves all three corresponding heads together, then the stamp expands
the visited interval by at most one cell. A halted source and its tracked
image are both absorbing, and the already-contained head changes neither bound. -/
private lemma emCall_track_run (M : FinTM Bool) (x : List Bool) :
    ∀ t, (emCallTrackTM M).tm.runFrom ((emCallTrackTM M).tm.initCfg x) (1 + 2 * t) =
      emCallTrackCfg M (M.tm.runFrom (M.tm.initCfg x) t) (emCallLo M x t) (emCallHi M x t) := by
  intro t
  induction t with
  | zero => simpa [emCallLo, emCallHi] using emCall_track_initial M x
  | succ t ih =>
    let c := M.tm.runFrom (M.tm.initCfg x) t
    have hb := emCall_track_extent M x t
    have hnext : M.tm.runFrom (M.tm.initCfg x) (t + 1) = M.tm.step c := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
    rw [show 1 + 2 * (t + 1) = (1 + 2 * t) + 2 by omega, MultiTapeTM.runFrom_add, ih]
    cases hs : c.state with
    | none =>
      have hl : emCallLo M x (t + 1) = emCallLo M x t := by
        funext i
        simp only [emCallLo, MultiTapeTM.runFrom_succ_eq_step']
        change min (emCallLo M x t i) ((M.tm.step c).workTapePos i) = _
        rw [MultiTapeTM.step_of_halt hs, min_eq_left (hb i).2.2.1]
      have hr : emCallHi M x (t + 1) = emCallHi M x t := by
        funext i
        simp only [emCallHi, MultiTapeTM.runFrom_succ_eq_step']
        change max (emCallHi M x t i) ((M.tm.step c).workTapePos i) = _
        rw [MultiTapeTM.step_of_halt hs, max_eq_left (hb i).2.2.2.1]
      have hhalt : (emCallTrackCfg M c (emCallLo M x t) (emCallHi M x t)).state = none := by
        simp only [emCallTrackCfg, hs, Option.map_none]
      rw [hl, hr, hnext]
      change (emCallTrackTM M).tm.runFrom (emCallTrackCfg M c _ _) 2 = emCallTrackCfg M (M.tm.step c) _ _
      rw [MultiTapeTM.runFrom_of_halt _ hhalt, MultiTapeTM.step_of_halt hs]
    | some q =>
      have hlive : c.state ≠ none := by rw [hs]; simp
      have hnear (i : Fin M.k) : emCallLo M x t i - 1 ≤ (M.tm.step c).workTapePos i ∧
          (M.tm.step c).workTapePos i ≤ emCallHi M x t i + 1 := by
        have hm := M.tm.workTapePos_step_le c i
        rw [abs_le] at hm
        have hh := hb i
        dsimp only [c] at hm ⊢
        omega
      change (emCallTrackTM M).tm.step ((emCallTrackTM M).tm.step (emCallTrackCfg M c _ _)) = _
      rw [emCall_track_action M c _ _ hlive,
        emCall_track_stamp M (M.tm.step c) _ _ (fun i => by have hh := hb i; omega) hnear]
      dsimp only [emCallLo, emCallHi]
      rw [hnext]

/-- The trace markers cost exactly two native steps per source step and one
initialization step. The output and halting judgment are unchanged. -/
private lemma emCall_track_computes (M : FinTM Bool) (x out : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x out T) :
    (emCallTrackTM M).ComputesInTime x out (1 + 2 * T) := by
  have hc := (computesInTime_iff M x out T).mp hM
  apply (computesInTime_iff _ _ _ _).mpr
  rw [emCall_track_run]
  exact ⟨by simp only [emCallTrackCfg, hc.1, Option.map_none], hc.2⟩

/-! Native accepting emission, adapted from the audited split emitter in
`Build/Primitives.lean` at the pinned base. The administrative bank is blank,
so it can enter after the new round's cleanup; no library source is changed. -/

/-- A closed visited span is the cleaner's half-open interval with exactly
one cell for each visited integer, including both endpoints. -/
private lemma emCall_span_interval (lo hi : ℤ) (h : lo ≤ hi) :
    emCallSpan lo hi = emCallInterval lo (hi - lo + 1).toNat := by
  funext z
  have hw : ((hi - lo + 1).toNat : ℤ) = hi - lo + 1 := by omega
  have he : (lo ≤ z ∧ z ≤ hi) ↔
      (lo ≤ z ∧ z < lo + ((hi - lo + 1).toNat : ℤ)) := by rw [hw]; omega
  simp only [emCallSpan, emCallInterval, he]

/-- Each actual source work tape, together with its tracked interval and
origin marker, satisfies the native cleaner's full restoration contract.
The common bound is linear in the actual elapsed source time.
**Proof sketch.** The trace invariant gives a visited interval containing the
head and zero, no nonblank cell outside it, and width at most `2T+1`.
Instantiate the proved interval cleaner, whose entire three-tape endpoint is
blank with every head zero, and absorb its cost into `6T+7`. -/
private lemma emCall_track_clearable (M : FinTM Bool) (x w : List Bool)
    (p : Fin (w.length + 2)) (T : ℕ) (i : Fin M.k) :
    ∃ t, 0 < t ∧ t ≤ 6 * T + 7 ∧
      emCallClearTM.tm.runFrom
        (emCallClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
          (emCallSpan (emCallLo M x T i) (emCallHi M x T i)) (bufferTape [true])
          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) t =
      emCallClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
  let lo := emCallLo M x T i
  let hi := emCallHi M x T i
  let h := (M.tm.runFrom (M.tm.initCfg x) T).workTapePos i
  let width := (hi - lo + 1).toNat
  let j := (h - lo).toNat
  have hb := emCall_track_extent M x T i
  have hw : (width : ℤ) = hi - lo + 1 := by dsimp only [width, hi, lo]; omega
  have hj : (j : ℤ) = h - lo := by dsimp only [j, h, lo]; omega
  have hwidth : width ≤ 2 * T + 1 := by dsimp only [hi, lo] at hw; omega
  have hpos : 0 < lo + width := by dsimp only [lo, hi] at hw ⊢; omega
  have hjlt : j < width := by dsimp only [h, lo, hi] at hw hj; omega
  have hdata : ∀ z, ¬(lo ≤ z ∧ z < lo + width) →
      (M.tm.runFrom (M.tm.initCfg x) T).workTapes i z = none := by
    intro z hz
    apply emCall_track_support M x T i z
    dsimp only [lo, hi] at hw hz
    omega
  obtain ⟨t, htpos, ht, hr⟩ := emCall_clear_run w p
    ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i) lo width j hb.1 hpos hjlt hdata
  refine ⟨t, htpos, by omega, ?_⟩
  have hhead : lo + j = h := by omega
  rw [hhead] at hr
  rw [emCall_span_interval _ _ (by have := hb; omega)]
  exact hr

/-- A phase with an absorbing return state can be cut at its actual first
return while retaining its complete configuration endpoint.
**Proof sketch.** Choose the least return-state visit. Absorption identifies
its configuration with the known bounded endpoint. The bound proves existence
and bounds the first visit; it is never used to dispatch native control. -/
private lemma emCall_first_entry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop) [DecidablePred stop]
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q := ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- Each tracked tape's native cleanup can dispatch at its actual positive
first return with the exact blank endpoint, never at the analysis deadline.
**Proof sketch.** Apply the per-tape bounded cleanup, then cut the absorbing return state
at its first visit. The initial left-scan state proves positivity, and
absorption preserves the complete blank endpoint. -/
private lemma emCall_clear_first (M : FinTM Bool) (x w : List Bool)
    (p : Fin (w.length + 2)) (T : ℕ) (i : Fin M.k) :
    ∃ t, 0 < t ∧ t ≤ 6 * T + 7 ∧
      (∀ j < t, (emCallClearTM.tm.runFrom
        (emCallClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
          (emCallSpan (emCallLo M x T i) (emCallHi M x T i)) (bufferTape [true])
          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) j).state ≠ some (3 : Fin 4)) ∧
      emCallClearTM.tm.runFrom
        (emCallClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
          (emCallSpan (emCallLo M x T i) (emCallHi M x T i)) (bufferTape [true])
          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) t =
        emCallClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
  obtain ⟨t, _, ht, hr⟩ := emCall_track_clearable M x w p T i
  obtain ⟨a, ha, hfirst, he⟩ := emCall_first_entry emCallClearTM.tm
    (fun q : Fin 4 => q = 3) _ _ t (by
      rintro z ⟨q, hz, rfl⟩
      unfold MultiTapeTM.step
      rw [hz]
      change (controlAction 0 (some (3 : Fin 4))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all) ⟨(3 : Fin 4), rfl, rfl⟩ hr
  have hpos : 0 < a := by
    by_contra h
    have hz : a = 0 := by omega
    have hh := congrArg Cfg.state he
    have hv := congrArg (fun q : Option (Fin 4) => q.map Fin.val) hh
    simp [hz, emCallClearCfg] at hv
  exact ⟨a, hpos, ha.trans ht, fun j hj hh => hfirst j hj ⟨(3 : Fin 4), hh, rfl⟩, he⟩

/-- After the source's actual halt, move to the native right input boundary
without altering its output or work tapes. The initial positive move handles
both blanks correctly, including the two distinct blanks of an empty input. -/
private def emCallRightTM (M : FinTM Bool) : FinTM Bool where
  k := M.k
  State := M.State ⊕ Bool
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl q =>
        let a := M.tm.tr q inp work
        { a with state := some ((a.state.map Sum.inl).getD (.inr false)) }
      | .inr false => controlAction .pos (some (.inr true))
      | .inr true => match inp with
        | some _ => controlAction .pos (some (.inr true))
        | none => controlAction 0 none }

/-- Before the right-boundary scan, the entire source configuration is
preserved, with its halt replaced by a live administrative state. -/
private def emCallRightCfg (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Cfg M.k Bool (emCallRightTM M).State x :=
  ⟨some ((c.state.map Sum.inl).getD (.inr false)), c.inputPos,
    c.workTapes, c.workTapePos, c.output⟩

/-- The wrapper follows each genuine source transition exactly, including its
halting emission; only the successor control encoding changes. -/
private lemma emCall_right_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (hc : c.state ≠ none) :
    (emCallRightTM M).tm.step (emCallRightCfg M c) = emCallRightCfg M (M.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hc hs)
  | some q =>
    have hstate : (emCallRightCfg M c).state = some (.inl q) := by
      simp only [emCallRightCfg, hs, Option.map_some, Option.getD_some]
    simp only [MultiTapeTM.step, hstate, hs]
    rfl

/-- The right-boundary wrapper simulates exactly up to the actual source halt.
No bound is substituted for the halting transition. -/
private lemma emCall_right_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (t : ℕ)
    (hlive : ∀ j < t, (M.tm.runFrom c j).state ≠ none) :
    (emCallRightTM M).tm.runFrom (emCallRightCfg M c) t =
      emCallRightCfg M (M.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      emCall_right_step M _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- A rightward scan configuration carries the completed source data and
output verbatim; its physical input position is the only moving field. -/
private def emCallRightScan (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q : Option Bool) (j : ℕ) (hj : j ≤ x.length) :
    Cfg M.k Bool (emCallRightTM M).State x :=
  ⟨q.map Sum.inr, ⟨j + 1, by omega⟩, c.workTapes, c.workTapePos, c.output⟩

/-- From any interior position, the native scan reaches the right blank and
halts silently. The scan does not confuse a blank work cell with an input end.
**Proof sketch.** Induct on the number of remaining native input cells. A live
cell costs one right move; the right blank costs the final silent halt. -/
private lemma emCall_right_scan (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    ∀ r j (hj : j ≤ x.length), j + r = x.length →
      (emCallRightTM M).tm.runFrom (emCallRightScan M c (some true) j hj) (r + 1) =
        emCallRightScan M c none x.length (le_refl _) := by
  intro r
  induction r with
  | zero =>
    intro j hj he
    have hje : j = x.length := by omega
    subst j
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have hin : (emCallRightScan M c (some true) x.length (le_refl _)).inputSymbol = none := by
      simp [emCallRightScan, Cfg.inputSymbol]
    simp only [MultiTapeTM.step, emCallRightScan, Option.map_some]
    change (match (emCallRightScan M c (some true) x.length (le_refl _)).inputSymbol with
      | some _ => controlAction .pos (some (Sum.inr true))
      | none => controlAction 0 none).apply _ = _
    rw [hin, controlAction_apply, moveInputPos_zero]
    rfl
  | succ r ih =>
    intro j hj he
    have hjlt : j < x.length := by omega
    have hin : (emCallRightScan M c (some true) j hj).inputSymbol = some (x[j]'hjlt) :=
      inputSymbolInner j (by simp [emCallRightScan, Nat.add_comm]) hjlt
    have hs : (emCallRightTM M).tm.step (emCallRightScan M c (some true) j hj) =
        emCallRightScan M c (some true) (j + 1) (by omega) := by
      simp only [MultiTapeTM.step, emCallRightScan, Option.map_some]
      change (match (emCallRightScan M c (some true) j hj).inputSymbol with
        | some _ => controlAction .pos (some (Sum.inr true))
        | none => controlAction 0 none).apply _ = _
      rw [hin, controlAction_apply]
      refine Cfg.ext rfl ?_ rfl rfl rfl
      exact moveInputPos_pos_of_ne_right _ (by simp; omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (j + 1) (by omega) (by omega)

/-- The completed source enters the right scan by a positive native move.
Clamping guarantees a position at least one even on empty input.
**Proof sketch.** The mandatory positive move reaches a position of at least one.
Apply the right-scan induction to its remaining distance; neither that move
nor the scan changes the completed source work tapes or output. -/
private lemma emCall_right_finish (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (hc : c.state = none) :
    ∃ t ≤ x.length + 2,
      (emCallRightTM M).tm.runFrom (emCallRightCfg M c) t =
        emCallRightScan M c none x.length (le_refl _) := by
  let p := moveInputPos c.inputPos .pos
  have hp : 1 ≤ p.val := by
    dsimp [p, moveInputPos]
    split <;> simp_all <;> omega
  let j := p.val - 1
  have hj : j ≤ x.length := by have := p.isLt; dsimp [j]; omega
  have hs : (emCallRightTM M).tm.step (emCallRightCfg M c) =
      emCallRightScan M c (some true) j hj := by
    simp only [MultiTapeTM.step, emCallRightCfg, hc, Option.map_none, Option.getD_none]
    change (controlAction .pos (some (Sum.inr true))).apply _ = _
    rw [controlAction_apply]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    apply Fin.ext
    change p.val = j + 1
    dsimp [j]; omega
  refine ⟨1 + (x.length - j + 1), by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, show (emCallRightTM M).tm.runFrom (emCallRightCfg M c) 1 = _ from hs]
  exact emCall_right_scan M c (x.length - j) j hj (by omega)

/-- Right-boundary normalization preserves the entire completed source
configuration, not just its output. This retains the tracked cleanup witnesses.
**Proof sketch.** Choose the actual first source halt. The native right scan
then costs at most `|x|+2`; absorb only the completed run to the advertised
budget. Source absorption identifies its work tapes with those at the original
deadline, including when that deadline exceeds the actual halt. -/
private lemma emCall_right_endpoint (M : FinTM Bool) (x : List Bool) (T : ℕ)
    (hc : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    (emCallRightTM M).tm.runFrom ((emCallRightTM M).tm.initCfg x) (T + x.length + 2) =
      emCallRightScan M (M.tm.runFrom (M.tm.initCfg x) T) none x.length (le_refl _) := by
  classical
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, hc⟩
  let t := Nat.find hex
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hex hc
  have hs : c.state = none := Nat.find_spec hex
  have hcT : M.tm.runFrom (M.tm.initCfg x) T = c := by
    rw [show T = t + (T - t) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hs]
  have hi : (emCallRightTM M).tm.initCfg x = emCallRightCfg M (M.tm.initCfg x) := rfl
  have hr := emCall_right_run M (M.tm.initCfg x) t (fun j hj => Nat.find_min hex hj)
  obtain ⟨r, hrle, hfinish⟩ := emCall_right_finish M c hs
  have hrun : (emCallRightTM M).tm.runFrom ((emCallRightTM M).tm.initCfg x) (t + r) =
      emCallRightScan M c none x.length (le_refl _) := by
    rw [hi, MultiTapeTM.runFrom_add, hr]
    exact hfinish
  have hle : t + r ≤ T + x.length + 2 := by omega
  rw [show T + x.length + 2 = (t + r) + (T + x.length + 2 - (t + r)) by omega,
    MultiTapeTM.runFrom_add, hrun, MultiTapeTM.runFrom_of_halt _ (by rfl), hcT]

/-- Every timed computation can finish at the right input boundary with only
linear extra time, preserving the source's complete output. -/
private lemma emCall_right_computes (M : FinTM Bool) (x out : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x out T) :
    (emCallRightTM M).ComputesInTime x out (T + x.length + 2) ∧
      ((emCallRightTM M).tm.runFrom ((emCallRightTM M).tm.initCfg x)
        (T + x.length + 2)).inputPos.val = x.length + 1 := by
  have hc := (computesInTime_iff M x out T).mp hM
  have he := emCall_right_endpoint M x T hc.1
  constructor
  · apply (computesInTime_iff _ _ _ _).mpr
    rw [he]
    exact ⟨rfl, hc.2⟩
  · rw [he]
    rfl

/-- A captured, tracked evaluator has an actual positive first return with
its full trace banks, complete output buffer, and candidate head at the right
boundary. It emits nothing to the physical output and fixes the physical input
head at one. The entry is the canonical prepared state-word configuration by
`emCall_eval_initial`. The full clean-call controller adds cleanup and finalization below.
**Proof sketch.** Track every source step, then normalize its virtual input
head after its actual halt. Capture this composite through its first completed
source state. Absorption equates that endpoint with the exact tracked trace at
the advertised deadline; the virtual right boundary fixes the candidate head
even for the empty word. The source deadline is never used as a native clock. -/
private lemma emCall_prepared_eval_first (M : FinTM Bool) (w s out : List Bool) (T : ℕ)
    (hM : M.ComputesInTime s out T) :
    let R := emCallRightTM (emCallTrackTM M)
    ∃ t, 0 < t ∧ t ≤ 1 + 2 * T + s.length + 2 ∧
      (∀ j < t, ((emCallEvalTM R).tm.runFrom
        (emCallEvalCfg (w := w) R (R.tm.initCfg s) true 1) j).state ≠ some (.inr ())) ∧
      (emCallEvalTM R).tm.runFrom
        (emCallEvalCfg (w := w) R (R.tm.initCfg s) true 1) t =
          emCallEvalCfg (w := w) R
            (emCallRightScan (emCallTrackTM M)
              (emCallTrackCfg M (M.tm.runFrom (M.tm.initCfg s) T)
                (emCallLo M s T) (emCallHi M s T)) none s.length (le_refl _)) false 1 := by
  dsimp only
  let R := emCallRightTM (emCallTrackTM M)
  let D := 1 + 2 * T + s.length + 2
  have htrack := emCall_track_computes M s out T hM
  have hright := (emCall_right_computes (emCallTrackTM M) s out (1 + 2 * T) htrack).1
  obtain ⟨t, ht, b, _, hh, _, hfirst, hr⟩ := emCall_eval_first R w s out D hright
  have hpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := by omega
    simp [ht0, MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg, Cfg.init] at hh
  have habs : R.tm.runFrom (R.tm.initCfg s) D = R.tm.runFrom (R.tm.initCfg s) t := by
    rw [show D = t + (D - t) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
  have hend := emCall_right_endpoint (emCallTrackTM M) s (1 + 2 * T)
    ((computesInTime_iff _ _ _ _).mp htrack).1
  rw [emCall_track_run] at hend
  refine ⟨t, hpos, ht, hfirst, ?_⟩
  rw [hr, ← habs, hend]
  rfl

/-- Relocate an action to an arbitrary fixed set of host tape slots. The
partial inverse selects active tapes; every inactive tape is stationary. -/
private def emCallAction {k l : ℕ} {S H : Type}
    (select : Fin l → Option (Fin k)) (emb : S → H) (a : Action k Bool S) :
    Action l Bool H :=
  ⟨a.inputTape, (fun i => match select i with
    | some j => a.workTapes j
    | none => (none, 0)), a.output, a.state.map emb⟩

/-- A relocated phase preserves all inactive host tapes and their heads.
Its output is the phase's actual physical output. -/
private def emCallCfg {k l : ℕ} {S H : Type} {x : List Bool}
    (select : Fin l → Option (Fin k)) (emb : S → H)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c : Cfg k Bool S x) : Cfg l Bool H x :=
  ⟨c.state.map emb, c.inputPos,
    (fun i => match select i with | some j => c.workTapes j | none => tapes i),
    (fun i => match select i with | some j => c.workTapePos j | none => heads i),
    c.output⟩

/-- Relocation commutes with applying one action, including its write, head
motion, and final emission. Inactive tape contents and positions are fixed. -/
private lemma emCall_apply {k l : ℕ} {S H : Type} {x : List Bool}
    (select : Fin l → Option (Fin k)) (emb : S → H)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (emCallAction select emb a).apply (emCallCfg select emb tapes heads c) =
      emCallCfg select emb tapes heads (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    cases hi : select i <;> simp [emCallAction, emCallCfg, Action.apply, hi]
  · funext i
    cases hi : select i <;> simp [emCallAction, emCallCfg, Action.apply, hi]

/-- Guarded phase relocation is exact through the first observed return.
**Proof sketch.** At each live source state the selected symbols agree by
the left-inverse law on tape indices. The host therefore takes the relocated
action. The action equality preserves all five configuration fields, and
induction composes the steps. The guard is required only before the endpoint. -/
private lemma emCall_relocate_run {k l : ℕ} {S H : Type} {x : List Bool}
    (src : MultiTapeTM k Bool S) (host : MultiTapeTM l Bool H)
    (index : Fin k → Fin l) (select : Fin l → Option (Fin k))
    (hinv : ∀ i, select (index i) = some i) (emb : S → H) (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work,
      host.tr (emb q) inp work =
        emCallAction select emb (src.tr q inp (fun i => work (index i))))
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c : Cfg k Bool S x) (t : ℕ)
    (hguard : ∀ j < t, ∀ q, (src.runFrom c j).state = some q → good q) :
    host.runFrom (emCallCfg select emb tapes heads c) t =
      emCallCfg select emb tapes heads (src.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hguard j (by omega))]
    let d := src.runFrom c t
    have he : src.runFrom c (t + 1) = src.step d :=
      by rw [MultiTapeTM.runFrom_succ_eq_step']
    rw [he]
    change host.step (emCallCfg select emb tapes heads d) =
      emCallCfg select emb tapes heads (src.step d)
    cases hs : d.state with
    | none =>
      have hs' : (emCallCfg select emb tapes heads d).state = none := by
        simp [emCallCfg, hs]
      rw [MultiTapeTM.step_of_halt hs', MultiTapeTM.step_of_halt hs]
    | some q =>
      have hsymbols : (fun i => (emCallCfg select emb tapes heads d).workTapeSymbols
          (index i)) = d.workTapeSymbols := by
        funext i
        simp [emCallCfg, Cfg.workTapeSymbols, hinv]
      have hs' : (emCallCfg select emb tapes heads d).state = some (emb q) := by
        simp [emCallCfg, hs]
      simp only [MultiTapeTM.step, hs', hs]
      rw [hagree q (hguard t (by omega) q hs), hsymbols]
      exact emCall_apply select emb tapes heads _ d

/-- Two-tape result finalization. The argument and capture enter at their
known right blanks. Install mode replaces the argument; emit mode preserves
it and forwards the captured result. Both modes erase and rewind capture. -/
private def emCallFinishTM (emit : Bool) : FinTM Bool where
  k := 2
  State := Fin 6
  tm := {
    q₀ := 0
    tr := fun q _ work => match q.val with
      | 0 => ⟨0, fun i => (none, if i = 0 then .neg else 0), none, some 1⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun i =>
            (if i = 0 ∧ emit = false then some none else none,
              if i = 0 then .neg else 0), none, some 1⟩
        | none => ⟨0, fun i => (none, if i = 0 then .pos else .neg), none, some 2⟩
      | 2 => match work 1 with
        | some _ => ⟨0, fun i => (none, if i = 0 then 0 else .neg), none, some 2⟩
        | none => ⟨0, fun i => (none, if i = 0 then 0 else .pos), none, some 3⟩
      | 3 => match work 1 with
        | some b => ⟨0, fun i =>
            (if i = 0 ∧ emit = false then some (some b) else none,
              if i = 0 ∧ emit = true then 0 else .pos),
            if emit then some b else none, some 3⟩
        | none => ⟨0, fun i =>
            (none, if i = 0 ∧ emit = true then 0 else .neg), none, some 4⟩
      | 4 => match work 1 with
        | some _ => ⟨0, fun i => (if i = 0 then none else some none,
            if i = 0 ∧ emit = true then 0 else .neg), none, some 4⟩
        | none => ⟨0, fun i =>
            (none, if i = 0 ∧ emit = true then 0 else .pos), none, some 5⟩
      | _ => controlAction 0 (some 5) }

/-- The result phase's full configuration, retaining an arbitrary physical
input position. The two work heads are independent until install replay. -/
private def emCallFinishCfg (emit : Bool) (x : List Bool) (p : Fin (x.length + 2))
    (q : Fin 6) (arg cap : ℤ → Option Bool) (a b : ℤ) (out : List Bool) :
    Cfg 2 Bool (emCallFinishTM emit).State x :=
  ⟨some q, p, (fun i => if i = 0 then arg else cap),
    (fun i => if i = 0 then a else b), out⟩

/-- A word whose suffix has been erased is precisely its surviving prefix. -/
private lemma emCall_erase_last (w : List Bool) (b : Bool) :
    Function.update (bufferTape (w ++ [b])) w.length none = bufferTape w := by
  rw [bufferTape_append, Function.update_idem]
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp [bufferTape_nat]
  · simp [Function.update_of_ne hz]

/-- Scanning the argument leftwards erases its suffix in install mode and
leaves the entire word intact in emit mode. The right blank fixes the side,
so an empty argument follows the same route.
**Proof sketch.** Induct on the remaining prefix length. The current cell is
the prefix's final bit; install mode removes it, while emit mode keeps it.
The blank immediately to the left turns the controller to the capture pass. -/
private lemma emCall_finish_arg (emit : Bool) (x arg cap : List Bool)
    (p : Fin (x.length + 2)) : ∀ pre suf : List Bool, arg = pre ++ suf →
    (emCallFinishTM emit).tm.runFrom
      (emCallFinishCfg emit x p 1
        (bufferTape (if emit then arg else pre)) (bufferTape cap)
        ((pre.length : ℤ) - 1) cap.length []) (pre.length + 1) =
      emCallFinishCfg emit x p 2 (bufferTape (if emit then arg else []))
        (bufferTape cap) 0 ((cap.length : ℤ) - 1) [] := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro suf harg
    have hblank : bufferTape (if emit then arg else []) (-1) = none := by
      simp [bufferTape]
    simp only [List.length_nil, Nat.cast_zero, zero_sub, zero_add]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
      Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hblank]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; fin_cases i <;> simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
  | append_singleton pre b ih =>
    intro suf harg
    have hread : bufferTape (if emit then arg else pre ++ [b]) pre.length = some b := by
      cases emit
      · simp [bufferTape_nat]
      · rw [harg, bufferTape_nat]
        simp [List.append_assoc]
    have hs : (emCallFinishTM emit).tm.step
        (emCallFinishCfg emit x p 1
          (bufferTape (if emit then arg else pre ++ [b])) (bufferTape cap)
          pre.length cap.length []) =
        emCallFinishCfg emit x p 1 (bufferTape (if emit then arg else pre))
          (bufferTape cap) ((pre.length : ℤ) - 1) cap.length [] := by
      simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
        Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i; fin_cases i <;> cases emit <;>
          simp [Action.apply, emCallFinishCfg, emCall_erase_last]
      · funext i; fin_cases i <;> simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
    have hlen : ((pre ++ [b]).length : ℤ) - 1 = pre.length := by simp
    rw [hlen, List.length_append, List.length_singleton,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (b :: suf) (by simpa [List.append_assoc] using harg)

/-- Rewind a contiguous captured word from its known right side. The capture
is retained for the following forward pass; the argument head stays zero.
**Proof sketch.** Induct on the distance from the capture head to its left
boundary. Each nonblank cell moves the head left without writing. At the
left blank, the next transition moves to zero and selects forward replay. -/
private lemma emCall_finish_rewind (emit : Bool) (x cap : List Bool)
    (p : Fin (x.length + 2)) (arg : ℤ → Option Bool) :
    ∀ pre suf : List Bool, cap = pre ++ suf →
    (emCallFinishTM emit).tm.runFrom
      (emCallFinishCfg emit x p 2 arg (bufferTape cap) 0
        ((pre.length : ℤ) - 1) []) (pre.length + 1) =
      emCallFinishCfg emit x p 3 arg (bufferTape cap) 0 0 [] := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro suf hcap
    have hblank : bufferTape cap (-1) = none := by simp [bufferTape]
    simp only [List.length_nil, Nat.cast_zero, zero_sub, zero_add]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
      Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hblank]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; fin_cases i <;> simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
  | append_singleton pre b ih =>
    intro suf hcap
    have hread : bufferTape cap pre.length = some b := by
      rw [hcap, bufferTape_nat]; simp [List.append_assoc]
    have hs : (emCallFinishTM emit).tm.step
        (emCallFinishCfg emit x p 2 arg (bufferTape cap) 0 pre.length []) =
        emCallFinishCfg emit x p 2 arg (bufferTape cap) 0 ((pre.length : ℤ) - 1) [] := by
      simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
        Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
    have hlen : ((pre ++ [b]).length : ℤ) - 1 = pre.length := by simp
    rw [hlen, List.length_append, List.length_singleton,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (b :: suf) (by simpa [List.append_assoc] using hcap)

/-- Transfer the capture in order, either to the argument tape or to physical
output. Capture itself remains intact until the erase-and-rewind pass.
**Proof sketch.** Induct on the untransferred suffix. Each live cell either
appends one work-tape bit or emits one bit. At the right blank, turn both
install heads, or only the emit capture head, left for cleanup. -/
private lemma emCall_finish_transfer (emit : Bool) (x arg cap : List Bool)
    (p : Fin (x.length + 2)) : ∀ rest pre : List Bool, cap = pre ++ rest →
    (emCallFinishTM emit).tm.runFrom
      (emCallFinishCfg emit x p 3 (bufferTape (if emit then arg else pre))
        (bufferTape cap) (if emit then 0 else pre.length) pre.length
        (if emit then pre else [])) (rest.length + 1) =
      emCallFinishCfg emit x p 4 (bufferTape (if emit then arg else cap))
        (bufferTape cap) (if emit then 0 else (cap.length : ℤ) - 1)
        ((cap.length : ℤ) - 1) (if emit then cap else []) := by
  intro rest
  induction rest with
  | nil =>
    intro pre hcap
    have he : cap = pre := by simpa using hcap
    subst cap
    simp only [List.append_nil, List.length_nil]
    have hblank : bufferTape pre pre.length = none := by simp [bufferTape_nat]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
      Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hblank]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ (by simp [Action.apply])
    funext i; fin_cases i <;> cases emit <;>
      simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
  | cons b rest ih =>
    intro pre hcap
    have hread : bufferTape cap pre.length = some b := by
      rw [hcap, bufferTape_nat]; simp
    have hs : (emCallFinishTM emit).tm.step
        (emCallFinishCfg emit x p 3 (bufferTape (if emit then arg else pre))
          (bufferTape cap) (if emit then 0 else pre.length) pre.length
          (if emit then pre else [])) =
        emCallFinishCfg emit x p 3 (bufferTape (if emit then arg else pre ++ [b]))
          (bufferTape cap) (if emit then 0 else (pre ++ [b]).length)
          (pre ++ [b]).length (if emit then pre ++ [b] else []) := by
      simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
        Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
      · funext i; fin_cases i <;> cases emit <;>
          simp [Action.apply, emCallFinishCfg, bufferTape_append]
      · funext i; fin_cases i <;> cases emit <;>
          simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
      · cases emit <;> simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (pre ++ [b]) (by simpa [List.append_assoc] using hcap)

/-- Erase capture while returning its head to zero. In install mode the
result head moves with it; in emit mode the argument head stays at zero.
**Proof sketch.** Remove the last remaining captured bit and induct on the
prefix length. The install head follows the same backward moves; the emit
head is stationary. The final left-blank transition restores zero positions. -/
private lemma emCall_finish_erase (emit : Bool) (x : List Bool)
    (p : Fin (x.length + 2)) (arg : ℤ → Option Bool) (out : List Bool) :
    ∀ pre : List Bool, (emCallFinishTM emit).tm.runFrom
      (emCallFinishCfg emit x p 4 arg (bufferTape pre)
        (if emit then 0 else (pre.length : ℤ) - 1) ((pre.length : ℤ) - 1) out)
        (pre.length + 1) =
      emCallFinishCfg emit x p 5 arg (fun _ => none) 0 0 out := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, zero_sub, zero_add, bufferTape_nil]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
      Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ (by simp [Action.apply])
    funext i; fin_cases i <;> cases emit <;> simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
  | append_singleton pre b ih =>
    have hread : bufferTape (pre ++ [b]) pre.length = some b := by simp [bufferTape_nat]
    have hs : (emCallFinishTM emit).tm.step
        (emCallFinishCfg emit x p 4 arg (bufferTape (pre ++ [b]))
          (if emit then 0 else pre.length) pre.length out) =
        emCallFinishCfg emit x p 4 arg (bufferTape pre)
          (if emit then 0 else (pre.length : ℤ) - 1) ((pre.length : ℤ) - 1) out := by
      simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
        Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [Action.apply])
      · funext i; fin_cases i <;> simp [Action.apply, emCallFinishCfg, emCall_erase_last]
      · funext i; fin_cases i <;> cases emit <;>
          simp [Action.apply, emCallFinishCfg, sub_eq_add_neg]
    have hlen : ((pre ++ [b]).length : ℤ) - 1 = pre.length := by simp
    rw [hlen, List.length_append, List.length_singleton,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih

/-- Finalize a captured result with a full clean endpoint. The exact cost is
argument length plus three result passes plus five dispatches; empty words
are included.
**Proof sketch.** From the known right blanks, rewind (and optionally erase)
the argument, rewind capture, transfer capture, then erase and rewind capture.
The install result is kept, or the emit argument is kept and the result is
physical output. Each phase equality includes both tapes and both heads. -/
private lemma emCall_finish_run (emit : Bool) (x arg cap : List Bool)
    (p : Fin (x.length + 2)) :
    (emCallFinishTM emit).tm.runFrom
      (emCallFinishCfg emit x p 0 (bufferTape arg) (bufferTape cap)
        arg.length cap.length []) (arg.length + 3 * cap.length + 5) =
      emCallFinishCfg emit x p 5 (bufferTape (if emit then arg else cap))
        (fun _ => none) 0 0 (if emit then cap else []) := by
  have hs : (emCallFinishTM emit).tm.step
      (emCallFinishCfg emit x p 0 (bufferTape arg) (bufferTape cap)
        arg.length cap.length []) =
      emCallFinishCfg emit x p 1 (bufferTape arg) (bufferTape cap)
        ((arg.length : ℤ) - 1) cap.length [] := by
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; fin_cases i <;> simp [MultiTapeTM.step, emCallFinishCfg,
      emCallFinishTM, Action.apply, sub_eq_add_neg]
  have harg := emCall_finish_arg emit x arg cap p arg [] (by simp)
  have hrew := emCall_finish_rewind emit x cap p
    (bufferTape (if emit then arg else [])) cap [] (by simp)
  have htransfer := emCall_finish_transfer emit x arg cap p cap [] (by simp)
  have herase := emCall_finish_erase emit x p
    (bufferTape (if emit then arg else cap)) (if emit then cap else []) cap
  simp only [ite_self] at harg
  simp only [List.length_nil, Nat.cast_zero, ite_self] at htransfer
  have hsrun : (emCallFinishTM emit).tm.runFrom
      (emCallFinishCfg emit x p 0 (bufferTape arg) (bufferTape cap)
        arg.length cap.length []) 1 =
      emCallFinishCfg emit x p 1 (bufferTape arg) (bufferTape cap)
        ((arg.length : ℤ) - 1) cap.length [] := by
    simpa only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero] using hs
  have h1 := (emCallFinishTM emit).tm.runFrom_add
    (emCallFinishCfg emit x p 0 (bufferTape arg) (bufferTape cap)
      arg.length cap.length []) 1 (arg.length + 1)
  rw [hsrun, harg] at h1
  have h2 := (emCallFinishTM emit).tm.runFrom_add
    (emCallFinishCfg emit x p 0 (bufferTape arg) (bufferTape cap)
      arg.length cap.length []) (1 + (arg.length + 1)) (cap.length + 1)
  rw [h1, hrew] at h2
  have h3 := (emCallFinishTM emit).tm.runFrom_add
    (emCallFinishCfg emit x p 0 (bufferTape arg) (bufferTape cap)
      arg.length cap.length []) (1 + (arg.length + 1) + (cap.length + 1)) (cap.length + 1)
  rw [h2, htransfer] at h3
  have h4 := (emCallFinishTM emit).tm.runFrom_add
    (emCallFinishCfg emit x p 0 (bufferTape arg) (bufferTape cap)
      arg.length cap.length [])
    (1 + (arg.length + 1) + (cap.length + 1) + (cap.length + 1)) (cap.length + 1)
  rw [h3, herase] at h4
  convert h4 using 1 <;> congr 1 <;> omega

/-- The prepared source phase has one genuine argument tape, three tracked
banks, and one capture tape, even when the source machine has no work tapes. -/
private abbrev emCallSource (M : FinTM Bool) : FinTM Bool :=
  emCallEvalTM (emCallRightTM (emCallTrackTM M))

/-- Fixed control for evaluation, successive triple cleanups, and finalization.
The extra bank index is the dispatch after all source banks are clean. -/
private abbrev emCallState (M : FinTM Bool) :=
  (emCallSource M).State ⊕ ((Fin (M.k + 1) × Fin 4) ⊕ Fin 6)

/-- Physical index of a source tape's data, interval, or origin component. -/
private def emCallTripleIndex (M : FinTM Bool) (i : Fin M.k) (r : Fin 3) :
    Fin (emCallSource M).k :=
  match r.val with
  | 0 => ⟨1 + i.val, by have := i.isLt; dsimp [emCallSource, emCallEvalTM,
      bufferedCompTM, emCallIdleTM, emCallRightTM, emCallTrackTM]; omega⟩
  | 1 => ⟨1 + M.k + i.val, by have := i.isLt; dsimp [emCallSource, emCallEvalTM,
      bufferedCompTM, emCallIdleTM, emCallRightTM, emCallTrackTM]; omega⟩
  | _ => ⟨1 + M.k + M.k + i.val, by have := i.isLt; dsimp [emCallSource, emCallEvalTM,
      bufferedCompTM, emCallIdleTM, emCallRightTM, emCallTrackTM]; omega⟩

/-- Partial inverse of the triple layout; all other host tapes are inactive. -/
private def emCallTripleSelect (M : FinTM Bool) (i : Fin M.k)
    (j : Fin (emCallSource M).k) : Option (Fin 3) :=
  if j.val = 1 + i.val then some 0 else
  if j.val = 1 + M.k + i.val then some 1 else
  if j.val = 1 + M.k + M.k + i.val then some 2 else none

/-- The three slots of a genuine source tape are distinct and select back
to their corresponding cleaner tape. -/
private lemma emCall_triple_inverse (M : FinTM Bool) (i : Fin M.k) (r : Fin 3) :
    emCallTripleSelect M i (emCallTripleIndex M i r) = some r := by
  have hk : 0 < M.k := Nat.zero_lt_of_lt i.isLt
  fin_cases r <;> simp [emCallTripleSelect, emCallTripleIndex, show M.k ≠ 0 by omega]
  all_goals repeat first | rfl | omega | split
  all_goals repeat first | rfl | omega | split

/-- Argument and result capture occupy the first and last physical tapes. -/
private def emCallPairIndex (M : FinTM Bool) (i : Fin 2) : Fin (emCallSource M).k :=
  if i = 0 then ⟨0, by dsimp [emCallSource, emCallEvalTM]; omega⟩
  else Fin.last (bufferedCompTM emCallIdleTM (emCallRightTM (emCallTrackTM M))).k

/-- Select only the argument and capture from a full call layout. -/
private def emCallPairSelect (M : FinTM Bool) (j : Fin (emCallSource M).k) :
    Option (Fin 2) :=
  if j.val = 0 then some 0 else
  if j.val = (bufferedCompTM emCallIdleTM (emCallRightTM (emCallTrackTM M))).k
    then some 1 else none

/-- The finalizer's two tape indices satisfy the relocation inverse law. -/
private lemma emCall_pair_inverse (M : FinTM Bool) (i : Fin 2) :
    emCallPairSelect M (emCallPairIndex M i) = some i := by
  fin_cases i <;> simp [emCallPairIndex, emCallPairSelect, emCallIdleTM,
    bufferedCompTM, emCallRightTM, emCallTrackTM]

/-- Native clean-call controller. Evaluation is captured at its actual
return; each tracked triple is cleared to its observed return; the last
phase installs or emits the capture and erases administrative storage.
No deadline or source running time is part of this transition table. -/
private def emCallTM (M : FinTM Bool) (emit : Bool) : FinTM Bool where
  k := (emCallSource M).k
  State := emCallState M
  tm := {
    q₀ := .inl (.inl (.inr (.inr ((emCallRightTM (emCallTrackTM M)).tm.q₀, true))))
    tr := fun q inp work => match q with
      | .inl q =>
        if q = .inr () then controlAction 0 (some (.inr (.inl (0, 0))))
        else emCallAction (fun i => some i) Sum.inl ((emCallSource M).tm.tr q inp work)
      | .inr (.inl (i, q)) =>
        if hi : i.val < M.k then
          if q = 3 then controlAction 0 (some (.inr (.inl (⟨i.val + 1, by omega⟩, 0))))
          else emCallAction (emCallTripleSelect M ⟨i.val, hi⟩)
            (fun s => .inr (.inl (i, s)))
            (emCallClearTM.tm.tr q inp (fun r => work (emCallTripleIndex M ⟨i.val, hi⟩ r)))
        else controlAction 0 (some (.inr (.inr 0)))
      | .inr (.inr q) => emCallAction (emCallPairSelect M)
          (fun s => .inr (.inr s))
          ((emCallFinishTM emit).tm.tr q inp (fun r => work (emCallPairIndex M r))) }

/-- Canonical tape layout for the call: argument, data bank, visited bank,
origin bank, capture. The same layout is used for contents and head positions. -/
private def emCallLayout {α : Type} (M : FinTM Bool) (arg cap : α)
    (data marks origin : Fin M.k → α) : Fin (emCallSource M).k → α :=
  Fin.addCases (tapeBlocks (fun i : Fin 0 => i.elim0) arg
    (emCallSlots data marks origin)) (fun _ : Fin 1 => cap)

/-- An index in the call layout is either an argument slot, one of the three
source-bank slots, or the capture slot. -/
private lemma emCall_layout_cases (M : FinTM Bool) (j : Fin (emCallSource M).k) :
    j = emCallPairIndex M 0 ∨ j = emCallPairIndex M 1 ∨
      ∃ i r, j = emCallTripleIndex M i r := by
  have hj : j.val < (1 + (M.k + (M.k + M.k))) + 1 := by
    simpa only [emCallSource, emCallEvalTM, bufferedCompTM, emCallIdleTM,
      emCallRightTM, emCallTrackTM, Nat.zero_add] using j.isLt
  by_cases hz : j.val = 0
  · left; apply Fin.ext; simpa [emCallPairIndex] using hz
  · right
    by_cases hc : j.val = 1 + (M.k + (M.k + M.k))
    · left; apply Fin.ext; simpa [emCallPairIndex, bufferedCompTM, emCallIdleTM,
        emCallRightTM, emCallTrackTM] using hc
    · right
      by_cases h1 : j.val < 1 + M.k
      · refine ⟨⟨j.val - 1, by omega⟩, 0, ?_⟩
        apply Fin.ext; dsimp [emCallTripleIndex]; omega
      · by_cases h2 : j.val < 1 + M.k + M.k
        · refine ⟨⟨j.val - (1 + M.k), by omega⟩, 1, ?_⟩
          apply Fin.ext; dsimp [emCallTripleIndex]; omega
        · refine ⟨⟨j.val - (1 + M.k + M.k), by omega⟩, 2, ?_⟩
          apply Fin.ext; dsimp [emCallTripleIndex]; omega

/-- Projecting a cleaner component from the full layout gives exactly its
source data, interval, or origin value.
**Proof sketch.** Express the bank index through the nested finite sums of
the argument, tracked source banks, and capture. The three possible local
indices then project the data, interval marker, and origin marker directly. -/
private lemma emCall_layout_triple {α : Type} (M : FinTM Bool) (arg cap : α)
    (data marks origin : Fin M.k → α) (i : Fin M.k) (r : Fin 3) :
    emCallLayout M arg cap data marks origin (emCallTripleIndex M i r) =
      match r.val with | 0 => data i | 1 => marks i | _ => origin i := by
  fin_cases r
  · have he : emCallTripleIndex M i 0 =
        Fin.castAdd 1 (Fin.natAdd 0 (Fin.natAdd 1 (Fin.castAdd (M.k + M.k) i))) := by
      apply Fin.ext; simp [emCallTripleIndex]
    erw [he]
    simp only [emCallLayout, tapeBlocks, Fin.addCases_left]
    erw [Fin.addCases_right, Fin.addCases_right]
    simp only [emCallSlots, Fin.addCases_left, Fin.addCases_right]
  · have he : emCallTripleIndex M i 1 =
        Fin.castAdd 1 (Fin.natAdd 0 (Fin.natAdd 1 (Fin.natAdd M.k (Fin.castAdd M.k i)))) := by
      apply Fin.ext; simp [emCallTripleIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    erw [he]
    simp only [emCallLayout, tapeBlocks, Fin.addCases_left]
    erw [Fin.addCases_right, Fin.addCases_right]
    simp only [emCallSlots, Fin.addCases_left, Fin.addCases_right]
  · have he : emCallTripleIndex M i 2 =
        Fin.castAdd 1 (Fin.natAdd 0 (Fin.natAdd 1 (Fin.natAdd M.k (Fin.natAdd M.k i)))) := by
      apply Fin.ext; simp [emCallTripleIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    erw [he]
    simp only [emCallLayout, tapeBlocks, Fin.addCases_left]
    erw [Fin.addCases_right, Fin.addCases_right]
    simp only [emCallSlots, Fin.addCases_left, Fin.addCases_right]

/-- Projecting the two administrative slots gives the argument and capture. -/
private lemma emCall_layout_pair {α : Type} (M : FinTM Bool) (arg cap : α)
    (data marks origin : Fin M.k → α) (i : Fin 2) :
    emCallLayout M arg cap data marks origin (emCallPairIndex M i) =
      if i = 0 then arg else cap := by
  fin_cases i <;> simp [emCallLayout, emCallPairIndex, tapeBlocks, emCallSlots,
    Fin.addCases, bufferedCompTM, emCallIdleTM, emCallRightTM, emCallTrackTM]

/-- A cleaner does not select either administrative tape. -/
private lemma emCall_triple_pair (M : FinTM Bool) (i : Fin M.k) (r : Fin 2) :
    emCallTripleSelect M i (emCallPairIndex M r) = none := by
  have hi := i.isLt
  fin_cases r <;> simp [emCallTripleSelect, emCallPairIndex, bufferedCompTM,
    emCallIdleTM, emCallRightTM, emCallTrackTM]
  all_goals repeat first | rfl | omega | split
  all_goals repeat first | rfl | omega | split
  all_goals repeat first | rfl | omega | split

/-- A triple selector acts only on the named source bank. -/
private lemma emCall_triple_other (M : FinTM Bool) (i j : Fin M.k) (r : Fin 3) :
    emCallTripleSelect M i (emCallTripleIndex M j r) =
      if j = i then some r else none := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases he : j = i
  · subst j; simp [emCall_triple_inverse]
  · have hv : j.val ≠ i.val := fun h => he (Fin.ext h)
    fin_cases r <;> simp [emCallTripleSelect, emCallTripleIndex, he, hv]
    all_goals repeat first | rfl | omega | split
    all_goals repeat first | rfl | omega | split
    all_goals repeat first | rfl | omega | split

/-- The two-tape finalizer never acts on tracked source storage. -/
private lemma emCall_pair_triple (M : FinTM Bool) (i : Fin M.k) (r : Fin 3) :
    emCallPairSelect M (emCallTripleIndex M i r) = none := by
  have hi := i.isLt
  fin_cases r <;> simp [emCallPairSelect, emCallTripleIndex, bufferedCompTM,
    emCallIdleTM, emCallRightTM, emCallTrackTM]
  all_goals repeat first | rfl | omega | split

/-- Full host frame during cleanup. The argument and capture are retained
at their known right boundaries while all three source banks are normalized. -/
private def emCallFrame (M : FinTM Bool) (emit : Bool) (x arg cap : List Bool)
    (q : emCallState M) (data marks origin : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) : Cfg (emCallTM M emit).k Bool (emCallTM M emit).State x :=
  ⟨some q, 1, emCallLayout M (bufferTape arg) (bufferTape cap) data marks origin,
    emCallLayout M arg.length cap.length heads heads heads, []⟩

/-- The prefix of cleaned source banks is blank, the remaining banks retain
the source's exact halted trace. The native time is analysis data only. -/
private def emCallBankFrame (M : FinTM Bool) (emit : Bool) (x arg cap : List Bool)
    (T j : ℕ) (q : emCallState M) :
    Cfg (emCallTM M emit).k Bool (emCallTM M emit).State x :=
  emCallFrame M emit x arg cap q
    (fun i => if i.val < j then fun _ => none else
      (M.tm.runFrom (M.tm.initCfg arg) T).workTapes i)
    (fun i => if i.val < j then fun _ => none else emCallSpan (emCallLo M arg T i) (emCallHi M arg T i))
    (fun i => if i.val < j then fun _ => none else bufferTape [true])
    (fun i => if i.val < j then 0 else (M.tm.runFrom (M.tm.initCfg arg) T).workTapePos i)

/-- Embedding one cleaner at the current bank reproduces the full bank frame.
Every other bank and both administrative tapes are retained exactly.
**Proof sketch.** Extensionality reduces the claim to individual tape slots.
The active triple uses the relocation inverse law; every other triple, the
argument, and the capture use the disjointness laws and are unchanged. -/
private lemma emCall_bank_initial (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (i : Fin M.k) :
    let frame := emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))
    emCallCfg (emCallTripleSelect M i) (fun q => .inr (.inl (i.castSucc, q)))
      frame.workTapes frame.workTapePos
      (emCallClearCfg x 1 0 ((M.tm.runFrom (M.tm.initCfg arg) T).workTapes i)
        (emCallSpan (emCallLo M arg T i) (emCallHi M arg T i)) (bufferTape [true])
        ((M.tm.runFrom (M.tm.initCfg arg) T).workTapePos i)) = frame := by
  dsimp only
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
    · subst j; simp [emCallCfg, emCall_triple_pair]
    · subst j; simp [emCallCfg, emCall_triple_pair]
    · subst j
      by_cases he : l = i
      · subst l
        simp only [emCallCfg, emCall_triple_inverse]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg]
        fin_cases r <;> simp
      · simp [emCallCfg, emCall_triple_other, he]
  · funext j
    rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
    · subst j; simp [emCallCfg, emCall_triple_pair]
    · subst j; simp [emCallCfg, emCall_triple_pair]
    · subst j
      by_cases he : l = i
      · subst l
        simp only [emCallCfg, emCall_triple_inverse]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg]
        fin_cases r <;> simp
      · simp [emCallCfg, emCall_triple_other, he]

/-- The cleaner's complete blank endpoint enlarges the cleaned bank prefix
by exactly one, while retaining every inactive tape and head.
**Proof sketch.** Separate the completed bank from every other tape slot.
Its three tapes and heads equal the cleaner's blank endpoint. Arithmetic on
the bank indices identifies this update with increasing the cleaned prefix. -/
private lemma emCall_bank_final (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (i : Fin M.k) :
    let frame := emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))
    emCallCfg (emCallTripleSelect M i) (fun q => .inr (.inl (i.castSucc, q)))
      frame.workTapes frame.workTapePos
      (emCallClearCfg x 1 3 (fun _ => none) (fun _ => none) (fun _ => none) 0) =
      emCallBankFrame M emit x arg cap T (i.val + 1) (.inr (.inl (i.castSucc, 3))) := by
  dsimp only
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
    · subst j; simp [emCallCfg, emCall_triple_pair, emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j; simp [emCallCfg, emCall_triple_pair, emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j
      by_cases he : l = i
      · subst l
        simp only [emCallCfg, emCall_triple_inverse]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg]
        fin_cases r <;> simp
      · have hi : l.val ≠ i.val := fun h => he (Fin.ext h)
        have hiff : l.val < i.val + 1 ↔ l.val < i.val := by omega
        simp only [emCallCfg, emCall_triple_other, he, ↓reduceIte]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, hiff]
  · funext j
    rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
    · subst j; simp [emCallCfg, emCall_triple_pair, emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j; simp [emCallCfg, emCall_triple_pair, emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j
      by_cases he : l = i
      · subst l
        simp only [emCallCfg, emCall_triple_inverse]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, emCallClearCfg]
        fin_cases r <;> simp
      · have hi : l.val ≠ i.val := fun h => he (Fin.ext h)
        have hiff : l.val < i.val + 1 ↔ l.val < i.val := by omega
        simp only [emCallCfg, emCall_triple_other, he, ↓reduceIte]
        simp only [emCallBankFrame, emCallFrame, emCall_layout_triple, hiff]

/-- One native bank-cleaning segment, including its dispatch to the next
bank, costs at most six source deadlines plus eight. Dispatch occurs at the
cleaner's observed first return, not at that analysis bound.
**Proof sketch.** Relocate the guarded first-return cleaner to the selected
triple. Its full blank endpoint is the next cleaned-prefix frame; a single
silent transition advances the finite bank index. -/
private lemma emCall_bank_step (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (i : Fin M.k) :
    ∃ t ≤ 6 * T + 8,
      (emCallTM M emit).tm.runFrom
        (emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))) t =
        emCallBankFrame M emit x arg cap T (i.val + 1) (.inr (.inl (i.succ, 0))) := by
  obtain ⟨t, _, ht, hfirst, hr⟩ := emCall_clear_first M arg x 1 T i
  let c := emCallClearCfg x 1 0 ((M.tm.runFrom (M.tm.initCfg arg) T).workTapes i)
    (emCallSpan (emCallLo M arg T i) (emCallHi M arg T i)) (bufferTape [true])
    ((M.tm.runFrom (M.tm.initCfg arg) T).workTapePos i)
  let frame := emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))
  have hrun := emCall_relocate_run emCallClearTM.tm (emCallTM M emit).tm
    (emCallTripleIndex M i) (emCallTripleSelect M i) (emCall_triple_inverse M i)
    (fun q => .inr (.inl (i.castSucc, q))) (fun q : Fin 4 => q ≠ 3)
    (by intro q hq inp work; simp [emCallTM, i.isLt, hq]; rfl)
    frame.workTapes frame.workTapePos c t
    (by intro j hj q hs hq; subst q; exact hfirst j hj hs)
  dsimp only [c, frame] at hrun
  rw [emCall_bank_initial, hr, emCall_bank_final] at hrun
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', hrun]
  simp only [MultiTapeTM.step, emCallBankFrame, emCallFrame, emCallTM,
    Fin.coe_castSucc, i.isLt, ↓reduceDIte, ↓reduceIte]
  rw [controlAction_apply, moveInputPos_zero]
  rfl

/-- All tracked banks are cleaned sequentially, with both administrative
words preserved. This is a full configuration equality, not a per-tape claim.
**Proof sketch.** Induct over the finite bank prefix. Each bank's native
cleaner and dispatch adds at most `6T+8`, and the exact next frame provides the
following cleaner's entry. Zero source tapes gives the reflexive empty sequence. -/
private lemma emCall_banks_run (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) : ∀ j (hj : j ≤ M.k),
    ∃ t ≤ j * (6 * T + 8),
      (emCallTM M emit).tm.runFrom
        (emCallBankFrame M emit x arg cap T 0 (.inr (.inl (0, 0)))) t =
        emCallBankFrame M emit x arg cap T j (.inr (.inl (⟨j, by omega⟩, 0))) := by
  intro j
  induction j with
  | zero => intro hj; exact ⟨0, by omega, rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨a, ha, he⟩ := ih (by omega)
    obtain ⟨b, hb, hr⟩ := emCall_bank_step M emit x arg cap T ⟨j, by omega⟩
    refine ⟨a + b, ?_, ?_⟩
    · rw [Nat.succ_mul]; omega
    · rw [MultiTapeTM.runFrom_add, he]
      exact hr

/-- The identity tape relocation of the prepared evaluator's entry is the
caller's canonical argument seam. -/
private lemma emCall_prepare_initial (M : FinTM Bool) (emit : Bool) (x arg : List Bool) :
    let R := emCallRightTM (emCallTrackTM M)
    emCallCfg (fun i => some i) (Sum.inl : (emCallSource M).State → emCallState M)
      (fun _ _ => none) (fun _ => 0)
      (emCallEvalCfg (w := x) R (R.tm.initCfg arg) true 1) =
      Cfg.ofWords (emCallTM M emit).tm.q₀ (stateWord (emCallTM M emit).k arg) := by
  dsimp only
  rw [emCall_eval_initial]
  rfl

/-- The completed prepared evaluation is exactly the uncleaned bank frame:
complete source data, visited intervals, origin markers, and captured result,
with the argument head at its known right boundary. -/
private lemma emCall_prepare_final (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ)
    (hout : (M.tm.runFrom (M.tm.initCfg arg) T).output = cap) :
    emCallCfg (fun i => some i) (Sum.inl : (emCallSource M).State → emCallState M)
      (fun _ _ => none) (fun _ => 0)
      (emCallEvalCfg (w := x) (emCallRightTM (emCallTrackTM M))
        (emCallRightScan (emCallTrackTM M)
          (emCallTrackCfg M (M.tm.runFrom (M.tm.initCfg arg) T)
            (emCallLo M arg T) (emCallHi M arg T)) none arg.length (le_refl _)) false 1) =
      emCallBankFrame M emit x arg cap T 0 (.inl (.inr ())) := by
  have hout' : (M.tm.runFrom (M.tm.initCfg arg) T).output = cap := hout
  simp only [MultiTapeTM.initCfg, Cfg.init] at hout'
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    simp [emCallCfg, emCallEvalCfg, captureCfg, bufferedSecondCfg, emCallRightScan,
      emCallTrackCfg, emCallBankFrame, emCallFrame, emCallLayout, Fin.addCases, hout']
    rfl
  · funext j
    simp [emCallCfg, emCallEvalCfg, captureCfg, bufferedSecondCfg, emCallRightScan,
      emCallTrackCfg, emCallBankFrame, emCallFrame, emCallLayout, Fin.addCases, hout']
    rfl

/-- The controller reaches its first bank-cleaning entry from the genuine
argument seam after observed evaluation, with no native-input scan.
**Proof sketch.** The prepared evaluator's actual first-return contract
supplies the guard for identity tape relocation into the call controller.
The full endpoint frame then takes one silent dispatch to bank zero. -/
private lemma emCall_prepare_run (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (hM : M.ComputesInTime arg cap T) :
    ∃ t ≤ 2 * T + arg.length + 4,
      (emCallTM M emit).tm.runFrom
        (Cfg.ofWords (emCallTM M emit).tm.q₀ (stateWord (emCallTM M emit).k arg)) t =
        emCallBankFrame M emit x arg cap T 0 (.inr (.inl (0, 0))) := by
  obtain ⟨t, _, ht, hfirst, hr⟩ := emCall_prepared_eval_first M x arg cap T hM
  let R := emCallRightTM (emCallTrackTM M)
  let c := emCallEvalCfg (w := x) R (R.tm.initCfg arg) true 1
  have he := emCall_relocate_run (emCallSource M).tm (emCallTM M emit).tm
    id (fun i => some i) (fun _ => rfl)
    (Sum.inl : (emCallSource M).State → emCallState M)
    (fun q => q ≠ .inr ())
    (by intro q hq inp work; simp [emCallTM, hq])
    (fun _ _ => none) (fun _ => 0) c t
    (by intro j hj q hs hq; rw [hq] at hs; exact hfirst j hj hs)
  dsimp only [c, R] at he
  erw [emCall_prepare_initial M emit x arg, hr,
    emCall_prepare_final M emit x arg cap T ((computesInTime_iff _ _ _ _).mp hM).2] at he
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', he]
  simp only [MultiTapeTM.step, emCallBankFrame, emCallFrame, emCallTM, ↓reduceIte]
  rw [controlAction_apply, moveInputPos_zero]

/-- Once all source banks are clean, the relocated finalizer's entry is the
full caller frame, including the known argument and capture right boundaries.
**Proof sketch.** Split each tape index into argument, capture, or source
triple. The first two agree with the finalizer's entry by their relocation
inverse; all triples are blank because the cleaned prefix contains every bank. -/
private lemma emCall_finish_initial (M : FinTM Bool) (emit : Bool) (x arg cap : List Bool)
    (T : ℕ) :
    emCallCfg (emCallPairSelect M) (fun q => .inr (.inr q) : Fin 6 → emCallState M)
      (fun _ _ => none) (fun _ => 0)
      (emCallFinishCfg emit x 1 0 (bufferTape arg) (bufferTape cap) arg.length cap.length []) =
      emCallBankFrame M emit x arg cap T M.k (.inr (.inr 0)) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    rcases emCall_layout_cases M j with h | h | ⟨i, r, h⟩
    · subst j; simp [emCallCfg, emCall_pair_inverse, emCallFinishCfg,
        emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j; simp [emCallCfg, emCall_pair_inverse, emCallFinishCfg,
        emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j; simp only [emCallCfg, emCall_pair_triple, emCallBankFrame, emCallFrame,
        emCall_layout_triple, i.isLt, ↓reduceIte]
      fin_cases r <;> rfl
  · funext j
    rcases emCall_layout_cases M j with h | h | ⟨i, r, h⟩
    · subst j; simp [emCallCfg, emCall_pair_inverse, emCallFinishCfg,
        emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j; simp [emCallCfg, emCall_pair_inverse, emCallFinishCfg,
        emCallBankFrame, emCallFrame, emCall_layout_pair]
    · subst j; simp only [emCallCfg, emCall_pair_triple, emCallBankFrame, emCallFrame,
        emCall_layout_triple, i.isLt, ↓reduceIte]
      fin_cases r <;> rfl

/-- The finalizer's endpoint is the complete canonical clean-call seam. -/
private lemma emCall_finish_final (M : FinTM Bool) (emit : Bool) (x arg cap : List Bool) :
    emCallCfg (emCallPairSelect M) (fun q => .inr (.inr q) : Fin 6 → emCallState M)
      (fun _ _ => none) (fun _ => 0)
      (emCallFinishCfg emit x 1 5 (bufferTape (if emit then arg else cap))
        (fun _ => none) 0 0 (if emit then cap else [])) =
      { Cfg.ofWords (input := x) (.inr (.inr (5 : Fin 6)) : emCallState M)
          (stateWord (emCallTM M emit).k (if emit then arg else cap))
        with output := if emit then cap else [] } := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext j
    rcases emCall_layout_cases M j with h | h | ⟨i, r, h⟩
    · subst j; simp [emCallCfg, emCall_pair_inverse, emCallFinishCfg, Cfg.ofWords,
        stateWord, emCallPairIndex, emCallPairSelect]
    · subst j; simp [emCallCfg, emCall_pair_inverse, emCallFinishCfg, Cfg.ofWords,
        stateWord, emCallPairIndex, emCallPairSelect, bufferedCompTM, emCallIdleTM, emCallRightTM, emCallTrackTM]
    · subst j; simp only [emCallCfg, emCall_pair_triple, Cfg.ofWords, stateWord]
      fin_cases r <;> simp [emCallTripleIndex]
  · funext j
    simp only [emCallCfg, emCallFinishCfg, Cfg.ofWords]
    cases emCallPairSelect M j <;> simp

/-- Finalization in the full controller includes the post-cleanup dispatch
and restores every scratch tape and head. -/
private lemma emCall_finalize_run (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) :
    (emCallTM M emit).tm.runFrom
      (emCallBankFrame M emit x arg cap T M.k (.inr (.inl (Fin.last M.k, 0))))
      (arg.length + 3 * cap.length + 6) =
      { Cfg.ofWords (input := x) (.inr (.inr (5 : Fin 6)) : emCallState M)
          (stateWord (emCallTM M emit).k (if emit then arg else cap))
        with output := if emit then cap else [] } := by
  have hs : (emCallTM M emit).tm.step
      (emCallBankFrame M emit x arg cap T M.k (.inr (.inl (Fin.last M.k, 0)))) =
      emCallBankFrame M emit x arg cap T M.k (.inr (.inr 0)) := by
    simp only [MultiTapeTM.step, emCallBankFrame, emCallFrame, emCallTM,
      Fin.val_last, lt_self_iff_false, ↓reduceDIte]
    rw [controlAction_apply, moveInputPos_zero]
  have he := emCall_relocate_run (emCallFinishTM emit).tm (emCallTM M emit).tm
    (emCallPairIndex M) (emCallPairSelect M) (emCall_pair_inverse M)
    (fun q => .inr (.inr q)) (fun _ => True) (by intros; rfl)
    (fun _ _ => none) (fun _ => 0)
    (emCallFinishCfg emit x 1 0 (bufferTape arg) (bufferTape cap) arg.length cap.length [])
    (arg.length + 3 * cap.length + 5) (by intros; trivial)
  erw [emCall_finish_initial M emit x arg cap T, emCall_finish_run, emCall_finish_final] at he
  rw [show arg.length + 3 * cap.length + 6 = (arg.length + 3 * cap.length + 5) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs]
  exact he

/-- Both call modes reach the full clean seam within the audited linear
shape, with `K = 6` (so `6 + 13 M.k + 3K = 24 + 13 M.k`).
**Proof sketch.** Compose the complete prepared evaluation, all sequential
bank cleanups, and result finalization. The bank prefix induction accounts for
every source tape. Each term is charged to the actual argument deadline or a
word length; no native transition reads a numerical deadline. -/
private lemma emCall_complete (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (hM : M.ComputesInTime arg cap T) :
    ∃ t ≤ (24 + 13 * M.k) * (T + arg.length + cap.length + 1),
      (emCallTM M emit).tm.runFrom
        (Cfg.ofWords (input := x) (emCallTM M emit).tm.q₀ (stateWord (emCallTM M emit).k arg)) t =
        { Cfg.ofWords (input := x) (.inr (.inr (5 : Fin 6)) : emCallState M)
            (stateWord (emCallTM M emit).k (if emit then arg else cap))
          with output := if emit then cap else [] } := by
  obtain ⟨a, ha, he⟩ := emCall_prepare_run M emit x arg cap T hM
  obtain ⟨b, hb, hf⟩ := emCall_banks_run M emit x arg cap T M.k (le_refl _)
  let B := T + arg.length + cap.length + 1
  have hbank : b ≤ (13 * M.k) * B := by
    calc
      b ≤ M.k * (6 * T + 8) := hb
      _ ≤ M.k * (13 * B) := Nat.mul_le_mul_left M.k (by dsimp [B]; omega)
      _ = (13 * M.k) * B := by simp [Nat.mul_assoc, Nat.mul_left_comm]
  have hrest : a + (arg.length + 3 * cap.length + 6) ≤ 24 * B := by
    dsimp [B]; omega
  refine ⟨a + b + (arg.length + 3 * cap.length + 6), ?_, ?_⟩
  · calc
      a + b + (arg.length + 3 * cap.length + 6) ≤ 24 * B + (13 * M.k) * B := by omega
      _ = (24 + 13 * M.k) * B := (Nat.add_mul _ _ _).symm
  · rw [MultiTapeTM.runFrom_add,
      (emCallTM M emit).tm.runFrom_add _ a b, he, hf]
    exact emCall_finalize_run M emit x arg cap T

/-- The fresh exit control is an absorbing silent state, on every tape
configuration, so cutting at first exit preserves the entire endpoint. -/
private lemma emCall_exit_fixed (M : FinTM Bool) (emit : Bool) (x : List Bool)
    (z : Cfg (emCallTM M emit).k Bool (emCallTM M emit).State x)
    (hz : z.state = some (.inr (.inr (5 : Fin 6)))) :
    (emCallTM M emit).tm.step z = z := by
  have ha : ∀ inp work, (emCallTM M emit).tm.tr (.inr (.inr 5)) inp work =
      controlAction 0 (some (.inr (.inr 5))) := by
    intro inp work
    dsimp only [emCallTM, emCallFinishTM, emCallAction, controlAction]
    congr 1
    funext i
    cases emCallPairSelect M i <;> rfl
  unfold MultiTapeTM.step
  simp only [hz]
  rw [ha, controlAction_apply, moveInputPos_zero]
  cases z
  simp_all

/-- The complete clean call returns at its actual first positive exit.
**Proof sketch.** Cut the bounded complete run at the least exit visit.
Absorption preserves its full tape/head/output endpoint. The entry and exit
lie in disjoint finite-control summands, excluding time zero. -/
private lemma emCall_first (M : FinTM Bool) (emit : Bool)
    (x arg cap : List Bool) (T : ℕ) (hM : M.ComputesInTime arg cap T) :
    ∃ t ≤ (24 + 13 * M.k) * (T + arg.length + cap.length + 1),
      0 < t ∧
      (∀ j < t, ((emCallTM M emit).tm.runFrom
        (Cfg.ofWords (input := x) (emCallTM M emit).tm.q₀ (stateWord (emCallTM M emit).k arg)) j).state
          ≠ some (.inr (.inr (5 : Fin 6)))) ∧
      (emCallTM M emit).tm.runFrom
        (Cfg.ofWords (input := x) (emCallTM M emit).tm.q₀ (stateWord (emCallTM M emit).k arg)) t =
        { Cfg.ofWords (input := x) (.inr (.inr (5 : Fin 6)) : emCallState M)
            (stateWord (emCallTM M emit).k (if emit then arg else cap))
          with output := if emit then cap else [] } := by
  obtain ⟨b, hb, he⟩ := emCall_complete M emit x arg cap T hM
  obtain ⟨t, ht, hfirst, hr⟩ := emCall_first_entry (emCallTM M emit).tm
    (fun q => q = (.inr (.inr (5 : Fin 6)) : emCallState M)) _ _ b
    (by rintro z ⟨q, hz, rfl⟩; exact emCall_exit_fixed M emit x z hz)
    ⟨_, rfl, rfl⟩ he
  have hpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := by omega
    have hstate := congrArg Cfg.state hr
    simp [ht0, Cfg.ofWords, emCallTM] at hstate
  refine ⟨t, ht.trans hb, hpos, ?_, hr⟩
  intro j hj hs
  exact hfirst j hj ⟨_, hs, rfl⟩

/-! ### Forwarding loop controller -/

/-- Native transitions commute with an arbitrary existing output prefix:
control and input/work symbols cannot inspect the append-only output. -/
private lemma emLoop_step_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (pre : List Bool) (c : Cfg k Bool S x) :
    tm.step { c with output := pre ++ c.output } =
      { tm.step c with output := pre ++ (tm.step c).output } := by
  have hi : ({c with output := pre ++ c.output} : Cfg k Bool S x).inputSymbol =
      c.inputSymbol := rfl
  have hw : ({c with output := pre ++ c.output} : Cfg k Bool S x).workTapeSymbols =
      c.workTapeSymbols := rfl
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, hs]
  | some q =>
    simp only [MultiTapeTM.step, hs, hi, hw]
    refine Cfg.ext rfl rfl rfl rfl ?_
    simp only [Action.apply, List.append_assoc]
    rfl

/-- Every native run commutes with prepending arbitrary accumulated output.
**Proof sketch.** Induct on the run length and apply the one-step prefix law;
list associativity is the only output calculation. Halted tails are included. -/
private lemma emLoop_run_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (pre : List Bool) (c : Cfg k Bool S x) (t : ℕ) :
    tm.runFrom { c with output := pre ++ c.output } t =
      { tm.runFrom c t with output := pre ++ (tm.runFrom c t).output } := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih, emLoop_step_prefix,
      MultiTapeTM.runFrom_succ_eq_step']

/-- The forwarding variant retains the fuel capture and every administrative
transition of the existing loop skeleton. Body actions go through
`Turing.emitAction`, with a stationary unused payload tape. -/
private def emLoopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool where
  k := body.k + 1 + (1 + F.k) + 1
  State := LoopHostState body F
  tm := {
    q₀ := .inl F.tm.q₀
    tr := fun q inp work => match q with
      | .inr (.inl (startup, s)) =>
        leftAction 1 id
          (Turing.emitAction (fun s => .inr (.inl (startup, s)))
            (.inr (.inr (if startup then 6 else 7)))
            ((loopBodySource body F anchor).tr s inp (fun i => work i.castSucc)))
      | _ => (loopHost body F anchor findMode).tm.tr q inp work }

/-- The fuel states capture all fuel emissions directly in the concrete host. -/
private lemma emLoopHost_fuel_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool F.State x) (t : ℕ)
    (hlive : ∀ u < t, ¬((loopFuelSource body F).runFrom c u).Halted) :
    (emLoopHost body F anchor findMode).tm.runFrom
        (captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] c) t =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).runFrom c t) := by
  exact capture_run (loopFuelSource body F) (emLoopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel capture starts at the host's genuine blank initial configuration. -/
private lemma emLoopHost_init (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) :
    (emLoopHost body F anchor findMode).tm.initCfg x =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((loopFuelSource body F).initCfg x) := by
  rw [initCfg_ofWords, initCfg_ofWords]
  simp [Cfg.ofWords, captureCfg, emLoopHost, loopHost, loopFuelSource]

/-- Host phases 4 and 5 rewind the native input in bounded time, retaining
all tapes, heads, and output, then dispatch to genuine body startup. -/
private lemma emLoopHost_input_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (cfg : Cfg (emLoopHost body F anchor findMode).k Bool (emLoopHost body F anchor findMode).State x)
    (hs : cfg.state = some (.inr (.inr (4 : Fin 14)))) :
    ∃ t ≤ cfg.inputPos.val + 2,
      (emLoopHost body F anchor findMode).tm.runFrom cfg t =
        {cfg with state := some (.inr (.inl (true, (body.tm.q₀, false)))), inputPos := 1} := by
  apply loop_rewind_bounded (emLoopHost body F anchor findMode).tm
    (.inr (.inr 4)) (.inr (.inr 5)) (.some (.inr (.inl (true, (body.tm.q₀, false)))))
    ?_ ?_ cfg hs
  · intro inp work
    exact loopControl_idle body F .neg _
  · intro inp work
    cases inp <;> exact loopControl_idle body F _ _

/-- Fuel-rewind phase 1 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma emLoopHost_fuel_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (emLoopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 2))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 1))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 1)))
      | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 2)))).apply _ = _
    rw [loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [loopControl_apply]
    simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (emLoopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 1)))
        | none => loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 2)))).apply _ = _
      rw [loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [loopControl_apply]
      simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Phase 2 copies the remaining fuel bits to the counter, clearing each
captured bit, then starts the synchronized rewind.
**Proof sketch.** Induct on the uncopied suffix. A nonempty suffix writes
its head at the counter's right blank, clears the corresponding payload
cell, and advances both heads. The empty suffix detects the right blank
and moves both heads left once, including when the original word is empty. -/
private lemma emLoopHost_fuel_copy (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (out : List Bool)
    (rest : List Bool) : ∀ pre,
    (emLoopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre rest) pre.length pre.length out) (rest.length + 1) =
      loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape (pre ++ rest))
        (bufferTape []) ((pre ++ rest).length - 1) ((pre ++ rest).length - 1) out := by
  induction rest with
  | nil =>
    intro pre
    rw [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
        (loopCopyTape pre []) pre.length pre.length out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => loopControlAction body F 0 none (some (some b), .pos)
          (some none, .pos) none (some (.inr (.inr 2)))
      | none => loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))).apply _ = _
    rw [loopFrame_payload, loopCopy_read]
    dsimp only [List.head?]
    rw [loopControl_apply]
    simp [loopWrite, loopCopy_final, sub_eq_add_neg]
  | cons b rest ih =>
    intro pre
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (emLoopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre (b :: rest)) pre.length pre.length out) =
        loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape (pre ++ [b]))
          (loopCopyTape (pre ++ [b]) rest) (pre ++ [b]).length (pre ++ [b]).length out := by
      change (match (loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (loopCopyTape pre (b :: rest)) pre.length pre.length out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some bit => loopControlAction body F 0 none (some (some bit), .pos)
            (some none, .pos) none (some (.inr (.inr 2)))
        | none => loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))).apply _ = _
      rw [loopFrame_payload, loopCopy_read]
      dsimp only [List.head?]
      rw [loopControl_apply]
      simp [loopWrite, loopCopy_erase, bufferTape_append]
    rw [hs]
    simpa [List.append_assoc] using ih (pre ++ [b])

/-- Phase 3 rewinds counter and cleared capture heads together.
**Proof sketch.** Induct on the number of counter cells to the left. Both
heads take the same moves; only the counter is read, so the already-cleared
capture tape stays blank. The final left-blank test moves both heads to zero. -/
private lemma emLoopHost_fuel_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    ∀ j, j ≤ word.length →
    (emLoopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out) (j + 1) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
        (bufferTape []) ((0 : ℤ) - 1) ((0 : ℤ) - 1) out).workTapeSymbols
          ⟨body.k + 1, by omega⟩ with
      | some _ => loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))
      | none => loopControlAction body F 0 none (none, .pos) (none, .pos) none
          (some (.inr (.inr 4)))).apply _ = _
    rw [loopFrame_counter]
    simp only [zero_sub, bufferTape_left]
    rw [loopControl_apply]
    simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (emLoopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out) =
        loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out := by
      change (match (loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            ⟨body.k + 1, by omega⟩ with
        | some _ => loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))
        | none => loopControlAction body F 0 none (none, .pos) (none, .pos) none
            (some (.inr (.inr 4)))).apply _ = _
      rw [loopFrame_counter]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [loopControl_apply]
      simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Fuel setup phases 0--3 copy the complete fuel word to the counter,
clear the capture track, and return both heads to zero in exactly `3|word|+4`
steps. This includes the empty word, with no counter debit.
**Proof sketch.** Compose the mandatory left move, the fuel rewind, the
copy/clear scan, and the synchronized rewind. Their costs are respectively
one and three copies of the word length plus one. -/
private lemma emLoopHost_fuel_setup (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    (emLoopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
          (bufferTape word) 0 word.length out) (3 * word.length + 4) =
      loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  have hs : (emLoopHost body F anchor findMode).tm.step
      (loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
        (bufferTape word) 0 word.length out) =
      loopFrame body F base (some (.inr (.inr 1))) p flag (bufferTape [])
        (bufferTape word) 0 ((word.length : ℤ) - 1) out := by
    change (loopControlAction body F 0 none (none, 0) (none, .neg) none
      (some (.inr (.inr 1)))).apply _ = _
    rw [loopControl_apply]
    simp [loopWrite, sub_eq_add_neg]
  rw [show 3 * word.length + 4 =
      ((word.length + 1) + (word.length + 1) + (word.length + 1)) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs]
  rw [MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add (a := word.length + 1) (b := word.length + 1),
    emLoopHost_fuel_rewind body F anchor findMode base p flag (bufferTape []) 0 word out
      word.length (le_refl _)]
  have hc := emLoopHost_fuel_copy body F anchor findMode base p flag out word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, loopCopy_initial] at hc
  rw [hc, emLoopHost_fuel_return body F anchor findMode base p flag word out
    word.length (le_refl _)]

/-- Fuel execution, setup, and input rewind reach prepared body startup
within `5*T+7` steps, retaining the actual fuel endpoint.
**Proof sketch.** Replace the supplied padded fuel run by its first halt,
relocate it twice, and capture it in the actual host. Setup costs `3L+4`,
where `L ≤ T`; the input rewind costs at most the first run's displacement
plus two, hence at most `T+3`. No bound in the input length is used. -/
private lemma emLoopHost_prepare (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (emLoopHost body F anchor findMode).tm.runFrom
        ((emLoopHost body F anchor findMode).tm.initCfg x) t = loopReady body F c := by
  obtain ⟨space, hhalt, hout, hspace⟩ := hF x
  obtain ⟨u, hu, hut, hlive, huh, hue⟩ :=
    loop_first_halt F.tm (F.tm.initCfg x) (T x.length) (by simp [MultiTapeTM.initCfg, Cfg.init]) hhalt
  let c := F.tm.runFrom (F.tm.initCfg x) u
  have hc : c.state = none := huh
  have ho : c.output = Nat.bits (R x.length) := by dsimp only [c]; rw [hue]; exact hout
  have hcap : (emLoopHost body F anchor findMode).tm.runFrom
      ((emLoopHost body F anchor findMode).tm.initCfg x) u = loopFuelCaptured body F c := by
    rw [emLoopHost_init, loopFuel_init]
    rw [emLoopHost_fuel_capture]
    · rw [loopFuel_run]; rfl
    · intro v hv
      rw [loopFuel_run]
      simpa [Cfg.Halted, loopFuelCfg, rightCfg] using hlive v hv
  let prepared := loopFrame body F (loopFuelCaptured body F c)
    (some (.inr (.inr 4))) c.inputPos (bufferTape []) (bufferTape c.output)
    (bufferTape []) 0 0 []
  have hsetup : (emLoopHost body F anchor findMode).tm.runFrom
      (loopFuelCaptured body F c) (3 * c.output.length + 4) = prepared := by
    conv_lhs => arg 1; rw [loopFuelCaptured_frame body F c hc]
    exact emLoopHost_fuel_setup body F anchor findMode _ _ _ _ _
  obtain ⟨v, hv, hrew⟩ := emLoopHost_input_rewind body F anchor findMode prepared rfl
  have hw : c.output.length ≤ T x.length := by rw [ho]; exact loop_fuel_width F R T hF x
  have hp : c.inputPos.val ≤ 1 + u := loop_input_run_le F.tm (F.tm.initCfg x) u
  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_⟩
  · change v ≤ c.inputPos.val + 2 at hv
    omega
  · rw [MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew]
    rfl

/-- Phase 6 clears startup's false flag and releases the first anchor for
free. It changes no body, counter, or fuel data.
**Proof sketch.** The captured stopped body is in phase 6. Its sole write
clears the flag's origin cell. Comparing tape blocks identifies the result
with the active released call on the same body data. -/
private lemma emLoopHost_release (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    (emLoopHost body F anchor findMode).tm.step
        (loopCall body F anchor true {c with state := none} false (some false) word fuel) =
      loopCall body F anchor false {c with state := some anchor} true none word fuel := by
  change (loopControlAction body F 0 (some none) (none, 0) (none, 0) none
    (some (.inr (.inl (false, (anchor, true)))))).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hf : (i : ℕ) = body.k
    · have hi : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
        leftCfg, loopBodyCfg, hf, hi, Fin.addCases, Function.update]
    · by_cases hb : (i : ℕ) < body.k + 1
      · have hi : (i : ℕ) < body.k := by omega
        simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
          leftCfg, loopBodyCfg, hf, Fin.addCases, hb, hi]
      · simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
          leftCfg, loopBodyCfg, hf, Fin.addCases, hb]
  · funext i
    by_cases hf : (i : ℕ) = body.k <;>
      simp [Action.apply, loopControlAction, loopCall, captureCfg, loopBodyPadded,
        leftCfg, loopBodyCfg, hf]
  · simp [Action.apply, loopControlAction, loopCall, captureCfg]

/-- One actual-host borrow step changes only the counter, recording success
or underflow in the rewind phase. -/
private lemma emLoopHost_borrow_step (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (pre rest : List Bool) :
    (emLoopHost body F anchor findMode).tm.step
      (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
        (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []) =
      match rest with
      | [] => loopFrame body F base (some (.inr (.inr 10))) p (bufferTape [])
          (bufferTape pre) (bufferTape []) (pre.length - 1) 0 []
      | true :: us => loopFrame body F base (some (.inr (.inr 9))) p (bufferTape [])
          (bufferTape (pre ++ false :: us)) (bufferTape []) (pre.length - 1) 0 []
      | false :: us => loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ true :: us)) (bufferTape []) (pre.length + 1) 0 [] := by
  change (match (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
      (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []).workTapeSymbols
        ⟨body.k + 1, by omega⟩ with
    | some false => loopControlAction body F 0 none (some (some true), .pos) (none, 0)
        none (some (.inr (.inr 8)))
    | some true => loopControlAction body F 0 none (some (some false), .neg) (none, 0)
        none (some (.inr (.inr 9)))
    | none => loopControlAction body F 0 none (none, .neg) (none, 0) none
        (some (.inr (.inr 10)))).apply _ = _
  rw [loopFrame_counter, loopBuffer_read]
  cases rest with
  | nil =>
    simp only [List.head?]
    rw [loopControl_apply]
    simp [loopWrite, sub_eq_add_neg]
  | cons b rest =>
    cases b <;> simp only [List.head?]
    all_goals rw [loopControl_apply]; simp [loopWrite, loopBuffer_write, sub_eq_add_neg]

/-- The actual host performs the borrow scan in the standalone scan's exact
time, preserving all non-counter tracks.
**Proof sketch.** Induct on the remaining word. Each false bit advances the
processed prefix. A true bit or the right blank starts the appropriate
rewind phase; no cell outside the original counter width is written. -/
private lemma emLoopHost_borrow_run (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) : ∀ pre,
    (emLoopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ word)) (bufferTape []) pre.length 0 [])
        (loopBorrowPos word + 1) =
      loopFrame body F base (some (.inr (.inr (if (loopDebit word).2 then 9 else 10)))) p
        (bufferTape []) (bufferTape (pre ++ (loopDebit word).1)) (bufferTape [])
        ((pre.length : ℤ) + loopBorrowPos word - 1) 0 [] := by
  induction word with
  | nil =>
    intro pre
    simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      emLoopHost_borrow_step body F anchor findMode base p pre []
  | cons b word ih =>
    intro pre
    cases b with
    | true =>
      simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        emLoopHost_borrow_step body F anchor findMode base p pre (true :: word)
    | false =>
      simp only [loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, emLoopHost_borrow_step]
      simpa [loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- The host's success/underflow rewind returns the counter head to zero.
Success releases the next anchor; underflow enters phase 11 without yet
emitting. Both paths retain all inactive residue.
**Proof sketch.** Induct on the number of counter cells to the left. The
left-blank test dispatches according to the stored success bit. -/
private lemma emLoopHost_borrow_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) (success : Bool) :
    ∀ j, j ≤ word.length →
    (emLoopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 []) (j + 1) =
      loopFrame body F base
        (some (if success then .inr (.inl (false, (anchor, true))) else .inr (.inr 11))) p
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    cases success <;>
      (change (match (loopFrame body F base _ p (bufferTape []) (bufferTape word)
          (bufferTape []) ((0 : ℤ) - 1) 0 []).workTapeSymbols ⟨body.k + 1, by omega⟩ with
        | some _ => loopControlAction body F 0 none (none, .neg) (none, 0) none _
        | none => loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
    all_goals
      rw [loopFrame_counter]
      simp only [zero_sub, bufferTape_left]
      rw [loopControl_apply]
      simp [loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (emLoopHost body F anchor findMode).tm.step
        (loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []) =
        loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 [] := by
      cases success <;>
        (change (match (loopFrame body F base _ p (bufferTape []) (bufferTape word)
            (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []).workTapeSymbols
              ⟨body.k + 1, by omega⟩ with
          | some _ => loopControlAction body F 0 none (none, .neg) (none, 0) none _
          | none => loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
      all_goals
        rw [loopFrame_counter, show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
          bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
        rw [loopControl_apply]
        simp [loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- The complete actual-host counter operation has the fixed-width
worst-case bound `2|word|+2`, covering underflow and width zero. -/
private lemma emLoopHost_borrow (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) :
    2 * loopBorrowPos word + 2 ≤ 2 * word.length + 2 ∧
    (emLoopHost body F anchor findMode).tm.runFrom
        (loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape word) (bufferTape []) 0 0 []) (2 * loopBorrowPos word + 2) =
      loopFrame body F base
        (some (if (loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) p
        (bufferTape []) (bufferTape (loopDebit word).1) (bufferTape []) 0 0 [] := by
  refine ⟨by have := loopBorrowPos_le word; omega, ?_⟩
  have hr := emLoopHost_borrow_run body F anchor findMode base p word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * loopBorrowPos word + 2 =
      (loopBorrowPos word + 1) + (loopBorrowPos word + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact emLoopHost_borrow_rewind body F anchor findMode base p (loopDebit word).1
    (loopDebit word).2 _ (by rw [loopDebit_length]; exact loopBorrowPos_le word)

/-- A rejecting stopped call clears its flag, debits in worst-case width
time, and either releases the next anchor or emits exhaustion and halts.
Underflow and its emission are included in this same segment.
**Proof sketch.** Phase 7 clears the false flag in one step. The proved host
borrow takes `2j+2` steps. Success is the reframed next body seam; underflow
takes one additional phase-11 step, for at most `2|word|+4` steps in total. -/
private lemma emLoopHost_reject (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.state = none) (ho : c.output = []) :
    ∃ t ≤ 2 * word.length + 4,
      if (loopDebit word).2 then
        (emLoopHost body F anchor findMode).tm.runFrom
            (loopCall body F anchor false c false (some false) word fuel) t =
          loopCall body F anchor false {c with state := some anchor} true none (loopDebit word).1 fuel
      else
        ((emLoopHost body F anchor findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).state = none ∧
        ((emLoopHost body F anchor findMode).tm.runFrom
          (loopCall body F anchor false c false (some false) word fuel) t).output =
            (if findMode then [] else [false]) := by
  let base := loopCall body F anchor false c false (some false) word fuel
  have hs : base.state = some (.inr (.inr (7 : Fin 14))) := by
    simp [base, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, hc]
  have hf : base = loopFrame body F base (some (.inr (.inr 7))) c.inputPos
      (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 [] := by
    have h := loopCall_frame body F anchor false c false (some false) word fuel
    have hstate : (loopCall body F anchor false c false (some false) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := hs
    simpa only [hstate, ho, List.length_nil, Nat.cast_zero] using h
  have hstep : (emLoopHost body F anchor findMode).tm.step base =
      loopFrame body F base (some (.inr (.inr 8))) c.inputPos
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
    conv_lhs => arg 1; rw [hf]
    change (if (loopFrame body F base (some (.inr (.inr 7))) c.inputPos
        (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [loopFrame_flag]
    change (loopControlAction body F 0 (some none) (none, 0) (none, 0) none
      (some (.inr (.inr 8)))).apply _ = _
    rw [loopControl_apply, loopFlag_clear]
    simp [loopWrite]
  have hrun : (emLoopHost body F anchor findMode).tm.runFrom base (2 * loopBorrowPos word + 3) =
      loopFrame body F base
        (some (if (loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) c.inputPos
        (bufferTape []) (bufferTape (loopDebit word).1) (bufferTape []) 0 0 [] := by
    rw [show 2 * loopBorrowPos word + 3 = (2 * loopBorrowPos word + 2) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact (emLoopHost_borrow body F anchor findMode base c.inputPos word).2
  have hw := loopBorrowPos_le word
  by_cases hb : (loopDebit word).2 = true
  · refine ⟨2 * loopBorrowPos word + 3, by omega, ?_⟩
    simp only [hb, if_true] at hrun ⊢
    rw [hrun]
    have h := loopCall_reframe body F anchor c false false false true (some false) none
      word (loopDebit word).1 fuel (some anchor)
    simpa [base, loopCall, captureCfg, loopBodyPadded, leftCfg, loopBodyCfg, ho] using h
  · refine ⟨2 * loopBorrowPos word + 4, by omega, ?_⟩
    simp only [hb] at hrun ⊢
    have hh : (emLoopHost body F anchor findMode).tm.runFrom base (2 * loopBorrowPos word + 4) =
        loopFrame body F base none c.inputPos (bufferTape []) (bufferTape (loopDebit word).1)
          (bufferTape []) 0 0 (if findMode then [] else [false]) := by
      rw [show 2 * loopBorrowPos word + 4 = (2 * loopBorrowPos word + 3) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step', hrun]
      change (loopControlAction body F 0 none (none, 0) (none, 0)
        (if findMode then none else some false) none).apply _ = _
      rw [loopControl_apply]
      cases findMode <;> simp [loopWrite]
    rw [hh]
    exact ⟨rfl, rfl⟩

/-- Forwarded body configuration with a blank, inactive last tape. This
uses the existing tape layout, but the physical output carries the chunk. -/
private def emLoopForwardCfg {k : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (ret : H) (pre : List Bool) (c : Cfg k Bool S x) :
    Cfg (k + 1) Bool H x :=
  leftCfg id (Turing.emitCfg emb ret pre c) (fun _ : Fin 1 => bufferTape []) (fun _ => 0)

/-- A forwarded action preserves the padded source configuration and appends
its optional bit after the accumulated prefix, including on a halting action. -/
private lemma emLoop_forward_apply {k : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (ret : H) (pre : List Bool)
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (leftAction 1 id (Turing.emitAction emb ret a)).apply (emLoopForwardCfg emb ret pre c) =
      emLoopForwardCfg emb ret pre (a.apply c) := by
  unfold emLoopForwardCfg
  rw [leftCfg_apply]
  have he : (Turing.emitAction emb ret a).apply (Turing.emitCfg emb ret pre c) =
      Turing.emitCfg emb ret pre (a.apply c) := by
    refine Cfg.ext rfl rfl rfl rfl ?_
    simp only [Turing.emitAction, Turing.emitCfg, Action.apply, List.append_assoc]
  rw [he]

/-- Guarded forwarding with one inactive tape, proved locally so this batch
does not depend on the concurrent `Turing.emit_run` admission.
**Proof sketch.** The host sees exactly the source's active symbols. Apply
the forwarded-action identity once per live source step and induct; the source
may halt on the final action, after that action's emission is forwarded. -/
private lemma emLoop_forward_run {k : ℕ} {S H : Type} {x : List Bool}
    (src : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → H) (ret : H)
    (hagree : ∀ q inp work, host.tr (emb q) inp work =
      leftAction 1 id (Turing.emitAction emb ret (src.tr q inp (fun i => work i.castSucc))))
    (pre : List Bool) (c : Cfg k Bool S x) (t : ℕ)
    (hlive : ∀ j < t, (src.runFrom c j).state ≠ none) :
    host.runFrom (emLoopForwardCfg emb ret pre c) t =
      emLoopForwardCfg emb ret pre (src.runFrom c t) := by
  have hs (d : Cfg k Bool S x) (hd : d.state ≠ none) :
      host.step (emLoopForwardCfg emb ret pre d) =
        emLoopForwardCfg emb ret pre (src.step d) := by
    cases hq : d.state with
    | none => exact False.elim (hd hq)
    | some q =>
      have hstate : (emLoopForwardCfg emb ret pre d).state = some (emb q) := by
        simp [emLoopForwardCfg, leftCfg, Turing.emitCfg, hq]
      have hwork : (fun i => (emLoopForwardCfg emb ret pre d).workTapeSymbols i.castSucc) =
          d.workTapeSymbols := by
        funext i
        simp [emLoopForwardCfg, leftCfg, Turing.emitCfg, Cfg.workTapeSymbols,
          Fin.addCases, i.isLt]
      have hin : (emLoopForwardCfg emb ret pre d).inputSymbol = d.inputSymbol := rfl
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hwork, hin]
      exact emLoop_forward_apply emb ret pre _ d
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      hs _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- The forwarding call stores output physically and keeps the former payload
tape blank at zero. All body, counter, and fuel data use the existing layout. -/
private def emLoopCall (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (pre : List Bool) (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x :=
  emLoopForwardCfg (fun s => .inr (.inl (startup, s)))
    (.inr (.inr (if startup then 6 else 7 : Fin 14))) pre
    (loopBodyPadded body F anchor c release flag word fuel)

/-- A forwarding call is the old clean-payload frame with the exact output
prefix installed physically. This is a configuration identity only; no old
capturing-body run is reused. -/
private lemma emLoopCall_frame (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (pre : List Bool) (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    emLoopCall body F anchor pre startup c release flag word fuel =
      { loopCall body F anchor startup {c with output := []} release flag word fuel
        with output := pre ++ c.output } := by
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [emLoopCall, emLoopForwardCfg, leftCfg, Turing.emitCfg, loopCall, captureCfg,
      loopBodyPadded, loopBodyCfg]
  · funext i
    simp [emLoopCall, emLoopForwardCfg, leftCfg, Turing.emitCfg, loopCall, captureCfg,
      loopBodyPadded, loopBodyCfg, Fin.addCases]
    split_ifs <;> rfl
  · funext i
    simp [emLoopCall, emLoopForwardCfg, leftCfg, Turing.emitCfg, loopCall, captureCfg,
      loopBodyPadded, loopBodyCfg, Fin.addCases]
    split_ifs <;> rfl

/-- Forward the complete stopped-body run, including its silent anchor-stop
transition, into the new host. -/
private lemma emLoopHost_body_forward (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (pre : List Bool) (c : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) (t : ℕ)
    (hlive : ∀ u < t, ¬((loopBodySource body F anchor).runFrom c u).Halted) :
    (emLoopHost body F anchor findMode).tm.runFrom
      (emLoopForwardCfg (fun s => .inr (.inl (startup, s)))
        (.inr (.inr (if startup then 6 else 7 : Fin 14))) pre c) t =
      emLoopForwardCfg (fun s => .inr (.inl (startup, s)))
        (.inr (.inr (if startup then 6 else 7 : Fin 14))) pre
        ((loopBodySource body F anchor).runFrom c t) := by
  exact emLoop_forward_run (loopBodySource body F anchor) (emLoopHost body F anchor findMode).tm
    _ _ (by intros; rfl) pre c t hlive

/-- A live anchor endpoint is forwarded after one additional stop step.
The exact endpoint keeps every inactive tape and carries the false stop flag.
**Proof sketch.** The live endpoint rules out earlier halts. Use the source
wrapper simulation up to that endpoint, take its silent anchor-stop step,
and lift the resulting run through the padded source and actual host forwarding.
The guard at time zero is supplied by the release bit for active calls. -/
private lemma emLoopHost_anchor_return (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) (pre : List Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hend : (body.tm.runFrom c t).state = some anchor)
    (hreleased : t = 0 → release = false)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (emLoopHost body F anchor findMode).tm.runFrom
        (emLoopCall body F anchor pre startup c release none word fuel) (t + 1) =
      emLoopCall body F anchor pre startup {body.tm.runFrom c t with state := none}
        false (some false) word fuel := by
  have hlive : ∀ u ≤ t, (body.tm.runFrom c u).state ≠ none :=
    loop_live_prefix body.tm c t (by rw [hend]; simp)
  have hc : c.state ≠ none := by simpa using hlive 0 (Nat.zero_le _)
  have hr : (loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none) t =
      loopBodyCfg body anchor (body.tm.runFrom c t) false none := by
    rw [loopBody_run body anchor c release hc t
      (fun u hu => hlive u (by omega)) hanchor]
    have hn := hlive t (le_refl _)
    rw [if_neg hn]
    by_cases ht : t = 0
    · rw [if_pos ht, hreleased ht]
    · rw [if_neg ht]
  have hstop : (loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none)
      (t + 1) =
      loopBodyCfg body anchor {body.tm.runFrom c t with state := none} false (some false) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hr, loopBody_stop body anchor _ hend]
  unfold emLoopCall loopBodyPadded
  rw [emLoopHost_body_forward]
  · rw [loopBodySource_run, hstop]
  · intro u hu
    rw [loopBodySource_run, loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, leftCfg, loopBodyCfg] using hlive u (by omega)

/-- On a silent source seam, forwarding with an empty prefix coincides with
the old clean-payload configuration. -/
private lemma emLoopCall_empty (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (startup : Bool) (c : Cfg body.k Bool body.State x) (release : Bool)
    (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.output = []) :
    emLoopCall body F anchor [] startup c release flag word fuel =
      loopCall body F anchor startup c release flag word fuel := by
  rw [emLoopCall_frame, List.nil_append, hc]
  have he : {c with output := []} = c := by cases c; simp_all
  rw [he]
  rfl

/-- Silent startup in the forwarding host reaches the first released round
without debiting fuel. Only the body execution is new; the release action is
the inherited silent administrative action. -/
private lemma emLoopHost_start (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s : List Bool) (t : ℕ)
    (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s)) :
    (emLoopHost body F anchor findMode).tm.runFrom (loopReady body F fuel) (t + 2) =
      loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
        true none fuel.output fuel := by
  have hi := emLoopCall_empty body F anchor true (body.tm.initCfg x) false none fuel.output fuel rfl
  have hr := emLoopHost_anchor_return body F anchor findMode true [] (body.tm.initCfg x)
    false t fuel.output fuel (by rw [hend]; rfl) (fun _ => rfl)
    (fun u hu => Or.inr (hguard u hu))
  rw [hi, hend, emLoopCall_empty body F anchor true _ false (some false) fuel.output fuel rfl] at hr
  rw [loopReady_call body F anchor, show t + 2 = (t + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hr, emLoopHost_release]
  rfl

/-- A forwarding round appends its exact chunk, then performs the silent
fixed-width debit. Positive fuel reaches the next clean seam; underflow
halts with the chunk and no verdict bit.
**Proof sketch.** Forward the source round and its anchor-stop action. Its
entire data endpoint is the old clean-payload frame with the chunk in physical
output. Prefix commutation lifts the proved silent countdown to that output.
The underflow transition is charged inside this same final segment. -/
private lemma emLoopHost_round (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (s next chunk word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (t : ℕ) (ht : 0 < t)
    (hanchor : ∀ u, 0 < u → u < t →
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u).state ≠ some anchor)
    (hend : body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
      { Cfg.ofWords (input := x) anchor (stateWord body.k next) with output := chunk }) :
    ∃ v ≤ t + 2 * word.length + 5,
      if (loopDebit word).2 then
        (emLoopHost body F anchor true).tm.runFrom
          (loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel) v =
          {loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k next))
            true none (loopDebit word).1 fuel with output := chunk}
      else
        ((emLoopHost body F anchor true).tm.runFrom
          (loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel) v).state = none ∧
        ((emLoopHost body F anchor true).tm.runFrom
          (loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel) v).output = chunk := by
  let c := Cfg.ofWords (input := x) anchor (stateWord body.k s)
  let d := Cfg.ofWords (input := x) anchor (stateWord body.k next)
  have hguard : ∀ u < t, (u = 0 ∧ true = true) ∨ (body.tm.runFrom c u).state ≠ some anchor := by
    intro u hu
    by_cases hz : u = 0
    · exact Or.inl ⟨hz, rfl⟩
    · exact Or.inr (hanchor u (by omega) hu)
  have hr := emLoopHost_anchor_return body F anchor true false [] c true t word fuel
    (by rw [hend]; rfl) (by intro h; omega) hguard
  rw [emLoopCall_empty body F anchor false c true none word fuel rfl, hend, emLoopCall_frame] at hr
  change (emLoopHost body F anchor true).tm.runFrom
      (loopCall body F anchor false c true none word fuel) (t + 1) =
      {loopCall body F anchor false {d with state := none} false (some false) word fuel
        with output := chunk} at hr
  obtain ⟨v, hv, hc⟩ := emLoopHost_reject body F anchor true
    {d with state := none} word fuel rfl rfl
  let admin := loopCall body F anchor false {d with state := none} false (some false) word fuel
  have hp := emLoop_run_prefix (emLoopHost body F anchor true).tm chunk admin v
  have hao : admin.output = [] := rfl
  rw [hao, List.append_nil] at hp
  refine ⟨(t + 1) + v, by omega, ?_⟩
  by_cases hb : (loopDebit word).2 = true
  · simp only [hb, if_true] at hc ⊢
    rw [MultiTapeTM.runFrom_add, hr, hp]
    rw [hc]
    refine Cfg.ext rfl rfl rfl rfl ?_
    change chunk ++ [] = chunk
    exact List.append_nil _
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    rw [MultiTapeTM.runFrom_add, hr, hp]
    have hco : ((emLoopHost body F anchor true).tm.runFrom admin v).output = [] := hc.2
    exact ⟨hc.1, by simp only [hco, List.append_nil]⟩

/-- Sum consecutive emitting segments from arbitrary accumulated output.
Each segment contributes its exact chunk, and the final segment halts.
**Proof sketch.** Induct on the number of rounds. Prefix commutation turns
the next clean-seam segment into a segment after the preceding chunks.
Concatenation follows the same order as the configuration indices. This is
a new summation lemma; the frozen empty-output `loop_run` is not used. -/
private lemma emLoop_sum {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (chunk : ℕ → List Bool) (B : ℕ) : ∀ N,
    (∀ i < N, (cfg i).output = []) →
    (∀ i < N, ∃ t ≤ B,
      if i + 1 < N then tm.runFrom (cfg i) t = {cfg (i + 1) with output := chunk i}
      else (tm.runFrom (cfg i) t).state = none ∧ (tm.runFrom (cfg i) t).output = chunk i) →
    0 < N → ∀ pre, ∃ t ≤ N * B,
      (tm.runFrom {cfg 0 with output := pre} t).state = none ∧
      (tm.runFrom {cfg 0 with output := pre} t).output =
        pre ++ (List.range N).flatMap chunk := by
  intro N
  induction N generalizing cfg chunk with
  | zero => intro _ _ h; omega
  | succ N ih =>
    intro hout hseg _ pre
    obtain ⟨a, ha, he⟩ := hseg 0 (by omega)
    have hp := emLoop_run_prefix tm pre (cfg 0) a
    rw [hout 0 (by omega), List.append_nil] at hp
    cases N with
    | zero =>
      simp only [Nat.lt_irrefl, ↓reduceIte] at he
      refine ⟨a, by simpa using ha, ?_, ?_⟩
      · rw [hp]; exact he.1
      · rw [hp]; simp [he.2]
    | succ N =>
      simp only [show 0 + 1 < (N + 1) + 1 by omega, ↓reduceIte] at he
      rw [he] at hp
      obtain ⟨b, hb, hh, ho⟩ := ih (fun i => cfg (i + 1)) (fun i => chunk (i + 1))
        (fun i hi => hout (i + 1) (by omega))
        (fun i hi => by
          obtain ⟨t, ht, h⟩ := hseg (i + 1) (by omega)
          exact ⟨t, ht, by simpa only [Nat.add_lt_add_iff_right] using h⟩)
        (by omega) (pre ++ chunk 0)
      refine ⟨a + b, by rw [Nat.succ_mul]; omega, ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_add, hp]
        exact hh
      · rw [MultiTapeTM.runFrom_add, hp, ho]
        rw [List.range_succ_eq_map (n := N + 1), List.flatMap_cons, List.flatMap_map]
        simp [List.append_assoc, Function.comp_def]

/-- **E1, the emitting loop** (spec, fill pending — design §11; customers:
the Cook-Levin clause-group emitter (4A), 3B-cont's streaming reduction
transducer, 4B's dual-reduction emitter). The emitting sibling of
`Turing.FinTM.exists_loopCfgTM`: the same anchored round discipline —
startup within the envelope and no earlier anchor visit; per-round
positive duration, anchor exclusion, and input-length-only budgets — but
each round, instead of staying silent and either accepting or advancing,
**advances and appends its exact chunk** `emitF x s` to the physical
output. The machine runs all `R + 1` rounds and computes the
concatenation of the chunks in order. There is no verdict bit and no
deciding variant: compose with the existing decision layer instead
(design §11 non-goals).

Each round's seam is stated from the canonical clean configuration; the
round equality itself bounds the chunk length by the round's duration
(output grows by at most one symbol per step), so no separate emission
bound is hypothesized.

**Construction sketch** (corrected per the emitter-infra round-1 audit,
finding 3: the unchanged find-mode host routes body actions through
`captureAction`, whose physical output is always `none`, so captured
chunks never reach the physical output — a one-state self-emitting body
refutes the literal reuse). Build a **forwarding host variant**: the
same skeleton with the body dispatched through `Turing.emitAction`
(chunks land on the physical output), the fuel capture and silent
countdown machinery reused as they stand. Its contracts are proved over
configurations with arbitrary accumulated output (runs commute with
output prefixes — the transition table never reads the output tape),
and the concatenation is threaded through a **new** prefix-summation
lemma modeled on `loop_run`; the frozen empty-output `loop_run` itself
is not reusable for this.

**Batch L completion.** The forwarding host is `emLoopHost`; its body branch
uses `Turing.emitAction`, while fuel capture and the silent debit keep their
original behavior. `emLoop_run_prefix` proves arbitrary-prefix commutation;
`emLoopHost_round` charges the complete round, anchor stop, debit, and final
underflow. The new `emLoop_sum` concatenates exactly rounds `0..R` (including
one round at zero fuel), without using or changing the empty-output summation
lemma. Silent startup plus these `R + 1` segments satisfies the coefficient
`10` in the audited envelope. Every supporting dependency is proved. -/
theorem exists_emitLoopTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF emitF : List Bool → List Bool → List Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        body.tm.runFrom
          (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
            { Cfg.ofWords (input := x) anchor (stateWord body.k (stepF x s))
                with output := emitF x s }) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => (List.range (R x.length + 1)).flatMap
          (fun i => emitF x ((stepF x)^[i] (s0 x))))
        (fun n => c * (T n + 1) * (R n + 2)) := by
  let E := emLoopHost body F anchor true
  refine ⟨E, 10, fun x => ?_⟩
  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare⟩ :=
    emLoopHost_prepare body F anchor true R T hF x
  obtain ⟨btime, hbt, hbguard, hbend⟩ := hstart x
  let words (i : ℕ) := (fun w => (loopDebit w).1)^[i] (Nat.bits (R x.length))
  let orbit (i : ℕ) := (stepF x)^[i] (s0 x)
  let candidate (i : ℕ) := loopCall body F anchor false
    (Cfg.ofWords (input := x) anchor (stateWord body.k (orbit i))) true none (words i) fuel
  have hwidth (i : ℕ) : (words i).length ≤ T x.length := by
    dsimp only [words]
    rw [loopDebit_iterate_length]
    exact loop_fuel_width F R T hF x
  have hsuccess (i : ℕ) (hi : i ≤ R x.length) :
      (loopDebit (words i)).2 = true ↔ i < R x.length := by
    rw [loopDebit_success]
    dsimp only [words]
    rw [loopDebit_iterate_value _ _ hi]
    omega
  have hsegments : ∀ i < R x.length + 1, ∃ t ≤ 10 * (T x.length + 1),
      if i + 1 < R x.length + 1 then
        E.tm.runFrom (candidate i) t = {candidate (i + 1) with output := emitF x (orbit i)}
      else
        (E.tm.runFrom (candidate i) t).state = none ∧
        (E.tm.runFrom (candidate i) t).output = emitF x (orbit i) := by
    intro i hi
    obtain ⟨t, htpos, ht, hguard, hend⟩ := hround x (orbit i)
      (loop_orbit_inv Inv stepF s0 hInv0 hInvStep x i)
    obtain ⟨v, hv, hsegment⟩ := emLoopHost_round body F anchor
      (orbit i) (stepF x (orbit i)) (emitF x (orbit i)) (words i) fuel t htpos hguard hend
    refine ⟨v, ?_, ?_⟩
    · have hw := hwidth i
      omega
    · simpa only [E, candidate, words, orbit, Function.iterate_succ_apply',
        hsuccess i (by omega), Nat.add_lt_add_iff_right] using hsegment
  let startup := ftime + (btime + 2)
  have hs : startup ≤ 10 * (T x.length + 1) := by dsimp only [startup]; omega
  have hinit : E.tm.runFrom (E.tm.initCfg x) startup = candidate 0 := by
    rw [MultiTapeTM.runFrom_add, hprepare,
      emLoopHost_start body F anchor true (s0 x) btime fuel hbguard hbend]
    simp only [candidate, words, orbit, Function.iterate_zero_apply, hfo]
  obtain ⟨t, ht, hhalt, houtput⟩ := emLoop_sum E.tm candidate
    (fun i => emitF x (orbit i)) (10 * (T x.length + 1)) (R x.length + 1)
    (fun _ _ => rfl) hsegments (by omega) []
  have hclean : {candidate 0 with output := []} = candidate 0 := rfl
  rw [hclean] at hhalt houtput
  have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
  rw [hinit] at hrun
  have hcompute : E.ComputesInTime x
      ((List.range (R x.length + 1)).flatMap (fun i => emitF x ((stepF x)^[i] (s0 x))))
      (startup + t) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun]; exact hhalt
    · rw [hrun]; simpa only [List.nil_append, orbit] using houtput
  apply hcompute.mono
  calc startup + t ≤ 10 * (T x.length + 1) +
        (R x.length + 1) * (10 * (T x.length + 1)) := Nat.add_le_add hs ht
    _ = 10 * (T x.length + 1) * (R x.length + 2) := by
      rw [Nat.mul_comm (R x.length + 1)]
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
      omega

/-- **E5a, the install-mode clean call** (spec, added at the emitter-infra
round-1 repair — finding 1's prepared-input/clean-return bridge;
customers: loop and emit-loop bodies calling a catalog transducer on
their tape-resident data, in particular `computesFunInTime_splitSolveWith`'s
evaluator rounds and 3B-cont's token/counter installs). A function-level
contract says nothing about a witness's terminal heads or scratch — a
machine may dirty a tape on its final transition and still compute `f`
within `T` — so the bridge supplies what the function contract cannot:
for any such witness, a **callable module** with designated entry and
exit states whose entry and exit are both the canonical clean seam. From
`Cfg.ofWords entry (stateWord C.k arg)` — the argument as the sole
tape-resident word, every other tape blank, input head at one, empty
output, over an **arbitrary, untouched** native input — the module
reaches, at its first positive visit to `exit`, exactly
`Cfg.ofWords exit (stateWord C.k (f arg))`: the result installed, all
scratch restored, nothing emitted.

**Construction sketch** (attribution corrected per the emitter-infra
round-3 audit, finding 1). Prepare a virtual input from the
tape-resident argument (the relocated-read discipline of the proved
hosts); run the witness through the capture wrapper over **tracked
banks** — the A-continuation's proved visited-interval/origin-marker
family (`e3cTrackTM`/`e3c_track_run`, `e3cClearTM`/`e3c_clear_run`) —
then sequence the per-triple cleaner over the fixed `M.k` banks: at a
clean entry seam the module's scratch starts blank, so clearing the
tracked interval **is** the restoration, and no overwritten-symbol
history is needed; install the captured result on tape zero (or replay
it, in emit mode); erase the capture; rewind. The history/undo
alternative remains valid independently (round-2 audit, finding 4),
but is not what the delivered continuation proves. Every phase is
charged to `T`, the argument length, or the result length.

The `0 < C.k` clause is load-bearing (emitter-infra round-2 audit,
finding 1): at tape count zero, `stateWord 0 a = stateWord 0 b` for all
`a, b` — the empty-domain degeneracy — and a two-state zero-tape machine
would satisfy the rest of this conclusion for an arbitrary, even
noncomputable, `f`. The positive tape count makes the seam equality
yield `bufferTape (f arg)` at the genuine index zero, so the installed
result is actually extractable by the caller.

**Batch L completion.** `emCallTM M false` reserves a genuine argument tape,
executes the prepared input through tracked banks, and sequences every
triple cleaner after the observed evaluator return. Since scratch starts
blank, clearing the visited intervals restores the complete clean seam.
`emCall_complete` charges evaluation, bank dispatch/cleanup, result install,
capture erasure, and rewinds within coefficient `24 + 13 * M.k` (the ledger's
`6 + 13 * M.k + 3 * K` with `K = 6`). `emCall_first` cuts at the first visit
to a fresh absorbing exit; no time bound occurs in the transition table. -/
theorem exists_installCallTM (M : FinTM Bool) (f : List Bool → List Bool)
    (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    ∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧
      ∀ (x arg : List Bool),
        ∃ t ≤ c * (T arg.length + arg.length + (f arg).length + 1),
          0 < t ∧
          (∀ t', 0 < t' → t' < t →
            (C.tm.runFrom
              (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state
                ≠ some exit) ∧
          C.tm.runFrom
            (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
              Cfg.ofWords exit (stateWord C.k (f arg)) := by
  refine ⟨emCallTM M false, (emCallTM M false).tm.q₀, .inr (.inr 5),
    24 + 13 * M.k, ?_, ?_⟩
  · exact Nat.zero_lt_succ _
  · intro x arg
    obtain ⟨t, ht, hpos, hfirst, hr⟩ := emCall_first M false x arg (f arg) (T arg.length) (hM arg)
    refine ⟨t, ht, hpos, fun j _ hj => hfirst j hj, ?_⟩
    simpa using hr

/-- **E5b, the emit-mode clean call** (spec, added at the emitter-infra
round-1 repair — the forwarding half of finding 1's bridge; customers:
`exists_emitLoopTM` bodies emitting per-round chunks computed by a
catalog transducer — 3B-cont's clause fragments, 4A's clause groups).
Identical seam discipline to the install call, but the computed word is
**forwarded to the physical output** and the tape-resident argument is
preserved: from `Cfg.ofWords entry (stateWord C.k arg)`, the module
reaches, at its first positive visit to `exit`, exactly the entry seam
with `exit` control and output `f arg` — argument intact, scratch
restored, the chunk emitted.

**Construction sketch.** As the install call, with the captured result
replayed through `Turing.emitAction`-style forwarding and then erased,
instead of installed; the argument word is never consumed. The
`0 < C.k` clause mirrors the install call's (round-2 finding 1): the
physical output prevents the zero-tape degeneracy for nonconstant `f`,
but the preserved tape-resident argument is a promise of this
interface too, and it needs a genuine tape to live on.

**Batch L completion.** `emCallTM M true` uses the same tracked evaluation
and observed-completion cleanup as install mode. Its finishing pass preserves
the argument, replays the captured result onto physical output, erases the
capture, and restores every head. `emCall_complete` proves the full endpoint
and the same coefficient `24 + 13 * M.k`; `emCall_first` proves the first
positive exit condition, including empty arguments and empty results. -/
theorem exists_emitCallTM (M : FinTM Bool) (f : List Bool → List Bool)
    (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    ∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧
      ∀ (x arg : List Bool),
        ∃ t ≤ c * (T arg.length + arg.length + (f arg).length + 1),
          0 < t ∧
          (∀ t', 0 < t' → t' < t →
            (C.tm.runFrom
              (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state
                ≠ some exit) ∧
          C.tm.runFrom
            (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
              { Cfg.ofWords (input := x) exit (stateWord C.k arg)
                  with output := f arg } := by
  refine ⟨emCallTM M true, (emCallTM M true).tm.q₀, .inr (.inr 5),
    24 + 13 * M.k, ?_, ?_⟩
  · exact Nat.zero_lt_succ _
  · intro x arg
    obtain ⟨t, ht, hpos, hfirst, hr⟩ := emCall_first M true x arg (f arg) (T arg.length) (hM arg)
    refine ⟨t, ht, hpos, fun j _ hj => hfirst j hj, ?_⟩
    simpa using hr

end Turing.FinTM
