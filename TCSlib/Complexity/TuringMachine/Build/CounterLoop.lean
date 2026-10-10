/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Equiv.Bool
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: counter-driven loops (§12.7)

The §12.7 increment of the machine-construction library
(`machine-library-design.md` §12.7): a loop whose number of rounds is a
little-endian binary counter **read from a tape**, running a body whose
state lives on **persistent, arbitrarily positioned tapes**. Every public
loop host of `Build/Loop.lean` instead runs a number of rounds fixed by the
input length, between canonical `Turing.Cfg.ofWords` seams. The consumers
are the two-tape uniform machine-code scheme (`Codes2Tape`), the EXPCOM
simulation, the nondeterministic time hierarchy (a fused countdown at
linear overhead) and the space hierarchy's configuration-count clock.

**Status: statement skeleton (§12.7 statement phase).** All definitions
are real; every contract is sorried, each with a proof sketch naming its
fill obligations.

## Design (decisions 12.7.1–12.7.6, user 2026-10-10)

* **Symbol transport** (`Turing.MultiTapeTM.mapWorkSymbols`). A machine
  conjugated by a permutation of the work-tape alphabet runs as the
  original, cell for cell, from every configuration. This is the generic
  route of decision 12.7.4, so the decrement proof never copies the
  increment proof.
* **C1, decrement** (`Turing.decrementTM`). It is defined as
  `Turing.incrementTM` conjugated by bit complement, and its framed
  contracts are the §12.6 increment contracts transported.
* **C2, the counter-driven host** (`Turing.counterLoopTM`). The body's `k`
  tapes are embedded by R1 along `Fin.castSucc`, and the counter is the
  dedicated last tape (12.7.1). Arriving at the anchor starts a decrement,
  and success re-enters the body at the anchor, with no dispatch steps.
  Underflow leaves through the live anchor `done`; reaching the optional
  designated body exit leaves through the live anchor `escape` (12.7.2).
  A consumer branches on the two exits with `Turing.seamCompTM`; with no
  exit (`none`), `escape` is unreachable.
* **Round cost** (12.7.3). Each round from body configuration `c` lasts
  the **exact** time `τ c`. A round-indexed cost is the special case of
  `τ` along the orbit, and a uniform bound is the corollary
  `Turing.counterLoop_time_le`.
* **Amortized time** (12.7.6). The total is stated exactly over the whole
  run. The decrements' share, `Turing.counterOverhead`, is at most four
  steps per round plus one sweep of the counter.

## Main definitions

* `Turing.MultiTapeTM.mapWorkSymbols` — conjugation by a work-tape symbol
  permutation, with `Turing.Action.mapWorkSymbols` and
  `Turing.Cfg.mapWorkSymbols`.
* `Turing.decFixed`, `Turing.decrementTM` — fixed-width decrement, as a
  word function and as a machine.
* `Turing.counterWord`, `Turing.counterOverhead` — the counter after `r`
  decrements, and the exact cost of the first `r` decrements.
* `Turing.CounterLoopState`, `Turing.counterLoopTM`,
  `Turing.counterLoopCfg`, `Turing.counterLoopOrbit` — the host, its
  configurations, and the body's round-start configurations.

## Main results

All sorried (statement phase):

* `Turing.MultiTapeTM.mapWorkSymbols_runFrom` — symbol transport.
* `Turing.decrementTM_run_succ_ofCfg`, `Turing.decrementTM_run_underflow_ofCfg`
  — the framed decrement contracts, in the §12.6 shape.
* `Turing.counterWord_length`, `Turing.counterWord_value`,
  `Turing.counterOverhead_le_of_le`, `Turing.counterOverhead_le` — counter
  arithmetic, including the amortized bound.
* `Turing.counterLoopTM_run_done`, `Turing.counterLoopTM_run_escape` — the
  host's exact whole-run contracts, with no earlier exit, the counter
  head's range, and the body heads' trajectory.
* `Turing.counterLoop_time_le` — the uniform per-round bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1–§3.2 and §4.1: the hierarchy
  arguments run a universal machine for a bounded number of steps under a
  step counter; this file is that counter as a reusable machine.)

**Fill appendix (§12.7).** All ten contracts are now proved. The historical
statement-phase status labels above are retained under the docstring freeze.
Decrement is transported from increment once; `counter_rounds` is the single
round induction used by both host contracts. Its final state is unrestricted,
so it covers returning prefixes and the last escaping round with the same
trajectory invariant. The amortization proofs use the audit's bit-count
potential, as recorded in their fill appendices.
-/

namespace Turing

section SymbolTransport

variable {k : ℕ} {Symbol State : Type*}

/-- Rename the symbols an action writes on its work tapes along an
equivalence. Input movement, output and successor state are unchanged. -/
def Action.mapWorkSymbols (e : Symbol ≃ Symbol) (a : Action k Symbol State) :
    Action k Symbol State where
  inputTape := a.inputTape
  workTapes := fun j => ((a.workTapes j).1.map (Option.map e), (a.workTapes j).2)
  output := a.output
  state := a.state

/-- Rename every work-tape cell of a configuration along an equivalence;
blank cells stay blank. -/
def Cfg.mapWorkSymbols {input : List Symbol} (e : Symbol ≃ Symbol)
    (c : Cfg k Symbol State input) : Cfg k Symbol State input :=
  { c with workTapes := fun j p => (c.workTapes j p).map e }

/-- Conjugate a machine by a work-tape symbol permutation: read the work
tapes through `e.symm` and write through `e`. The input tape and the output
are not renamed. -/
def MultiTapeTM.mapWorkSymbols (M : MultiTapeTM k Symbol State)
    (e : Symbol ≃ Symbol) : MultiTapeTM k Symbol State where
  q₀ := M.q₀
  tr := fun q inp work => (M.tr q inp fun j => (work j).map e.symm).mapWorkSymbols e

/-- One step commutes with work-symbol conjugation, including writes into the frame.
**Proof sketch.** Inverse decoding cancels the equivalence at each read.
On the written cell the renamed update stores the renamed symbol; off that
cell the original tape is retained. The remaining configuration fields agree. -/
private lemma counter_work_step (M : MultiTapeTM k Symbol State) (e : Symbol ≃ Symbol)
    {input : List Symbol} (d : Cfg k Symbol State input) :
    (M.mapWorkSymbols e).step (d.mapWorkSymbols e) = (M.step d).mapWorkSymbols e := by
  cases hs : d.state with
  | none => simp [MultiTapeTM.step, Cfg.mapWorkSymbols, hs]
  | some s =>
    have reads : (fun j => ((d.workTapeSymbols j).map e).map e.symm) =
        d.workTapeSymbols := by
      funext j
      cases d.workTapeSymbols j <;> simp
    simp only [MultiTapeTM.step, Cfg.mapWorkSymbols, hs]
    change ((M.tr s d.inputSymbol (fun j =>
        ((d.workTapeSymbols j).map e).map e.symm)).mapWorkSymbols e).apply
        (d.mapWorkSymbols e) = _
    rw [reads]
    apply Cfg.ext <;> try rfl
    funext j p
    simp only [Action.apply, Action.mapWorkSymbols, Cfg.mapWorkSymbols]
    cases hw : (M.tr s d.inputSymbol d.workTapeSymbols).workTapes j |>.1 with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      by_cases hp : p = d.workTapePos j
      · subst p; simp
      · simp [Function.update_of_ne hp]

/-- **Symbol transport** (design §12.7, decision 12.7.4). From every
configuration and at every time, the conjugated machine runs as the original
with every work-tape cell renamed.

**Proof sketch.** One step: the conjugate reads `e.symm (e s) = s`, so it
chooses the original's action; writing renamed symbols commutes with
`Function.update`; heads, input position, output and state are copied. Then
`Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem MultiTapeTM.mapWorkSymbols_runFrom (M : MultiTapeTM k Symbol State)
    (e : Symbol ≃ Symbol) {input : List Symbol} (c : Cfg k Symbol State input)
    (t : ℕ) :
    (M.mapWorkSymbols e).runFrom (c.mapWorkSymbols e) t =
      (M.runFrom c t).mapWorkSymbols e := by
  exact MultiTapeTM.runFrom_comm_of_step (fun d => d.mapWorkSymbols e)
    (counter_work_step M e) c t

end SymbolTransport

/-! ## C1 — decrement -/

/-- Little-endian fixed-width binary decrement with explicit underflow, the
mirror of `Turing.incFixed`: `decFixed w` is the predecessor word of the same
length, or `none` when `w` is all `false`, that is, has value zero. Width zero
underflows immediately. -/
def decFixed : List Bool → Option (List Bool)
  | [] => none
  | true :: rest => some (false :: rest)
  | false :: rest => (decFixed rest).map (true :: ·)

/-- Complement exchanges the word-level carry and borrow recursions. -/
private lemma counter_dec_complement (w : List Bool) :
    decFixed w = (incFixed (w.map not)).map (List.map not) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [decFixed, incFixed, ih, List.map_map, Function.comp_def]

/-- Complementing work cells twice restores an arbitrary configuration. -/
private lemma counter_complement_twice {k : ℕ} {S : Type} {x : List Bool}
    (d : Cfg k Bool S x) :
    (d.mapWorkSymbols Equiv.boolNot).mapWorkSymbols Equiv.boolNot = d := by
  apply Cfg.ext <;> try rfl
  funext j p
  simp [Cfg.mapWorkSymbols, Option.map_map, Function.comp_def]

/-- Complementation of a buffered word preserves its blank delimiters. -/
private lemma counter_buffer_complement (w : List Bool) (p : ℤ) :
    FinTM.bufferTape (w.map not) p = (FinTM.bufferTape w p).map not := by
  by_cases hp : 0 ≤ p <;> simp [FinTM.bufferTape, hp]

/-- **R3, decrement** (design §12.7, C1). In-place little-endian fixed-width
binary decrement on tape `i`. The borrow pass flips `false` cells to `true`
moving right. The first `true` flips to `false` and selects the success
verdict. Running off the width (all `false`, value zero) selects the
underflow verdict, leaving the wrapped all-`true` word. The return pass
carries the verdict to the live `done` anchor at the origin.

It is defined as `Turing.incrementTM` conjugated by bit complement, so its
contracts are the increment's, transported by
`Turing.MultiTapeTM.mapWorkSymbols_runFrom`. -/
def decrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase :=
  (incrementTM k i).mapWorkSymbols Equiv.boolNot

/-- Every decrement run is one complemented increment run, including its frame. -/
private lemma counter_decrement_run {k : ℕ} {x : List Bool} (i : Fin k)
    (d : Cfg k Bool FlagPhase x) (t : ℕ) :
    (decrementTM k i).runFrom d t =
      ((incrementTM k i).runFrom (d.mapWorkSymbols Equiv.boolNot) t).mapWorkSymbols
        Equiv.boolNot := by
  simpa only [decrementTM, counter_complement_twice] using
    (incrementTM k i).mapWorkSymbols_runFrom Equiv.boolNot
      (d.mapWorkSymbols Equiv.boolNot) t

/-- **Decrement, framed success with exact borrow cost** (design §12.7, C1;
the mirror of `Turing.incrementTM_run_succ_ofCfg`). Let the delimited word `w`
on tape `i` have a predecessor at its width, `decFixed w = some v`, and let
`q = (w.takeWhile not).length` be its number of leading `false` cells. Then
the routine reaches the success anchor at exactly `2q + 2` and not earlier,
with the word interval holding `v` and everything else unchanged. Up to the
exit the head stays within `[pos - 1, pos + q]`.

**Proof sketch.** Complement the configuration's work tapes. The result
carries `w.map not`, whose successor is `v.map not` (`decFixed` is `incFixed`
conjugated by `not`) and whose `true` prefix has length `q`. Apply
`Turing.incrementTM_run_succ_ofCfg`, transport back by
`Turing.MultiTapeTM.mapWorkSymbols_runFrom`, and use that complementing
twice is the identity and that `FinTM.bufferTape` commutes with `map not`. -/
theorem decrementTM_run_succ_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w v : List Bool) (hv : decFixed w = some v) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (decrementTM k i).runFrom d (2 * (w.takeWhile not).length + 2) =
        { d with
          state := some (FlagPhase.done true)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape v (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * (w.takeWhile not).length + 2, ∀ b : Bool,
        ((decrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * (w.takeWhile not).length + 2 →
        if j = i then
          ((decrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1)
              (d.workTapePos j + ((w.takeWhile not).length : ℤ))
        else ((decrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hv' : incFixed (w.map not) = some (v.map not) := by
    have h := congrArg (Option.map (List.map not)) hv
    simpa [counter_dec_complement, Option.map_map, List.map_map, Function.comp_def] using h
  have hf : ∀ p : ℤ, -1 ≤ p → p ≤ ((w.map not).length : ℤ) →
      (d.mapWorkSymbols Equiv.boolNot).workTapes i
        ((d.mapWorkSymbols Equiv.boolNot).workTapePos i + p) =
          FinTM.bufferTape (w.map not) p := by
    intro p hl hr
    simpa [Cfg.mapWorkSymbols, counter_buffer_complement] using
      congrArg (Option.map not) (hw p hl (by simpa using hr))
  have hp : ((w.map not).takeWhile id).length = (w.takeWhile not).length := by
    simp [List.takeWhile_map, Function.comp_def]
  obtain ⟨he, hc, hh⟩ := incrementTM_run_succ_ofCfg i (w.map not) (v.map not)
    hv' (d.mapWorkSymbols Equiv.boolNot) hstate hf
  rw [hp] at he hc hh
  refine ⟨?_, ?_, ?_⟩
  · rw [counter_decrement_run, he]
    apply Cfg.ext <;> try rfl
    funext j p
    simp only [Cfg.mapWorkSymbols, List.length_map]
    split_ifs <;> simp [counter_buffer_complement, Option.map_map, Function.comp_def]
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hc
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh

/-- **Decrement, framed underflow** (design §12.7, C1; the mirror of
`Turing.incrementTM_run_overflow_ofCfg`). If the delimited word `w` on tape
`i` has no predecessor at its width (`decFixed w = none`, that is, it is all
`false`), the routine reaches the underflow anchor at exactly `2|w| + 2` and
not earlier. The word interval then holds `|w|` copies of `true`, and
everything else is unchanged. Up to the exit the head stays within
`[pos - 1, pos + |w|]`.

**Proof sketch.** As the success case, through
`Turing.incrementTM_run_overflow_ofCfg`: the complemented word is all `true`,
so `incFixed` overflows, and the wrapped all-`false` word complements back to
all `true`. -/
theorem decrementTM_run_underflow_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w : List Bool) (hv : decFixed w = none) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (decrementTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some (FlagPhase.done false)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (List.replicate w.length true) (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ∀ b : Bool,
        ((decrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((decrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((decrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hv' : incFixed (w.map not) = none := by
    simpa only [counter_dec_complement, Option.map_eq_none_iff] using hv
  obtain ⟨he, hc, hh⟩ := incrementTM_run_overflow_ofCfg i (w.map not) hv'
    (d.mapWorkSymbols Equiv.boolNot) hstate (by
      intro p hl hr
      change (d.workTapes i (d.workTapePos i + p)).map Equiv.boolNot = _
      rw [hw p hl (by simpa using hr), counter_buffer_complement]
      rfl)
  simp only [List.length_map] at he hc hh
  refine ⟨?_, ?_, ?_⟩
  · rw [counter_decrement_run, he]
    apply Cfg.ext <;> try rfl
    funext j p
    have hb := counter_buffer_complement (List.replicate w.length false)
      (p - d.workTapePos j)
    simp only [Cfg.mapWorkSymbols]
    split_ifs
    · simpa using hb.symm
    · simp [Option.map_map, Function.comp_def]
  · intro t ht b
    exact (hc t ht b) ∘ (by simp only [counter_decrement_run, Cfg.mapWorkSymbols]; exact id)
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh

/-! ## Counter arithmetic -/

/-- The counter word after `r` decrements. A decrement at value zero leaves
the word unchanged here; the machine's underflow wrap is stated in the host
contract. -/
def counterWord (w : List Bool) (r : ℕ) : List Bool :=
  (fun u => (decFixed u).getD u)^[r] w

/-- The cost sum of the first `r` decrements along the frozen word orbit
`Turing.counterWord`: the decrement of the word `u` costs
`2 * (u.takeWhile not).length + 2`, which is also the underflow cost
`2|u| + 2` when `u` is all `false`. Because `counterWord` freezes at value
zero while the machine wraps on underflow, the sum equals the physical
countdown's cost only through its first underflow, that is for
`r ≤ value + 1`. That range covers every use in this file (§12.7 statement
gate, SC-1). -/
def counterOverhead (w : List Bool) (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, (2 * ((counterWord w j).takeWhile not).length + 2)

/-- A borrow either detects an all-false word or preserves width, subtracts one,
and changes the true-bit potential by its false-prefix length.
**Proof sketch.** Induct on the word. A true low bit stops the borrow; a false
low bit propagates it and gains one true bit. -/
private lemma counter_dec_spec (w : List Bool) :
    match decFixed w with
    | none => w = List.replicate w.length false
    | some v => v.length = w.length ∧
        Nat.ofDigits 2 (w.map Bool.toNat) = Nat.ofDigits 2 (v.map Bool.toNat) + 1 ∧
        v.count true + 1 = w.count true + (w.takeWhile not).length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | true => simp [decFixed, Nat.ofDigits_cons, Nat.add_comm]
    | false =>
      cases hd : decFixed w with
      | none =>
        simp only [hd] at ih
        simpa [decFixed, hd, List.replicate_succ] using congrArg (false :: ·) ih
      | some v =>
        simp only [hd] at ih
        rcases ih with ⟨hl, hv, hc⟩
        simp [decFixed, hd, Nat.ofDigits_cons, hl]
        omega

/-- The next frozen counter word is obtained by one optional decrement. -/
private lemma counter_word_succ (w : List Bool) (r : ℕ) :
    counterWord w (r + 1) = (decFixed (counterWord w r)).getD (counterWord w r) :=
  Function.iterate_succ_apply' _ _ _

/-- Underflow occurs exactly at binary value zero, including padded words. -/
private lemma counter_dec_zero (w : List Bool) :
    decFixed w = none ↔ Nat.ofDigits 2 (w.map Bool.toNat) = 0 := by
  have hs := counter_dec_spec w
  cases hd : decFixed w with
  | none =>
    simp only [hd] at hs
    simp only [true_iff]
    conv_lhs => rw [hs]
    simp
  | some v =>
    simp only [hd] at hs
    simp only [reduceCtorEq, false_iff]
    omega

/-- Decrements preserve the counter's width.

**Proof sketch.** `decFixed` preserves length, by induction on the word, and
`Option.getD` keeps the word otherwise; induct on `r`. -/
theorem counterWord_length (w : List Bool) (r : ℕ) :
    (counterWord w r).length = w.length := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [counter_word_succ]
    have hs := counter_dec_spec (counterWord w r)
    cases hd : decFixed (counterWord w r) with
    | none => simpa [hd] using ih
    | some v =>
      rw [hd] at hs
      simpa [hd] using hs.1.trans ih

/-- Each of the first `value w` decrements lowers the little-endian value by
one.

**Proof sketch.** For a word of positive value, `decFixed` succeeds and its
result has value one less, by induction on the word: a leading `true`
loses weight one, and a leading `false` borrows from the rest with weight
two. Induct on `r`. -/
theorem counterWord_value (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    Nat.ofDigits 2 ((counterWord w r).map Bool.toNat) =
      Nat.ofDigits 2 (w.map Bool.toNat) - r := by
  induction r with
  | zero => simp [counterWord]
  | succ r ih =>
    have hi := ih (by omega)
    have hs := counter_dec_spec (counterWord w r)
    rw [counter_word_succ]
    cases hb : decFixed (counterWord w r) with
    | none =>
      have hz := (counter_dec_zero _).mp hb
      omega
    | some v =>
      simp only [hb] at hs
      simp only [Option.getD_some]
      omega

/-- Before exhaustion, the physical predecessor is the next frozen word. -/
private lemma counter_word_decrement (w : List Bool) (r : ℕ)
    (hr : r < Nat.ofDigits 2 (w.map Bool.toNat)) :
    decFixed (counterWord w r) = some (counterWord w (r + 1)) := by
  have hv := counterWord_value w r (by omega)
  rw [counter_word_succ]
  cases hd : decFixed (counterWord w r) with
  | none => have hz := (counter_dec_zero _).mp hd; omega
  | some v => rfl

/-- Successful borrow costs telescope against twice the number of true bits.
**Proof sketch.** At each step the borrow specification equates the new
potential plus four with the old potential plus the exact decrement cost.
Add this equality to the induction hypothesis. -/
private lemma counter_potential (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r + 2 * w.count true =
      4 * r + 2 * (counterWord w r).count true := by
  induction r with
  | zero => simp [counterOverhead, counterWord]
  | succ r ih =>
    have hi := ih (by omega)
    have hs := counter_dec_spec (counterWord w r)
    rw [counter_word_decrement w r (by omega)] at hs
    simp only [counterOverhead, Finset.sum_range_succ]
    change (counterOverhead w r + (2 * (List.takeWhile not (counterWord w r)).length + 2)) +
      2 * w.count true = 4 * (r + 1) + 2 * (counterWord w (r + 1)).count true
    omega

/-- **Prefix amortization.** The first `r` decrements, for `r` at most the
counter's value, cost at most `4r + 2|w|`.

**Proof sketch.** The `j`th decrement acts on a word of value `n - j`
(`Turing.counterWord_value`), where `n` is the counter's value, and its
`false` prefix is the number of trailing zero bits of that value. Summed over
`r` consecutive values below `2^|w|`, the trailing zeros total
`ν₂(r!) + ν₂(binom) ≤ (r - 1) + (|w| - 1)` by Legendre and Kummer, so the
cost is at most `4r + 2|w| - 4` once `r ≥ 1`.

**Fill proof appendix.** The binding statement-gate route replaces the
number-theoretic sketch above by the exact telescoping identity proved in
`counter_potential`. Twice the count of true bits is the potential; its
terminal value is bounded by twice the preserved word length. -/
theorem counterOverhead_le_of_le (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r ≤ 4 * r + 2 * w.length := by
  have hp := counter_potential w r hr
  have hc : (counterWord w r).count true ≤ w.length :=
    (List.count_le_length).trans_eq (counterWord_length w r)
  omega

/-- At exhaustion the fixed-width word is all false, retaining any padding. -/
private lemma counter_word_exhausted (w : List Bool) :
    counterWord w (Nat.ofDigits 2 (w.map Bool.toNat)) =
      List.replicate w.length false := by
  have hz := counterWord_value w (Nat.ofDigits 2 (w.map Bool.toNat)) le_rfl
  simp only [Nat.sub_self] at hz
  have hs := counter_dec_spec (counterWord w (Nat.ofDigits 2 (w.map Bool.toNat)))
  rw [(counter_dec_zero _).mpr hz] at hs
  simpa only [counterWord_length] using hs

/-- **Whole-run amortization** (design §12.7, decision 12.7.6). Counting a
counter of value `n` down to zero and through the final underflow costs at
most `4n + 2|w| + 2`.

**Proof sketch.** The successful decrements act on the values `n, …, 1`,
whose trailing zeros sum to `n - s₂(n) ≤ n` (Legendre), so they cost at most
`4n`. The final word is all `false` (`Turing.counterWord_value`), so the
underflow sweep costs `2|w| + 2` (`Turing.counterWord_length`).

**Fill proof appendix.** Use `counter_potential` at exhaustion, where the
remaining true-bit count is zero, then add the full underflow sweep.
No Legendre or Kummer theorem is used. -/
theorem counterOverhead_le (w : List Bool) :
    counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) ≤
      4 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2 := by
  have hp := counter_potential w (Nat.ofDigits 2 (w.map Bool.toNat)) le_rfl
  rw [counter_word_exhausted] at hp
  simp [List.count_replicate] at hp
  have hs : counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) =
      counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat)) + (2 * w.length + 2) := by
    simp [counterOverhead, Finset.sum_range_succ, counter_word_exhausted]
  omega

/-! ## C2 — the counter-driven host -/

/-- Control of the counter-driven host (design §12.7, C2): a body state, a
decrement phase, or one of the two live exit anchors. -/
inductive CounterLoopState (S : Type) where
  /-- running the body -/
  | body (s : S)
  /-- running the decrement on the counter tape -/
  | dec (f : FlagPhase)
  /-- the live exit anchor after the counter underflows -/
  | done
  /-- the live exit anchor after the body reaches its designated exit -/
  | escape
deriving DecidableEq

instance counterLoopStateFintype (S : Type) [Fintype S] :
    Fintype (CounterLoopState S) := derive_fintype% _

/-- Where a body transition lands in the host. Arriving at the anchor `a`
starts the next decrement; arriving at the designated exit leaves through
`escape`; every other body state is kept. -/
def counterLoopRedirect {S : Type} [DecidableEq S] (a : S) (exit : Option S)
    (s : S) : CounterLoopState S :=
  if s = a then .dec .run else if exit = some s then .escape else .body s

/-- Where a decrement transition lands in the host. The success anchor
re-enters the body at `a`, the underflow anchor is the host's `done`, and the
working phases are kept. -/
def counterLoopDecExit {S : Type} (a : S) : FlagPhase → CounterLoopState S
  | .done true => .body a
  | .done false => .done
  | f => .dec f

/-- **C2, the counter-driven loop host** (design §12.7). The body `M` runs on
the first `k` tapes, embedded by `Turing.embedEmitTM` along `Fin.castSucc`
with its emissions forwarded, and the counter is the last tape. The host
starts with a decrement. Each successful decrement re-enters the body at the
anchor `a`, and each arrival at `a` starts the next decrement, with no
dispatch steps in between. Underflow leaves through the live anchor `done`;
reaching the optional exit leaves through the live anchor `escape`. Both
anchors are stationary. -/
def counterLoopTM {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
    (a : S) (exit : Option S) : MultiTapeTM (k + 1) Bool (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((decrementTM (k + 1) (Fin.last k)).tr f inp work).mapState (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

/-- A host configuration with host state `q`: the body configuration `c` on
the first `k` tapes (its own state field is ignored), the counter tape `ct`
with its head at `cp` as the last tape, and the body's output as the host's
output. It is the R1 transport `Turing.embedEmitCfg` along `Fin.castSucc`,
with the counter as the ambient frame. -/
def counterLoopCfg {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) : Cfg (k + 1) Bool (CounterLoopState S) x :=
  { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
      CounterLoopState.body with state := q }

/-- The body configurations at the starts of successive rounds: round `r`
starts from `counterLoopOrbit M τ c r`, and a round from `c` lasts `τ c`
steps. -/
def counterLoopOrbit {k : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM k Bool S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) : Cfg k Bool S x :=
  (fun c => M.runFrom c (τ c))^[r] c

/-! ### Shared phase and prefix invariants -/

/-- The last tape is outside the forwarding embedding's selected bank. -/
private lemma counter_last_unselected (k : ℕ) :
    Fin.last k ∉ Set.range (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) := by
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

/-- The host layout is the body bank followed by its counter tape. -/
private lemma counter_cfg_eq {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ := by
  have hf := (embedEmitTM_frame Fin.castSuccEmb
    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Bool Unit)
    (fun _ => ct) (fun _ => cp) [] (c.mapState (fun _ => ())) 0).1
    (Fin.last k) (counter_last_unselected k)
  apply Cfg.ext <;> try rfl
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfg, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.1
    · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_tape Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfg, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.2
    · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_pos Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i

/-- Injective successor redirection for the decrement's five controls. -/
private lemma counter_dec_injective {S : Type} (a : S) :
    Function.Injective (counterLoopDecExit a) := by
  intro f g h
  cases f <;> cases g <;> (try casesm* Bool) <;> simp_all [counterLoopDecExit]

/-- Anchor priority still gives an injective body-state redirection. -/
private lemma counter_redirect_injective {S : Type} [DecidableEq S]
    (a : S) (exit : Option S) : Function.Injective (counterLoopRedirect a exit) := by
  intro s t h
  by_cases hs : s = a
  · subst s
    by_cases ht : t = a
    · exact ht.symm
    · simp only [counterLoopRedirect, ht, if_false] at h
      split_ifs at h
  · by_cases ht : t = a
    · subst t; simp only [counterLoopRedirect, hs, if_false] at h
      split_ifs at h
    · simp only [counterLoopRedirect, hs, ht, if_false] at h
      split_ifs at h <;> simp_all

/-- Common trajectory data for a finite host segment, with a chosen set of
permitted body-head vectors. -/
private def counterSpan {k : ℕ} {S : Type} {x : List Bool}
    (H : MultiTapeTM (k + 1) Bool (CounterLoopState S))
    (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
    (R : (Fin k → ℤ) → Prop) : Prop :=
  (∀ u < t, (H.runFrom z u).state ≠ some .done ∧
    (H.runFrom z u).state ≠ some .escape) ∧
  (∀ u ≤ t, (H.runFrom z u).workTapePos (Fin.last k) ∈
    Finset.Icc (cp - 1) (cp + (width : ℤ))) ∧
  (∀ u ≤ t, R (fun j => (H.runFrom z u).workTapePos j.castSucc))

/-- Adjacent segments concatenate their cuts and trajectory bounds.
**Proof sketch.** Split a queried time at the first segment's length and
use run addition on the suffix. The two head-vector relations imply the
requested relation separately. -/
private lemma counter_span_append {k : ℕ} {S : Type} {x : List Bool}
    (H : MultiTapeTM (k + 1) Bool (CounterLoopState S))
    (z : Cfg (k + 1) Bool (CounterLoopState S) x) (s t : ℕ) (cp : ℤ) (width : ℕ)
    (R₁ R₂ R : (Fin k → ℤ) → Prop)
    (h₁ : counterSpan H z s cp width R₁)
    (h₂ : counterSpan H (H.runFrom z s) t cp width R₂)
    (hr₁ : ∀ p, R₁ p → R p) (hr₂ : ∀ p, R₂ p → R p) :
    counterSpan H z (s + t) cp width R := by
  have suffix (u : ℕ) (hu : s ≤ u) :
      H.runFrom z u = H.runFrom (H.runFrom z s) (u - s) := by
    rw [← H.runFrom_add, Nat.add_sub_of_le hu]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    by_cases hs : u < s
    · exact h₁.1 u hs
    · rw [suffix u (by omega)]; exact h₂.1 (u - s) (by omega)
  · intro u hu
    by_cases hs : u ≤ s
    · exact h₁.2.1 u hs
    · rw [suffix u (by omega)]; exact h₂.2.1 (u - s) (by omega)
  · intro u hu
    by_cases hs : u ≤ s
    · exact hr₁ _ (h₁.2.2 u hs)
    · rw [suffix u (by omega)]; exact hr₂ _ (h₂.2.2 (u - s) (by omega))

/-- A width-preserving overwrite of just the counter word interval. -/
private def counterPatch (ct : ℤ → Option Bool) (cp : ℤ) (w : List Bool) : ℤ → Option Bool :=
  fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
    then FinTM.bufferTape w (q - cp) else ct q

/-- Patching the word that is already present changes no cell. -/
private lemma counter_patch_initial (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape w p) : counterPatch ct cp w = ct := by
  funext q
  apply ite_eq_right_iff.mpr
  intro h
  have hf := hw (q - cp) (by omega) (by omega)
  simpa using hf.symm

/-- Equal-width patches overwrite the same interval, preserving the original frame. -/
private lemma counter_patch_twice (ct : ℤ → Option Bool) (cp : ℤ) (u v : List Bool)
    (hv : v.length = u.length) :
    counterPatch (counterPatch ct cp u) cp v = counterPatch ct cp v := by
  funext q
  simp only [counterPatch, hv]
  split_ifs <;> rfl

/-- Replacing a framed word by an equal-width word keeps both blank delimiters. -/
private lemma counter_patch_frame (w v : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hv : v.length = w.length)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape w p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      counterPatch ct cp v (cp + p) = FinTM.bufferTape v p := by
  intro p hl hr
  by_cases h : 0 ≤ p ∧ p < (v.length : ℤ)
  · simp [counterPatch, show cp ≤ cp + p ∧ cp + p < cp + (v.length : ℤ) by omega]
  · have hp : p = -1 ∨ p = (v.length : ℤ) := by omega
    rcases hp with rfl | rfl
    · simp [counterPatch, hw (-1) (by omega) (by omega), FinTM.bufferTape_left]
    · simp [counterPatch, hv, hw w.length (by omega) le_rfl, FinTM.bufferTape_nat]

/-- A decrement phase uses the proved framed contract and guarded state transport.
**Proof sketch.** Select success or underflow from the word function. The
host agrees with the decrement on every pre-verdict control, so the single
injective transport carries its endpoint, first-verdict cut, and head bounds. -/
private lemma counter_debit {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (c : Cfg k Bool S x) (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape w p) :
    let cost := 2 * (w.takeWhile not).length + 2
    let v := (decFixed w).getD (List.replicate w.length true)
    let q : CounterLoopState S := if (decFixed w).isSome then .body a else .done
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) cost =
      counterLoopCfg (some q) c (counterPatch ct cp v) cp ∧
    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      cost cp w.length (fun p => ∀ j, p j = c.workTapePos j) := by
  let z : Cfg (k + 1) Bool FlagPhase x :=
    (counterLoopCfg (some (.dec .run)) c ct cp).mapState (fun _ => FlagPhase.run)
  let v := (decFixed w).getD (List.replicate w.length true)
  let cost := 2 * (w.takeWhile not).length + 2
  have hz : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      z.workTapes (Fin.last k) (z.workTapePos (Fin.last k) + p) = FinTM.bufferTape w p := by
    simpa [z, Cfg.mapState, counter_cfg_eq] using hw
  have spec :
      (decrementTM (k + 1) (Fin.last k)).runFrom z cost =
        {z with state := some (.done (decFixed w).isSome), workTapes := fun j p =>
          if j = Fin.last k ∧ z.workTapePos j ≤ p ∧ p < z.workTapePos j + (w.length : ℤ)
          then FinTM.bufferTape v (p - z.workTapePos j) else z.workTapes j p} ∧
      (∀ t < cost, ∀ b, ((decrementTM (k + 1) (Fin.last k)).runFrom z t).state ≠
        some (.done b)) ∧
      (∀ j t, t ≤ cost → if j = Fin.last k then
        ((decrementTM (k + 1) (Fin.last k)).runFrom z t).workTapePos j ∈
          Finset.Icc (z.workTapePos j - 1) (z.workTapePos j + (w.length : ℤ))
        else ((decrementTM (k + 1) (Fin.last k)).runFrom z t).workTapePos j = z.workTapePos j) := by
    cases hd : decFixed w with
    | none =>
      have hs := counter_dec_spec w
      rw [hd] at hs
      have hp : (w.takeWhile not).length = w.length := by
        conv_lhs => rw [hs]
        simp
      simpa [cost, v, hd, hp] using decrementTM_run_underflow_ofCfg (Fin.last k) w hd z rfl hz
    | some u =>
      obtain ⟨he, hc, hh⟩ := decrementTM_run_succ_ofCfg (Fin.last k) w u hd z rfl hz
      refine ⟨by simpa [v, hd] using he, hc, ?_⟩
      intro j t ht
      have h := hh j t ht
      split_ifs at h ⊢ with hj
      · simp only [Finset.mem_Icc] at h ⊢
        have hlen := (List.takeWhile_sublist (p := not) (l := w)).length_le
        exact ⟨h.1, by omega⟩
      · exact h
  let emb : FlagPhase ↪ CounterLoopState S := ⟨counterLoopDecExit a, counter_dec_injective a⟩
  have run (t : ℕ) (ht : t ≤ cost) :
      (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t =
        ((decrementTM (k + 1) (Fin.last k)).runFrom z t).mapState emb := by
    refine MultiTapeTM.runFrom_mapState_of_agreeOn
      (decrementTM (k + 1) (Fin.last k)) (counterLoopTM M a exit) emb
      (fun f => ∀ b, f ≠ .done b) ?_ z t ?_
    · intro f hf inp work
      cases f with
      | run => rfl
      | rewind b => rfl
      | done b => exact False.elim (hf b rfl)
    · intro u hu f hf b he
      exact spec.2.1 u (by omega) b (hf.trans (congrArg some he))
  have vl : v.length = w.length := by
    have hs := counter_dec_spec w
    cases hd : decFixed w <;> simp [v, hd] at *
    exact hs.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run cost le_rfl, spec.1]
    apply Cfg.ext <;> try rfl
    · cases hd : decFixed w <;> simp [Cfg.mapState, emb, counterLoopDecExit, counterLoopCfg]
    · funext j p
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [z, Cfg.mapState, counter_cfg_eq, Fin.lastCases_last,
          true_and, counterPatch]
        change _ = if cp ≤ p ∧ p < cp + (v.length : ℤ) then FinTM.bufferTape v (p - cp) else ct p
        rw [vl]
      · simp [z, Cfg.mapState, counter_cfg_eq, Fin.castSucc_ne_last]
  · intro t ht
    rw [run t (by omega)]
    have hc := spec.2.1 t ht
    cases hs : ((decrementTM (k + 1) (Fin.last k)).runFrom z t).state with
    | none => simp [Cfg.mapState, hs]
    | some f =>
      cases f with
      | run => simp [Cfg.mapState, hs, emb, counterLoopDecExit]
      | rewind b => simp [Cfg.mapState, hs, emb, counterLoopDecExit]
      | done b => exact False.elim (hc b hs)
  · intro t ht
    rw [run t ht]
    simpa [Cfg.mapState, z, counter_cfg_eq] using spec.2.2 (Fin.last k) t ht
  · intro t ht j
    rw [run t ht]
    simpa [Cfg.mapState, z, counter_cfg_eq, Fin.castSucc_ne_last] using
      spec.2.2 j.castSucc t ht

/-- The body phase executes its entry action once, then uses guarded transport.
**Proof sketch.** The entry action reads the forwarding embedding. After that
step, all strict intermediate states avoid both redirections, and the RB5
transport lemma applies. R1 identifies every transported configuration and
therefore preserves the counter frame and all body-head trajectories. -/
private lemma counter_body {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (c : Cfg k Bool S x) (ct : ℤ → Option Bool) (cp : ℤ) (width t : ℕ)
    (hc : c.state = some a) (ht : 0 < t)
    (hmid : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧
      s ≠ a ∧ exit ≠ some s) :
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) t =
      counterLoopCfg ((M.runFrom c t).state.map (counterLoopRedirect a exit))
        (M.runFrom c t) ct cp ∧
    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.body a)) c ct cp)
      t cp width (fun p => ∃ u ≤ t, ∀ j, p j = (M.runFrom c u).workTapePos j) := by
  let E := embedEmitTM Fin.castSuccEmb M
  let ec := embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c
  let emb : S ↪ CounterLoopState S :=
    ⟨counterLoopRedirect a exit, counter_redirect_injective a exit⟩
  have first : (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) 1 =
      (E.runFrom ec 1).mapState emb := by
    change (counterLoopTM M a exit).step (counterLoopCfg (some (.body a)) c ct cp) =
      (E.step ec).mapState emb
    have hec : ec.state = some a := hc
    simp only [MultiTapeTM.step, hec, counterLoopCfg, Cfg.mapState]
    rfl
  have run (u : ℕ) (hu : 0 < u) (hut : u ≤ t) :
      (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) u =
        counterLoopCfg ((M.runFrom c u).state.map (counterLoopRedirect a exit))
          (M.runFrom c u) ct cp := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    rw [Nat.succ_eq_add_one, Nat.add_comm n 1, MultiTapeTM.runFrom_add, first]
    have tr := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTM M a exit) emb
      (fun s => s ≠ a ∧ exit ≠ some s)
      (by intro s hs inp work; simp [emb, counterLoopRedirect, hs.1, hs.2, counterLoopTM, E])
      (E.runFrom ec 1) n (by
        intro v hv s hs
        have he := embedEmitTM_runFrom Fin.castSuccEmb M (fun _ => ct) (fun _ => cp) [] c (1 + v)
        change E.runFrom ec (1 + v) = _ at he
        rw [MultiTapeTM.runFrom_add] at he
        have hstate := congrArg Cfg.state he
        change (E.runFrom (E.runFrom ec 1) v).state = (M.runFrom c (1 + v)).state at hstate
        obtain ⟨s', hs', ha, hx⟩ := hmid (1 + v) (by omega) (by omega)
        have eqs : s = s' := Option.some.inj (hs.symm.trans (hstate.trans hs'))
        simpa [eqs] using And.intro ha hx)
    rw [tr, ← MultiTapeTM.runFrom_add]
    change (E.runFrom ec (1 + n)).mapState emb = _
    rw [show E.runFrom ec (1 + n) =
      embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] (M.runFrom c (1 + n)) from
      embedEmitTM_runFrom Fin.castSuccEmb M _ _ [] c (1 + n)]
    rfl
  refine ⟨run t ht le_rfl, ?_, ?_, ?_⟩
  · intro u hu
    by_cases hz : u = 0
    · subst u; simp [counterLoopCfg]
    · rw [run u (by omega) (by omega)]
      obtain ⟨s, hs, ha, hx⟩ := hmid u (by omega) hu
      simp [counterLoopCfg, hs, counterLoopRedirect, ha, hx]
  · intro u hu
    by_cases hz : u = 0
    · subst u; simp [counter_cfg_eq, Finset.mem_Icc]
    · rw [run u (by omega) hu]
      simp [counter_cfg_eq, Finset.mem_Icc]
  · intro u hu
    refine ⟨u, hu, ?_⟩
    by_cases hz : u = 0
    · subst u; simp [counter_cfg_eq]
    · rw [run u (by omega) hu]
      simp [counter_cfg_eq]

/-- An orbit successor is the completed current body round. -/
private lemma counter_orbit_succ {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) :
    counterLoopOrbit M τ c (r + 1) =
      M.runFrom (counterLoopOrbit M τ c r) (τ (counterLoopOrbit M τ c r)) :=
  Function.iterate_succ_apply' _ _ _

/-- The shared round invariant, with the final body state left unrestricted.
Returning prefixes are exactly the configurations before the next decrement.
**Proof sketch.** Induct once on the number of rounds. The current word has
positive value, so the framed decrement succeeds. Append its transported
segment and the forwarding body segment. Equal-width overwrites keep the
original counter frame, and the two cost recurrences give the exact elapsed
time. Earlier starts at the anchor supply all returns needed by the induction. -/
private lemma counter_rounds {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (n : ℕ) (hn : n ≤ Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r < n, (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s)) :
    let elapsed := ∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r) + counterOverhead w n
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) elapsed =
      counterLoopCfg (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit))
        (counterLoopOrbit M τ c n) (counterPatch ct cp (counterWord w n)) cp ∧
    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      elapsed cp w.length (fun p => ∃ r u,
        ((r < n ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = n ∧ u = 0)) ∧
        ∀ j, p j = (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, counterOverhead, Finset.sum_empty,
      Nat.zero_add, MultiTapeTM.runFrom_zero, ite_true]
    have hpatch : counterPatch ct cp (counterWord w 0) = ct := counter_patch_initial w ct cp hw
    rw [hpatch]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro u hu; omega
    · intro u hu; have hz : u = 0 := by omega
      subst u; simp [counter_cfg_eq, Finset.mem_Icc]
    · intro u hu; have hz : u = 0 := by omega
      subst u
      exact ⟨0, 0, Or.inr ⟨rfl, rfl⟩, by simp [counter_cfg_eq, counterLoopOrbit]⟩
  | succ n ih =>
    obtain ⟨before, span⟩ := ih (by omega) (fun r hr => hround r (by omega))
    obtain ⟨ha, ht, hg⟩ := hround n (by omega)
    have control : (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit)) =
        some (CounterLoopState.dec FlagPhase.run) := by
      split_ifs <;> simp [ha, counterLoopRedirect]
    rw [control] at before
    let cn := counterLoopOrbit M τ c n
    let wn := counterWord w n
    let pn := counterPatch ct cp wn
    let nextTape := counterPatch ct cp (counterWord w (n + 1))
    let cost := 2 * (wn.takeWhile not).length + 2
    have hd := counter_word_decrement w n (by omega)
    have hf := counter_patch_frame w wn ct cp (counterWord_length w n) hw
    obtain ⟨debit, ds⟩ := counter_debit M a exit cn wn pn cp hf
    change decFixed wn = some (counterWord w (n + 1)) at hd
    simp only [hd, Option.getD_some, Option.isSome_some, ite_true] at debit
    rw [counter_patch_twice ct cp wn (counterWord w (n + 1))
      (by simp only [wn, counterWord_length])] at debit
    obtain ⟨body, bs⟩ := counter_body M a exit cn nextTape cp w.length (τ cn) ha ht hg
    have round : (counterLoopTM M a exit).runFrom
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) =
        counterLoopCfg ((counterLoopOrbit M τ c (n + 1)).state.map (counterLoopRedirect a exit))
          (counterLoopOrbit M τ c (n + 1)) nextTape cp := by
      rw [MultiTapeTM.runFrom_add, debit, body, counter_orbit_succ]
    have rs : counterSpan (counterLoopTM M a exit)
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) cp w.length
        (fun p => ∃ u ≤ τ cn, ∀ j, p j = (M.runFrom cn u).workTapePos j) := by
      apply counter_span_append _ _ cost (τ cn) cp w.length _ _ _
        (by simpa only [wn, counterWord_length] using ds) (by rw [debit]; exact bs)
      · intro p hp; exact ⟨0, Nat.zero_le _, by simpa using hp⟩
      · exact fun _ h => h
    have time : (∑ r ∈ Finset.range (n + 1), τ (counterLoopOrbit M τ c r)) +
        counterOverhead w (n + 1) =
        ((∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r)) + counterOverhead w n) +
          (cost + τ cn) := by
      simp [counterOverhead, Finset.sum_range_succ, cost, wn, cn,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    dsimp only
    rw [time]
    refine ⟨?_, ?_⟩
    · rw [MultiTapeTM.runFrom_add, before, round]
      rfl
    · apply counter_span_append _ _ _ (cost + τ cn) cp w.length _ _ _ span
        (by rw [before]; exact rs)
      · intro p hp
        obtain ⟨r, u, hr, heads⟩ := hp
        refine ⟨r, u, Or.inl ?_, heads⟩
        rcases hr with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
        · exact ⟨by omega, hu⟩
        · exact ⟨by omega, Nat.zero_le _⟩
      · intro p hp
        obtain ⟨u, hu, heads⟩ := hp
        exact ⟨n, u, Or.inl ⟨by omega, hu⟩, heads⟩

/-- **The counter-driven loop, every round returns** (design §12.7, C2).
Start the host at its decrement phase, with body configuration `c` and the
delimited counter word `w`, of value `d`, at `cp`. Suppose each of the `d`
rounds starts at the anchor `a`, lasts its exact time `τ > 0`, avoids the
anchor, the exit and halting in between, and returns to `a`. Then the host
reaches `done` at exactly `T`: the `d` round times plus the exact decrement
overhead, including the final underflow sweep. Its body part is the orbit
after `d` rounds, its counter is all `true`, and its counter head is back at
`cp`. Earlier, neither exit anchor occurs. Throughout, the counter head stays
within `[cp - 1, cp + |w|]`, and the body heads are the body's own heads at
some point of some round. With `exit = none`, the hypotheses do not mention an
exit at all.

**Proof sketch.** Induct on the round. Each decrement is
`Turing.decrementTM_run_succ_ofCfg` at the counter tape, with the body tapes
idle; the final one is `Turing.decrementTM_run_underflow_ofCfg`. The
redirection is applied at the exit step. Each round is the R1 run
`Turing.embedEmitTM_runFrom` with its states renamed by
`Turing.CounterLoopState.body`. The host agrees with that renamed run step by
step while the body's next state is neither the anchor nor the exit, which
the round hypothesis guarantees before the final step; the final step is the
redirection. The counter word before round
`r` is `Turing.counterWord w r` (`Turing.counterWord_value`), and the decrement
costs add to `Turing.counterOverhead w (d + 1)`. -/
theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨before, span⟩ := counter_rounds M a exit τ c w ct cp hw d (by omega)
    (fun r hr => ⟨(hround r hr).1, (hround r hr).2.1, (hround r hr).2.2.1⟩)
  have control : (if d = 0 then some (.dec .run) else
      (counterLoopOrbit M τ c d).state.map (counterLoopRedirect a exit)) =
      some (CounterLoopState.dec FlagPhase.run) := by
    by_cases hz : d = 0
    · simp [hz]
    · have ret := (hround (d - 1) (by omega)).2.2.2
      rw [show d - 1 + 1 = d by omega] at ret
      simp [hz, ret, counterLoopRedirect]
  rw [control] at before
  let wd := counterWord w d
  have width : wd.length = w.length := counterWord_length w d
  have empty : wd = List.replicate w.length false := by
    simpa only [hd] using counter_word_exhausted w
  have under : decFixed wd = none := (counter_dec_zero wd).mpr (by simp [empty])
  have framed := counter_patch_frame w wd ct cp width hw
  obtain ⟨debit, ds⟩ := counter_debit M a exit (counterLoopOrbit M τ c d) wd
    (counterPatch ct cp wd) cp framed
  simp only [under, Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false,
    width] at debit
  rw [counter_patch_twice ct cp wd (List.replicate w.length true)
    (by simp [width])] at debit
  have fill : counterPatch ct cp (List.replicate w.length true) =
      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) := by
    funext q
    simp only [counterPatch, List.length_replicate]
    split_ifs with h
    · have hp : 0 ≤ q - cp := by omega
      have hn : (q - cp).toNat < w.length := by omega
      simp [FinTM.bufferTape, h.1, hn]
    · rfl
  rw [fill] at debit
  have time : (∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r)) +
      counterOverhead w (d + 1) =
      ((∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r)) + counterOverhead w d) +
        (2 * (wd.takeWhile not).length + 2) := by
    simp [counterOverhead, Finset.sum_range_succ, wd, Nat.add_assoc]
  rw [time]
  refine ⟨?_, ?_⟩
  · rw [MultiTapeTM.runFrom_add, before, debit]
  · exact counter_span_append _ _ _ _ cp w.length _ _ _ span
      (by rw [before]; simpa only [width] using ds) (fun _ h => h)
      (fun p hp => ⟨d, 0, Or.inr ⟨rfl, rfl⟩, by simpa using hp⟩)

/-- **The counter-driven loop, early exit** (design §12.7, C2). As
`Turing.counterLoopTM_run_done`, except that round `r₀`, below the counter's
value, ends at the designated exit `e ≠ a` while every earlier round returns
to `a`. Then the host reaches `escape` at exactly the `r₀ + 1` round times plus
the cost of the `r₀ + 1` decrements before them. Its body part is the orbit
after round `r₀`, and its counter holds `Turing.counterWord w (r₀ + 1)`.
Earlier, neither exit anchor occurs, and the trajectory clauses hold as in
the returning case.

**Proof sketch.** The induction of `Turing.counterLoopTM_run_done`, stopped at
round `r₀`: every decrement before it succeeds, since `r₀` is below the value
(`Turing.counterWord_value`), and the redirection sends round `r₀`'s final
step to `escape`. -/
theorem counterLoopTM_run_escape {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a e : S) (hea : e ≠ a)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ e))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some e)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTM M a (some e)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape (counterWord w (r₀ + 1)) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a (some e)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨he, hs⟩ := counter_rounds M a (some e) τ c w ct cp hw (r₀ + 1)
    (by omega) (by
      intro r hr
      obtain ⟨ha, ht, hg⟩ := hround r (by omega)
      refine ⟨ha, ht, ?_⟩
      intro u hu hut
      obtain ⟨s, hst, hsa, hse⟩ := hg u hu hut
      exact ⟨s, hst, hsa, fun h => hse (Option.some.inj h).symm⟩)
  refine ⟨?_, hs.1, hs.2.1, ?_⟩
  · unfold counterPatch at he
    simp only [counterWord_length] at he
    simpa [hexit, hea, counterLoopRedirect] using he
  · simpa only [Nat.lt_succ_iff] using hs.2.2

/-- **Uniform per-round bound** (design §12.7, decision 12.7.3). If each of
the `d` rounds costs at most `B`, the returning run's exact time is at most
`d·B + 4d + 2|w| + 2`.

**Proof sketch.** Bound the round sum termwise by `B`
(`Finset.sum_le_card_nsmul`) and the decrement share by
`Turing.counterOverhead_le`. -/
theorem counterLoop_time_le {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2 := by
  have hsum := Finset.sum_le_card_nsmul (Finset.range d)
    (fun r => τ (counterLoopOrbit M τ c r)) B
    (fun r hr => hB r (Finset.mem_range.mp hr))
  simp only [Finset.card_range, nsmul_eq_mul] at hsum
  have hc := counterOverhead_le w
  rw [hd] at hc
  calc
    _ ≤ d * B + (4 * d + 2 * w.length + 2) :=
      Nat.add_le_add (by simpa using hsum) hc
    _ = _ := by omega

end Turing
