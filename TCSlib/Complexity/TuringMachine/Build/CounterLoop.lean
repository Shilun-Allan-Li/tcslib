/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Equiv.Bool
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.Scan
import TCSlib.Complexity.TuringMachine.SymbolLift
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.CodeParser

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

**Status update (§12.8 fill, R8.0b/R8.6).** All contracts in this file are proved.
The expansion proof cites `Turing.writeAdvTM_run_ofCfg` (`Build/Scan`, proved by the §12.8
stream-B fill), so nothing in this file is proved modulo an admission (R8.0b gate round 1,
note F14: doc-only refresh after the combined tree was checked).
**Alphabet update (R8.0b).** The shared loop machinery now admits any tape alphabet,
with binary digits embedded into its dedicated counter tape.

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
* **R8.0b, rich alphabets.** `Turing.counterLoopTMVia` transports the one-tape
  decrement through the symbol overlay and R1. Both generic contracts use the
  single round induction; the Bool contracts follow by identity-table agreement.
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
  decrements, and the exact cost of the first `r` decrements, valid as a
  physical cost for `r ≤ value + 1` (the counter word freezes at zero,
  while the machine wraps).
* `Turing.CounterLoopState`, `Turing.counterLoopTM`,
  `Turing.counterLoopCfg`, `Turing.counterLoopOrbit` — the host, its
  configurations, and the body's round-start configurations.
* `Turing.lastEmb`, `Turing.counterLoopTMVia` — the last-tape embedding and
  the rich-alphabet counter host.
* `Turing.expandTM` — the expansion (§12.8, R8.6): the counter loop whose
  round is the advancing writer `Turing.writeAdvTM`.

## Main results


* `Turing.MultiTapeTM.mapWorkSymbols_runFrom` — symbol transport.
* `Turing.decrementTM_run_succ_ofCfg`, `Turing.decrementTM_run_underflow_ofCfg`
  — the framed decrement contracts, in the §12.6 shape.
* `Turing.counterWord_length`, `Turing.counterWord_value`,
  `Turing.counterOverhead_le_of_le`, `Turing.counterOverhead_le` — counter
  arithmetic, including the amortized bound.
* `Turing.counterLoopTM_run_done`, `Turing.counterLoopTM_run_escape` — the
  host's exact whole-run contracts, with no earlier exit, the counter
  head's range, and the body heads' trajectory.
* `Turing.counterLoopTMVia_run_done`, `Turing.counterLoopTMVia_run_escape` —
  the rich-alphabet whole-run contracts, preserving the arbitrary rich frame.
* `Turing.counterLoop_time_le` — the uniform per-round bound.
* `Turing.expandTM_run_ofCfg` — the expansion writes its pattern once per
  counter unit, contiguously, at exact time (modulo the advancing writer, §12.8).
* MIG-0b, over the round layer of `Build/Contract/Basic`:
  `Turing.counterLoopTMVia_done_witness`, `Turing.counterLoopTMVia_escape_witness` (the host
  segments with the shared round-and-offset witness) and their `_segment` corollaries;
  `Turing.counterLoopCfg_body` (the host layout as an R1 reconstruction); and the
  contract-level compositions `Turing.RoundContract.counterLoopDone` and
  `Turing.RoundContract.counterLoopEscape`, with their `_traj` joint trajectories and their
  `_pre`, `_time`, `_post`, `_lo`, `_hi` field equations (the brief-inventory API's gate,
  finding 2).
* `Turing.foldr_bit_eq_ofDigits`, `Turing.counterValue_bits` — the counter value of a word is its
  binary value, and the counter word `t.bits` has value `t` (H1 harvest landing).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1–§3.2 and §4.1: the hierarchy
  arguments run a universal machine for a bounded number of steps under a
  step counter; this file is that counter as a reusable machine.)

**Fill appendix (§12.7).** All ten contracts are proved. Decrement is transported from increment once; `counter_rounds` is the single
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

/-- The empty word has no predecessor: `decFixed [] = none` (the specification API, the briefs'
pre-ship inventories, 2026-10-16). -/
theorem decFixed_nil : decFixed [] = none :=
  rfl

/-- A leading `true` becomes `false`: `decFixed (true :: w) = some (false :: w)` (the specification
API, the briefs' pre-ship inventories, 2026-10-16). -/
theorem decFixed_true_cons (w : List Bool) : decFixed (true :: w) = some (false :: w) :=
  rfl

/-- A leading `false` becomes `true` and borrows from the rest:
`decFixed (false :: w) = (decFixed w).map (true :: ·)` (the specification API, the briefs' pre-ship
inventories, 2026-10-16). -/
theorem decFixed_false_cons (w : List Bool) :
    decFixed (false :: w) = (decFixed w).map (true :: ·) :=
  rfl

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
  exact FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p

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

/-- **The decrement ignores its input** (B6-F1 promotion): its transition does not depend on
the input symbol it reads. This is the input-obliviousness that the symbol overlay transport
`Turing.MultiTapeTM.liftSymbols_runFrom_over` asks of a table.

**Proof sketch.** The increment's table ignores its input argument, and the conjugation by
complement passes that argument through unchanged; both sides are the same term (`rfl`). -/
theorem decrementTM_tr_input {k : ℕ} (i : Fin k) (q : FlagPhase) (inp inp' : Option Bool)
    (work : Fin k → Option Bool) :
    (decrementTM k i).tr q inp work = (decrementTM k i).tr q inp' work :=
  rfl

/-- **The decrement's actions keep the input head and write no blank** (B6-F1 promotion): every
action of the table has input move `0`, and every cell it writes receives a digit. The second
half is the blank-freeness that `Turing.MultiTapeTM.liftSymbols_runFrom_over` asks of a table;
the first keeps a host's input head fixed during a decrement.

**Proof sketch.** The conjugated table is the increment's action with its writes mapped by
complement; the increment never moves the input head and writes either nothing or a digit.
Split on the phase and the scanned cell. -/
theorem decrementTM_tr_action {k : ℕ} (i : Fin k) (q : FlagPhase) (inp : Option Bool)
    (work : Fin k → Option Bool) :
    ((decrementTM k i).tr q inp work).inputTape = 0 ∧
      ∀ j, (((decrementTM k i).tr q inp work).workTapes j).1 ≠ some none := by
  unfold decrementTM MultiTapeTM.mapWorkSymbols Action.mapWorkSymbols
  cases q <;> dsimp only [incrementTM] <;> (try split) <;>
    exact ⟨rfl, fun j => by by_cases hj : j = i <;> simp [hj]⟩

/-! ## Counter arithmetic -/

/-- The counter word after `r` decrements. A decrement at value zero leaves
the word unchanged here; the machine's underflow wrap is stated in the host
contract. -/
def counterWord (w : List Bool) (r : ℕ) : List Bool :=
  (fun u => (decFixed u).getD u)^[r] w

/-- **The counter word before any decrement** is the word itself (B6-F1 promotion).

**Proof sketch.** The zeroth iterate of the optional decrement is the identity (`rfl`). -/
theorem counterWord_zero (w : List Bool) : counterWord w 0 = w :=
  rfl

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

/-- **No decrement costs nothing** (B6-F1 promotion): the cost of the first `0` decrements
is `0`.

**Proof sketch.** An empty sum (`Finset.sum_range_zero`). -/
theorem counterOverhead_zero (w : List Bool) : counterOverhead w 0 = 0 :=
  Finset.sum_range_zero _

/-- **One more decrement adds its own cost** (B6-F1 promotion): the first `r + 1` decrements
cost the first `r` plus `2 · |takeWhile not (counterWord w r)| + 2`, the cost of decrementing the
`r`-th frozen word.

**Proof sketch.** Split the last summand off the sum (`Finset.sum_range_succ`). -/
theorem counterOverhead_succ (w : List Bool) (r : ℕ) :
    counterOverhead w (r + 1) =
      counterOverhead w r + (2 * ((counterWord w r).takeWhile not).length + 2) :=
  Finset.sum_range_succ _ _

/-- A borrow either detects an all-false word or preserves width, subtracts one,
and changes the true-bit potential by its false-prefix length.
**Proof sketch.** Induct on the word. A true low bit stops the borrow; a false
low bit propagates it and gains one true bit. -/
lemma counter_dec_spec (w : List Bool) :
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

/-- **The decrement keeps the width:** `decFixed w = some v → |v| = |w|`, the width clause of
`Turing.counter_dec_spec`'s successful branch.

**Proof sketch.** Specialize `Turing.counter_dec_spec` at `w`; its match reduces by `h`. -/
theorem decFixed_length {w v : List Bool} (h : decFixed w = some v) : v.length = w.length := by
  have hs := counter_dec_spec w
  simp only [h] at hs
  exact hs.1

/-- The next frozen counter word is obtained by one optional decrement. -/
private lemma counter_word_succ (w : List Bool) (r : ℕ) :
    counterWord w (r + 1) = (decFixed (counterWord w r)).getD (counterWord w r) :=
  Function.iterate_succ_apply' _ _ _

/-- Underflow occurs exactly at binary value zero, including padded words. -/
lemma counter_dec_zero (w : List Bool) :
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
lemma counter_word_decrement (w : List Bool) (r : ℕ)
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

/-- Select the last host tape as a one-tape bank (design §12.8a, R8.0b).
**Proof sketch.** The singleton domain makes the constant last-tape map injective. -/
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) :=
  ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩

/-- **The last-tape embedding sends its one index to the last tape** (B6-F1 promotion).

**Proof sketch.** Definitional (`rfl`). -/
theorem lastEmb_apply (k : ℕ) (i : Fin 1) : lastEmb k i = Fin.last k :=
  rfl

/-- Run a rich-alphabet body with an embedded binary counter on the last tape
(design §12.8a, R8.0b).
**Proof sketch.** R1 forwards the body and the symbol-lifted one-tape decrement;
the existing redirections connect the phases without dispatch steps. -/
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) :
    MultiTapeTM (k + 1) Γ (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
        (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

/-- A host configuration with host state `q`: the body configuration `c` on
the first `k` tapes (its own state field is ignored), the counter tape `ct`
with its head at `cp` as the last tape, and the body's output as the host's
output. It is the R1 transport `Turing.embedEmitCfg` along `Fin.castSucc`,
with the counter as the ambient frame. -/
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x :=
  { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
      CounterLoopState.body with state := q }

/-- The body configurations at the starts of successive rounds: round `r`
starts from `counterLoopOrbit M τ c r`, and a round from `c` lasts `τ c`
steps. Since MIG-0b it is an abbreviation of the core's round orbit `Turing.roundOrbit`
(`Build/Contract/Basic`), the iterate `(fun c => M.runFrom c (τ c))^[r] c`; a proof that
unfolds it unfolds `Turing.roundOrbit` too. -/
abbrev counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) :
    Cfg k Symbol S x :=
  roundOrbit M τ c r

/-! ### Shared phase and prefix invariants -/

/-- The host layout over any tape alphabet.
**Proof sketch.** R1 identifies the selected body bank and the last-tape frame. -/
private lemma counter_layout {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ := by
  have hf := (embedEmitTM_frame Fin.castSuccEmb
    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Symbol Unit)
    (fun _ => ct) (fun _ => cp) [] (c.mapState (fun _ => ())) 0).1
    (Fin.last k) (by rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi)
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

/-- **The counter-loop host layout** (design §12.7; public since the §12.8 fill): the
host configuration is the body bank followed by its counter tape.

**Proof sketch.** The body tapes are R1's selected tapes (`Turing.embedEmitCfg_selected_tape`,
`_pos`); the counter tape is its frame (`Turing.embedEmitTM_frame` at time `0`).

**Re-derivation appendix (R8.0b).** Instantiate the generic private layout at the Bool alphabet. -/
theorem counter_cfg_eq {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ :=
  counter_layout q c ct cp

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
private def counterSpan {k : ℕ} {Γ S : Type} {x : List Γ}
    (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
    (z : Cfg (k + 1) Γ (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
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
private lemma counter_span_append {k : ℕ} {Γ S : Type} {x : List Γ}
    (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
    (z : Cfg (k + 1) Γ (CounterLoopState S) x) (s t : ℕ) (cp : ℤ) (width : ℕ)
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
private def counterPatch {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (w : List Γ) : ℤ → Option Γ :=
  fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
    then FinTM.bufferTape w (q - cp) else ct q

/-- Equal-width patches overwrite the same interval, preserving the original frame. -/
private lemma counter_patch_twice {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ)
    (hv : v.length = u.length) :
    counterPatch (counterPatch ct cp u) cp v = counterPatch ct cp v := by
  funext q
  simp only [counterPatch, hv]
  split_ifs <;> rfl

/-- Replacing a framed word by an equal-width word keeps both blank delimiters. -/
private lemma counter_patch_frame {Γ : Type} (w v : List Γ) (ct : ℤ → Option Γ) (cp : ℤ)
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
**Proof sketch.** Decode the rich one-tape start, apply the landed success or
underflow contract, and read back through the public symbol overlay. Its input
obliviousness and absence of blank writes preserve arbitrary rich frame cells.
R1 puts this run on the last tape; injective guarded state transport supplies
the host's verdict cut and the two head trajectories. -/
private lemma counter_debit {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    let cost := 2 * (w.takeWhile not).length + 2
    let v := (decFixed w).getD (List.replicate w.length true)
    let q : CounterLoopState S := if (decFixed w).isSome then .body a else .done
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) cost =
      counterLoopCfg (some q) c (counterPatch ct cp (v.map e)) cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      cost cp w.length (fun p => ∀ j, p j = c.workTapePos j) := by
  let D : Cfg 1 Γ FlagPhase x :=
    ⟨some .run, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩
  let z := Cfg.decodeSymbols e D
  let v := (decFixed w).getD (List.replicate w.length true)
  let cost := 2 * (w.takeWhile not).length + 2
  let N := (decrementTM 1 0).liftSymbols e
  let E := embedEmitTM (lastEmb k) N
  let bank (d : Cfg 1 Γ FlagPhase x) := embedEmitCfg (lastEmb k)
    (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d
  have layout (d : Cfg 1 Γ FlagPhase x) : bank d =
      ⟨d.state, d.inputPos, Fin.lastCases (d.workTapes 0) c.workTapes,
        Fin.lastCases (d.workTapePos 0) c.workTapePos, d.output⟩ := by
    have frame (i : Fin k) := (embedEmitTM_frame (lastEmb k) N
      (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d 0).1
      i.castSucc (by rintro ⟨j, hj⟩; exact Fin.castSucc_ne_last i hj.symm)
    apply Cfg.ext <;> try rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [bank, Fin.lastCases_last] using
          embedEmitCfg_selected_tape (lastEmb k) (Fin.lastCases ct c.workTapes)
            (Fin.lastCases cp c.workTapePos) [] d 0
      · simpa only [MultiTapeTM.runFrom_zero, Fin.lastCases_castSucc] using (frame i).1
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [bank, Fin.lastCases_last] using
          embedEmitCfg_selected_pos (lastEmb k) (Fin.lastCases ct c.workTapes)
            (Fin.lastCases cp c.workTapePos) [] d 0
      · simpa only [MultiTapeTM.runFrom_zero, Fin.lastCases_castSucc] using (frame i).2
  have hz : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      z.workTapes 0 (z.workTapePos 0 + p) = FinTM.bufferTape w p := by
    intro p hl hr
    change (ct (cp + p)).bind (decodeBool e) = _
    rw [hw p hl hr, FinTM.bufferTape_map_decode]
  -- The only decrement facts are the landed framed contracts, on the decoded shadow.
  have spec :
      (decrementTM 1 0).runFrom z cost =
        {z with state := some (.done (decFixed w).isSome), workTapes := fun j p =>
          if j = 0 ∧ z.workTapePos j ≤ p ∧ p < z.workTapePos j + (w.length : ℤ)
          then FinTM.bufferTape v (p - z.workTapePos j) else z.workTapes j p} ∧
      (∀ t < cost, ∀ b, ((decrementTM 1 0).runFrom z t).state ≠ some (.done b)) ∧
      (∀ t ≤ cost, ((decrementTM 1 0).runFrom z t).workTapePos 0 ∈
        Finset.Icc (cp - 1) (cp + (w.length : ℤ))) := by
    cases hd : decFixed w with
    | none =>
      have hs := counter_dec_spec w
      rw [hd] at hs
      have hp : (w.takeWhile not).length = w.length := by
        conv_lhs => rw [hs]
        simp
      obtain ⟨he, hc, hh⟩ := decrementTM_run_underflow_ofCfg 0 w hd z rfl hz
      refine ⟨by simpa [cost, v, hd, hp] using he,
        by simpa [cost, hp] using hc, ?_⟩
      intro t ht
      simpa [z, D, Cfg.decodeSymbols] using hh 0 t (by simpa [cost, hp] using ht)
    | some u =>
      obtain ⟨he, hc, hh⟩ := decrementTM_run_succ_ofCfg 0 w u hd z rfl hz
      refine ⟨by simpa [v, hd] using he, hc, ?_⟩
      intro t ht
      have h := hh 0 t ht
      simp only [ite_true, Finset.mem_Icc] at h ⊢
      have hlen := (List.takeWhile_sublist (p := not) (l := w)).length_le
      exact ⟨h.1, by
        have upper : ((decrementTM 1 0).runFrom z t).workTapePos 0 ≤
            cp + ((w.takeWhile not).length : ℤ) := h.2
        omega⟩
  have rich (t : ℕ) : N.runFrom D t =
      Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom z t) := by
    conv_lhs => rw [← Cfg.liftOver_decodeSymbols e D]
    apply MultiTapeTM.liftSymbols_runFrom_over e _ (fun _ _ _ _ => rfl)
    intro f inp work j
    rcases f with _ | b | b <;>
    rcases h : work 0 with _ | b' <;> (try cases b') <;>
    simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
    split_ifs <;> simp
  let emb : FlagPhase ↪ CounterLoopState S := ⟨counterLoopDecExit a, counter_dec_injective a⟩
  have start : (bank D).mapState emb = counterLoopCfg (some (.dec .run)) c ct cp := by
    rw [layout, counter_layout]
    rfl
  have run (t : ℕ) (ht : t ≤ cost) :
      (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t =
        (bank (Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom z t))).mapState emb := by
    rw [← start]
    have h := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTMVia e M a exit) emb
      (fun f => ∀ b, f ≠ .done b) (by
        intro f hf inp work
        cases f with
        | run => rfl
        | rewind b => rfl
        | done b => exact False.elim (hf b rfl)) (bank D) t (by
          intro u hu f hf b he
          rw [show E.runFrom (bank D) u = bank (N.runFrom D u) from
            embedEmitTM_runFrom (lastEmb k) N _ _ [] D u, rich] at hf
          exact spec.2.1 u (by omega) b (hf.trans (congrArg some he)))
    rw [h, show E.runFrom (bank D) t = bank (N.runFrom D t) from
      embedEmitTM_runFrom (lastEmb k) N _ _ [] D t, rich]
  have vl : v.length = w.length := by
    have hs := counter_dec_spec w
    cases hd : decFixed w <;> simp [v, hd] at *
    exact hs.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run cost le_rfl, spec.1, layout, counter_layout]
    apply Cfg.ext
    · cases hd : decFixed w <;> simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols,
        emb, counterLoopDecExit]
    · apply Fin.ext; rfl
    · funext j p
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Cfg.mapState, Fin.lastCases_last]
        change (if (if (0 : Fin 1) = 0 ∧ cp ≤ p ∧ p < cp + (w.length : ℤ)
            then FinTM.bufferTape v (p - cp) else (ct p).bind (decodeBool e)) =
              (ct p).bind (decodeBool e) then ct p
            else (if (0 : Fin 1) = 0 ∧ cp ≤ p ∧ p < cp + (w.length : ℤ)
              then FinTM.bufferTape v (p - cp) else (ct p).bind (decodeBool e)).map e) =
          counterPatch ct cp (v.map e) p
        simp only [true_and, counterPatch, List.length_map, vl, FinTM.bufferTape_map]
        by_cases hp : cp ≤ p ∧ p < cp + (w.length : ℤ)
        · simp only [if_pos hp]
          split_ifs with he
          · have hn : (p - cp).toNat < v.length := by omega
            have hb : FinTM.bufferTape v (p - cp) = some v[(p - cp).toNat] := by
              simp [FinTM.bufferTape, hp.1, hn]
            cases hct : ct p with
            | none => simp [hct, hb] at he
            | some γ =>
              have decoded : decodeBool e γ = some v[(p - cp).toNat] := by
                simpa only [hct, hb, Option.bind_some] using he.symm
              simp only [hb, Option.map_some, decodeBool_eq_some e γ _ decoded]
          · rfl
        · simp only [if_neg hp, if_true]
      · simp only [Cfg.mapState, Fin.lastCases_castSucc]
    · rfl
    · simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, z, Cfg.decodeSymbols, D]
  · intro t ht
    rw [run t (by omega), layout]
    have hc := spec.2.1 t ht
    cases hs : ((decrementTM 1 0).runFrom z t).state with
    | none => simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs]
    | some f =>
      cases f with
      | run => simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs, emb, counterLoopDecExit]
      | rewind b =>
        simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs, emb, counterLoopDecExit]
      | done b => exact False.elim (hc b hs)
  · intro t ht
    rw [run t ht, layout]
    simpa only [Cfg.mapState, Fin.lastCases_last, Cfg.liftOver, Cfg.liftSymbols] using
      spec.2.2 t ht
  · intro t ht j
    rw [run t ht, layout]
    simp only [Cfg.mapState, Fin.lastCases_castSucc]

/-- The body phase executes its entry action once, then uses guarded transport.
**Proof sketch.** The entry action reads the forwarding embedding. After that
step, all strict intermediate states avoid both redirections, and the RB5
transport lemma applies. R1 identifies every transported configuration and
therefore preserves the counter frame and all body-head trajectories. -/
private lemma counter_body {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (c : Cfg k Γ S x) (ct : ℤ → Option Γ) (cp : ℤ) (width t : ℕ)
    (hc : c.state = some a) (ht : 0 < t)
    (hmid : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧
      s ≠ a ∧ exit ≠ some s) :
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) t =
      counterLoopCfg ((M.runFrom c t).state.map (counterLoopRedirect a exit))
        (M.runFrom c t) ct cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.body a)) c ct cp)
      t cp width (fun p => ∃ u ≤ t, ∀ j, p j = (M.runFrom c u).workTapePos j) := by
  let E := embedEmitTM Fin.castSuccEmb M
  let ec := embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c
  let emb : S ↪ CounterLoopState S :=
    ⟨counterLoopRedirect a exit, counter_redirect_injective a exit⟩
  have first : (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) 1 =
      (E.runFrom ec 1).mapState emb := by
    change (counterLoopTMVia e M a exit).step (counterLoopCfg (some (.body a)) c ct cp) =
      (E.step ec).mapState emb
    have hec : ec.state = some a := hc
    simp only [MultiTapeTM.step, hec, counterLoopCfg, Cfg.mapState]
    rfl
  have run (u : ℕ) (hu : 0 < u) (hut : u ≤ t) :
      (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) u =
        counterLoopCfg ((M.runFrom c u).state.map (counterLoopRedirect a exit))
          (M.runFrom c u) ct cp := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    rw [Nat.succ_eq_add_one, Nat.add_comm n 1, MultiTapeTM.runFrom_add, first]
    have tr := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTMVia e M a exit) emb
      (fun s => s ≠ a ∧ exit ≠ some s)
      (by intro s hs inp work; simp [emb, counterLoopRedirect, hs.1, hs.2, counterLoopTMVia, E])
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
    · subst u; simp [counter_layout, Finset.mem_Icc]
    · rw [run u (by omega) hu]
      simp [counter_layout, Finset.mem_Icc]
  · intro u hu
    refine ⟨u, hu, ?_⟩
    by_cases hz : u = 0
    · subst u; simp [counter_layout]
    · rw [run u (by omega) hu]
      simp [counter_layout]

/-- At the identity embedding the generic and Bool hosts have the same table.
**Proof sketch.** Compute R1 on its public last-tape embedding, cancel the
identity symbol lift, and compare the decrement tables field by field. -/
private lemma counter_refl_agree {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
    (a : S) (exit : Option S) :
    (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).AgreeOn
      (counterLoopTM M a exit) Set.univ := by
  have action_eq {k : ℕ} {Sy Q : Type} {A B : Action k Sy Q}
      (h1 : A.inputTape = B.inputTape) (h2 : A.workTapes = B.workTapes)
      (h3 : A.output = B.output) (h4 : A.state = B.state) : A = B := by
    cases A; cases B; simp_all
  have lift_refl (f : FlagPhase) (inp : Option Bool) (work : Fin 1 → Option Bool) :
      ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool)).tr f inp work =
        (decrementTM 1 0).tr f inp work := by
    have hd : ∀ o : Option Bool, o.bind (decodeBool (Function.Embedding.refl Bool)) = o := by
      intro o; cases o with
      | none => rfl
      | some b => cases b <;> rfl
    simp only [MultiTapeTM.liftSymbols, hd]
    cases ((decrementTM 1 0).tr f inp work) with
    | mk i w o s =>
      simp only [Action.liftSymbols]
      congr 1
      · funext j
        cases w j with
        | mk a m => cases a with
          | none => rfl
          | some b => cases b <;> rfl
      · cases o <;> rfl
  have embed_last {k : ℕ} {Sy Q : Type} (N : MultiTapeTM 1 Sy Q) (q : Q)
      (inp : Option Sy) (work : Fin (k + 1) → Option Sy) :
      (embedEmitTM (lastEmb k) N).tr q inp work =
        ⟨(N.tr q inp fun _ => work (Fin.last k)).inputTape,
          fun j => if j = Fin.last k then (N.tr q inp fun _ => work (Fin.last k)).workTapes 0
            else (none, 0),
          (N.tr q inp fun _ => work (Fin.last k)).output,
          (N.tr q inp fun _ => work (Fin.last k)).state⟩ := by
    apply action_eq
    · rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [if_true]
        conv_lhs => whnf
        split
        · rename_i i h
          rw [Subsingleton.elim i 0]
          rfl
        · rename_i h
          revert h
          show ((List.finRange 1).find? fun i => decide ((lastEmb k) i = Fin.last k)) = none → _
          simp [lastEmb]
      · simp only [Fin.castSucc_ne_last, if_false]
        conv_lhs => whnf
        split
        · rename_i i' h
          revert h
          show ((List.finRange 1).find? fun i' => decide ((lastEmb k) i' = Fin.castSucc i)) =
            some i' → _
          simp only [lastEmb, Function.Embedding.coeFn_mk, (Fin.castSucc_ne_last i).symm,
            decide_false]
          intro h
          rw [List.find?_eq_none.mpr (fun _ _ => by simp)] at h
          cases h
        · rfl
    · rfl
    · rfl
  have dec_refl (k : ℕ) (f : FlagPhase) (inp : Option Bool)
      (work : Fin (k + 1) → Option Bool) :
      (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool))).tr
          f inp work =
        (decrementTM (k + 1) (Fin.last k)).tr f inp work := by
    rw [embed_last, lift_refl]
    apply action_eq
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
    · funext j
      rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
        split_ifs <;> simp_all
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
  intro q _ inp work
  cases q with
  | body s => rfl
  | dec f => exact congrArg (Action.mapState (counterLoopDecExit a)) (dec_refl k f inp work)
  | done => rfl
  | escape => rfl

/-- The shared round invariant, with the final body state left unrestricted.
Returning prefixes are exactly the configurations before the next decrement.
**Proof sketch.** Induct once on the number of rounds. The current word has
positive value, so the framed decrement succeeds. Append its transported
segment and the forwarding body segment. Equal-width overwrites keep the
original counter frame, and the two cost recurrences give the exact elapsed
time. Earlier starts at the anchor supply all returns needed by the induction. -/
private lemma counter_rounds {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (n : ℕ) (hn : n ≤ Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r < n, (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s)) :
    let elapsed := ∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r) + counterOverhead w n
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) elapsed =
      counterLoopCfg (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit))
        (counterLoopOrbit M τ c n) (counterPatch ct cp ((counterWord w n).map e)) cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      elapsed cp w.length (fun p => ∃ r u,
        ((r < n ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = n ∧ u = 0)) ∧
        ∀ j, p j = (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, counterOverhead, Finset.sum_empty,
      Nat.zero_add, MultiTapeTM.runFrom_zero, ite_true]
    have hpatch : counterPatch ct cp ((counterWord w 0).map e) = ct := by
      change counterPatch ct cp (w.map e) = ct
      funext q
      apply ite_eq_right_iff.mpr
      intro h
      simp only [List.length_map] at h
      have hf := hw (q - cp) (by omega) (by omega)
      simpa using hf.symm
    rw [hpatch]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro u hu; omega
    · intro u hu; have hz : u = 0 := by omega
      subst u; simp [counter_layout, Finset.mem_Icc]
    · intro u hu; have hz : u = 0 := by omega
      subst u
      exact ⟨0, 0, Or.inr ⟨rfl, rfl⟩, by simp [counter_layout, counterLoopOrbit, roundOrbit]⟩
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
    let pn := counterPatch ct cp (wn.map e)
    let nextTape := counterPatch ct cp ((counterWord w (n + 1)).map e)
    let cost := 2 * (wn.takeWhile not).length + 2
    have hd := counter_word_decrement w n (by omega)
    have hf := counter_patch_frame (w.map e) (wn.map e) ct cp
      (by simp [List.length_map, wn, counterWord_length]) (by simpa using hw)
    obtain ⟨debit, ds⟩ := counter_debit e M a exit cn wn pn cp (by simpa using hf)
    change decFixed wn = some (counterWord w (n + 1)) at hd
    simp only [hd, Option.getD_some, Option.isSome_some, ite_true] at debit
    rw [counter_patch_twice ct cp (wn.map e) ((counterWord w (n + 1)).map e)
      (by simp only [List.length_map, wn, counterWord_length])] at debit
    obtain ⟨body, bs⟩ := counter_body e M a exit cn nextTape cp w.length (τ cn) ha ht hg
    have round : (counterLoopTMVia e M a exit).runFrom
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) =
        counterLoopCfg ((counterLoopOrbit M τ c (n + 1)).state.map (counterLoopRedirect a exit))
          (counterLoopOrbit M τ c (n + 1)) nextTape cp := by
      rw [MultiTapeTM.runFrom_add, debit, body]
      rw [show counterLoopOrbit M τ c (n + 1) = M.runFrom cn (τ cn) from
        Function.iterate_succ_apply' _ _ _]
    have rs : counterSpan (counterLoopTMVia e M a exit)
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) cp w.length
        (fun p => ∃ u ≤ τ cn, ∀ j, p j = (M.runFrom cn u).workTapePos j) := by
      apply counter_span_append _ _ cost (τ cn) cp w.length _ _ _
        (by simpa only [List.length_map, wn, counterWord_length] using ds) (by rw [debit]; exact bs)
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

/-- The rich-alphabet counter host returns after all rounds
(design §12.8a, R8.0b), with exact time, first-exit and both head trajectories.
**Proof sketch.** Instantiate the single generic round induction and append the
transported final underflow sweep. -/
theorem counterLoopTMVia_run_done {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
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
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨before, span⟩ := counter_rounds e M a exit τ c w ct cp hw d (by omega)
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
  have framed := counter_patch_frame (w.map e) (wd.map e) ct cp
    (by simpa using width) (by simpa using hw)
  obtain ⟨debit, ds⟩ := counter_debit e M a exit (counterLoopOrbit M τ c d) wd
    (counterPatch ct cp (wd.map e)) cp (by simpa using framed)
  simp only [under, Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false,
    width] at debit
  rw [counter_patch_twice ct cp (wd.map e) ((List.replicate w.length true).map e)
    (by simp [width])] at debit
  have fill : counterPatch ct cp ((List.replicate w.length true).map e) =
      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) := by
    funext q
    simp only [counterPatch, List.length_replicate, List.map_replicate]
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

/-- The rich-alphabet counter host takes an early body exit
(design §12.8a, R8.0b), with exact time, first-exit and both head trajectories.
**Proof sketch.** Instantiate the single generic round induction; its unrestricted
last body state redirects to the designated escape. -/
theorem counterLoopTMVia_run_escape {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some ex)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTMVia e M a (some ex)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a (some ex)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨he, hs⟩ := counter_rounds e M a (some ex) τ c w ct cp hw (r₀ + 1)
    (by omega) (by
      intro r hr
      obtain ⟨ha, ht, hg⟩ := hround r (by omega)
      refine ⟨ha, ht, ?_⟩
      intro u hu hut
      obtain ⟨s, hst, hsa, hse⟩ := hg u hu hut
      exact ⟨s, hst, hsa, fun h => hse (Option.some.inj h).symm⟩)
  refine ⟨?_, hs.1, hs.2.1, ?_⟩
  · unfold counterPatch at he
    simp only [List.length_map, counterWord_length] at he
    simpa [hexit, hea, counterLoopRedirect] using he
  · simpa only [Nat.lt_succ_iff] using hs.2.2

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
costs add to `Turing.counterOverhead w (d + 1)`.

**Re-derivation appendix (R8.0b).** Apply the generic returning contract at the identity embedding and transport
its run by `MultiTapeTM.runFrom_eq_of_agreeOn`; no new induction is used. -/
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
  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
      (counterLoopTM M a exit).runFrom z t =
        (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).runFrom z t :=
    MultiTapeTM.runFrom_eq_of_agreeOn (counter_refl_agree M a exit) z t
      (fun _ _ _ _ => Set.mem_univ _)
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    simpa [Function.Embedding.coe_refl] using hw
  simp only [z5]
  exact counterLoopTMVia_run_done (Function.Embedding.refl Bool) M a exit τ c w ct cp hw'
    d hd hround T hT

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
step to `escape`.

**Re-derivation appendix (R8.0b).** Apply the generic escape contract at the identity embedding and transport
its run by `MultiTapeTM.runFrom_eq_of_agreeOn`; no new induction is used. -/
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
  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
      (counterLoopTM M a (some e)).runFrom z t =
        (counterLoopTMVia (Function.Embedding.refl Bool) M a (some e)).runFrom z t :=
    MultiTapeTM.runFrom_eq_of_agreeOn (counter_refl_agree M a (some e)) z t
      (fun _ _ _ _ => Set.mem_univ _)
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    simpa [Function.Embedding.coe_refl] using hw
  have h := counterLoopTMVia_run_escape (Function.Embedding.refl Bool) M a e hea τ c w ct cp
    hw' r₀ hr₀ hround hexit T hT
  simp only [Function.Embedding.coe_refl, List.map_id] at h
  simp only [z5]
  exact h

/-- **Uniform per-round bound** (design §12.7, decision 12.7.3). If each of
the `d` rounds costs at most `B`, the returning run's exact time is at most
`d·B + 4d + 2|w| + 2`.

**Proof sketch.** Bound the round sum termwise by `B`
(`Finset.sum_le_card_nsmul`) and the decrement share by
`Turing.counterOverhead_le`. -/
theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
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

/-! ## R8.6 — the expansion (§12.8) -/

/-- **R8.6, the expansion** (design §12.8a). The counter loop whose round is
the advancing writer: with a counter of value `d` on the last tape, it writes
the pattern `pat` on tape `i` `d` times, contiguously from the head, and leaves
the head after the last copy. Its uses are lengths given in binary: the
window halves of a record, of length `d·|pat|` for a radius counter `d`. -/
def expandTM (k : ℕ) (i : Fin k) (pat : List Bool) :
    MultiTapeTM (k + 1) Bool (CounterLoopState (Fin (pat.length + 1))) :=
  counterLoopTM (writeAdvTM k i pat) 0 none

/-- **R8.6, the expansion, framed** (design §12.8a). Start the expansion at its
decrement phase with body configuration `c` at the writer's state `0` and the
delimited counter word `w`, of value `d`, at `cp`. It reaches `done` at exactly
`d·(|pat| + 1) + counterOverhead w (d + 1)` and neither exit anchor earlier.
At that point the interval `[pos, pos + d·|pat|)` of tape `i` holds `d` copies
of `pat`, whatever it held before, the head of tape `i` is at `pos + d·|pat|`,
the counter is all `true` with its head back at `cp`, and every other cell,
every other head, the input position and the output are unchanged. Throughout,
the counter head stays within `[cp - 1, cp + |w|]`, the head of tape `i`
within `[pos, pos + d·|pat|]`, and every other body head is fixed.

**Proof sketch.** Apply `Turing.counterLoopTM_run_done` with the constant round
time `τ := |pat| + 1`. The round hypotheses are `Turing.writeAdvTM_run_ofCfg`
at the orbit's `r`-th configuration, which by induction on `r` has `r` copies
of `pat` written from `pos` and its head at `pos + r·|pat|`. The round sum is
`d·(|pat| + 1)`. The head clauses follow from the loop's trajectory clause and
the writer's. -/
theorem expandTM_run_ofCfg {k : ℕ} {x : List Bool} (i : Fin k) (pat : List Bool)
    (c : Cfg k Bool (Fin (pat.length + 1)) x) (hc : c.state = some 0)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) :
    (expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp)
        (d * (pat.length + 1) + counterOverhead w (d + 1)) =
      counterLoopCfg (some .done)
        { c with
          workTapes := fun j q =>
            if j = i ∧ c.workTapePos j ≤ q ∧
                q < c.workTapePos j + ((d * pat.length : ℕ) : ℤ)
              then FinTM.bufferTape (List.replicate d pat).flatten (q - c.workTapePos j)
            else c.workTapes j q
          workTapePos := Function.update c.workTapePos i
            (c.workTapePos i + ((d * pat.length : ℕ) : ℤ)) }
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1), ∀ j : Fin k,
        if j = i then
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc ∈
            Finset.Icc (c.workTapePos j) (c.workTapePos j + ((d * pat.length : ℕ) : ℤ))
        else
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            c.workTapePos j) := by
  let M := writeAdvTM k i pat
  let τ : Cfg k Bool (Fin (pat.length + 1)) x → ℕ := fun _ => pat.length + 1
  let finish (r : ℕ) : Cfg k Bool (Fin (pat.length + 1)) x :=
    { c with
      workTapes := fun j q =>
        if j = i ∧ c.workTapePos j ≤ q ∧
            q < c.workTapePos j + ((r * pat.length : ℕ) : ℤ)
          then FinTM.bufferTape (List.replicate r pat).flatten (q - c.workTapePos j)
        else c.workTapes j q
      workTapePos := Function.update c.workTapePos i
        (c.workTapePos i + ((r * pat.length : ℕ) : ℤ)) }
  -- This induction concerns only the advancing writer's orbit, not the loop host.
  have orbit (r : ℕ) : counterLoopOrbit M τ c r = finish r := by
    induction r with
    | zero =>
      change c = finish 0
      apply Cfg.ext <;> try rfl
      · funext j q
        simp [finish]
      · funext j
        by_cases hj : j = i <;> simp [finish, hj]
    | succ r ih =>
      have step := (writeAdvTM_run_ofCfg i pat (finish r) hc).1
      rw [show counterLoopOrbit M τ c (r + 1) =
        M.runFrom (counterLoopOrbit M τ c r) (τ (counterLoopOrbit M τ c r)) from
        Function.iterate_succ_apply' _ _ _, ih]
      change (writeAdvTM k i pat).runFrom (finish r) (pat.length + 1) = finish (r + 1)
      rw [step]
      have length : (List.replicate r pat).flatten.length = r * pat.length := by simp
      have append : (List.replicate (r + 1) pat).flatten =
          (List.replicate r pat).flatten ++ pat := by
        rw [List.replicate_succ', List.flatten_append]
        simp
      apply Cfg.ext
      · exact hc.symm
      · rfl
      · funext j q
        by_cases hj : j = i
        · subst j
          simp only [finish, Function.update_self, true_and, Nat.add_mul, Nat.one_mul,
            Nat.cast_add, append]
          by_cases hnew : c.workTapePos i + ((r * pat.length : ℕ) : ℤ) ≤ q ∧
              q < c.workTapePos i + ((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)
          · have hwhole : c.workTapePos i ≤ q ∧
                q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)) := by omega
            simp only [hnew, hwhole]
            have h0 : 0 ≤ q - c.workTapePos i := by omega
            have h1 : 0 ≤ q - (c.workTapePos i + ((r * pat.length : ℕ) : ℤ)) := by omega
            have hn : ¬ (q - c.workTapePos i).toNat < (List.replicate r pat).flatten.length := by
              rw [length]; omega
            simp only [FinTM.bufferTape, h0, h1, if_true, List.getElem?_append, hn, if_false]
            rw [show (q - (c.workTapePos i + ((r * pat.length : ℕ) : ℤ))).toNat =
              (q - c.workTapePos i).toNat - (List.replicate r pat).flatten.length by
                rw [length]; omega]
            simp only [and_self, if_true]
          · simp only [hnew, if_false]
            by_cases hold : c.workTapePos i ≤ q ∧
                q < c.workTapePos i + ((r * pat.length : ℕ) : ℤ)
            · have hwhole : c.workTapePos i ≤ q ∧
                  q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)) := by omega
              have h0 : 0 ≤ q - c.workTapePos i := by omega
              have hn : (q - c.workTapePos i).toNat < (List.replicate r pat).flatten.length := by
                rw [length]; omega
              simp only [hold, hwhole, FinTM.bufferTape, h0, List.getElem?_append, hn, if_true]
            · have hwhole : ¬ (c.workTapePos i ≤ q ∧
                  q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ))) := by omega
              simp only [hold, hwhole, if_false]
        · simp [finish, hj]
      · funext j
        by_cases hj : j = i
        · subst j
          simp [finish, Nat.add_mul, Nat.cast_add, add_assoc]
        · simp [finish, hj]
      · rfl
  have state (r : ℕ) : (counterLoopOrbit M τ c r).state = some 0 := by
    rw [orbit]; exact hc
  have rounds : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some 0 ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ 0 ∧ (none : Option (Fin (pat.length + 1))) ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some 0 := by
    intro r hr
    have spec := writeAdvTM_run_ofCfg i pat (counterLoopOrbit M τ c r) (state r)
    refine ⟨state r, Nat.succ_pos _, ?_, state (r + 1)⟩
    intro u hu hut
    change u < pat.length + 1 at hut
    have live := MultiTapeTM.runFrom_state_ne_none_of_le M (counterLoopOrbit M τ c r)
      (pat.length + 1) (by rw [spec.1]; simp) u (by omega)
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp live
    refine ⟨s, hs, ?_, Option.noConfusion⟩
    intro he
    exact spec.2.1 u hu hut (hs.trans (congrArg some he))
  obtain ⟨he, hcut, hcounter, hbody⟩ := counterLoopTM_run_done M 0 none τ c w ct cp hw d hd
    rounds (d * (pat.length + 1) + counterOverhead w (d + 1)) (by simp [τ])
  refine ⟨?_, hcut, hcounter, ?_⟩
  · rw [orbit] at he
    exact he
  · intro t ht j
    obtain ⟨r, u, hr, heads⟩ := hbody t ht
    have spec := (writeAdvTM_run_ofCfg i pat (counterLoopOrbit M τ c r) (state r)).2.2
    have hu : u ≤ pat.length + 1 := by
      rcases hr with h | ⟨rfl, rfl⟩
      · exact h.2
      · omega
    have hh := spec j u hu
    rw [heads j]
    by_cases hj : j = i
    · subst j
      simp only [ite_true, orbit, finish, Function.update_self, Finset.mem_Icc] at hh ⊢
      rcases hr with ⟨hr, _⟩ | ⟨rfl, rfl⟩
      · have hrd : (r + 1) * pat.length ≤ d * pat.length := Nat.mul_le_mul_right _ hr
        rw [Nat.add_mul, Nat.one_mul] at hrd
        exact ⟨by omega, by omega⟩
      · simpa only [MultiTapeTM.runFrom_zero, Function.update_self, le_refl, and_true,
          le_add_iff_nonneg_right] using (Int.natCast_nonneg (r * pat.length))
    · simpa [hj, orbit, finish] using hh

end Turing

/-! ## The counter loop over the round layer (MIG-0b; design §16a item 2)

The counter loop's **body** interface is the round layer of `Build/Contract/Basic`
(`Turing.counterLoopOrbit` is an abbreviation of `Turing.roundOrbit`); its **host** runs are
segments with a joint relation. Below: the host segments derived from the public
`counterLoopTMVia_run_done` and `_run_escape` with round-layer hypotheses on the body rounds,
keeping the public theorems' shared round-and-offset witness for all body heads, their exact
endpoints, the counter interval and liveness (`_witness`), and their corollaries with a body
relation (`_segment`); the host layout as an R1 reconstruction; and the contract-level
compositions `Turing.RoundContract.counterLoopDone` and `counterLoopEscape`, with their
shared-witness joint trajectories. -/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **The counter loop's segment with the shared witness, returning rounds** (fit test of the
segment, round and joint-trajectory layers against `Turing.counterLoopTMVia_run_done`; MIG-0a
gate, round 2). If the first `d` rounds of the body orbit are returning rounds with escape set
`{exit}`, the host run is a segment ending at `done`, live and off both exits before its end. Its
joint relation is the public theorem's, unweakened: the counter head in its interval, and **one**
round `r` and offset `u` at which **every** body head is the body's own.

**Proof sketch.** The round cut, read in the rows' form (`Turing.Round.cut_some`), gives the
public theorem's round hypothesis; its conclusion is the segment, and the live endpoint adds
liveness (`Turing.Segment.live`). -/
theorem counterLoopTMVia_done_witness {S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) {P : (Fin k → ℤ) → Prop}
    (hround : ∀ r < d, Round M a {exit} P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r)) ∧ (roundOrbit M τ c (r + 1)).state = some a) :
    Segment (counterLoopTMVia e M a exit) {none, some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        ∃ r u, ((r < d ∧ u ≤ τ (roundOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
          ∀ j : Fin k, p j.castSucc = (M.runFrom (roundOrbit M τ c r) u).workTapePos j)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .done) (roundOrbit M τ c d)
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp)
      (∑ r ∈ Finset.range d, τ (roundOrbit M τ c r) + counterOverhead w (d + 1)) := by
  have hr : ∀ r < d,
      (roundOrbit M τ c r).state = some a ∧ 0 < τ (roundOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (roundOrbit M τ c r) →
        ∃ s, (M.runFrom (roundOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ exit ≠ some s) ∧
      (roundOrbit M τ c (r + 1)).state = some a := by
    intro r hr
    obtain ⟨hR, hret⟩ := hround r hr
    refine ⟨hR.1, hR.2.1, fun u hu hut => ?_, hret⟩
    obtain ⟨s, hs, hsa, hsE⟩ := hR.cut_some u hu hut
    exact ⟨s, hs, hsa, fun h' => hsE (h' ▸ rfl)⟩
  obtain ⟨hrun, hcut, hctr, hbody⟩ :=
    counterLoopTMVia_run_done e M a exit τ c w ct cp hw d hd hr _ rfl
  have h : Segment (counterLoopTMVia e M a exit) {some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        ∃ r u, ((r < d ∧ u ≤ τ (roundOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
          ∀ j : Fin k, p j.castSucc = (M.runFrom (roundOrbit M τ c r) u).workTapePos j)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .done) (roundOrbit M τ c d)
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp)
      (∑ r ∈ Finset.range d, τ (roundOrbit M τ c r) + counterOverhead w (d + 1)) := by
    refine ⟨hrun, fun t ht hm => ?_, fun t ht => ⟨hctr t ht, hbody t ht⟩⟩
    rcases hm with hm | hm
    · exact (hcut t ht).1 hm
    · exact (hcut t ht).2 hm
  exact h.live (Option.some_ne_none _)

/-- **The counter loop's segment, returning rounds, with the body relation**: the corollary of
`Turing.counterLoopTMVia_done_witness` in which the shared witness is used up: the body heads
satisfy the rounds' relation `P` at every time.

**Proof sketch.** At the witness, the body heads are those of round `r` at offset `u`, where `P`
holds by round `r`'s relation, or of the start of round `d`, which is the end of round `d - 1`
(or the start `c` when `d = 0`). -/
theorem counterLoopTMVia_done_segment {S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) {P : (Fin k → ℤ) → Prop}
    (h0 : P c.workTapePos)
    (hround : ∀ r < d, Round M a {exit} P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r)) ∧ (roundOrbit M τ c (r + 1)).state = some a) :
    Segment (counterLoopTMVia e M a exit) {some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        P fun j => p j.castSucc)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .done) (roundOrbit M τ c d)
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp)
      (∑ r ∈ Finset.range d, τ (roundOrbit M τ c r) + counterOverhead w (d + 1)) := by
  refine (counterLoopTMVia_done_witness e M a exit τ c w ct cp hw d hd hround).mono
    (Set.subset_insert _ _) fun p ⟨hc, r, u, hru, hj⟩ => ⟨hc, ?_⟩
  have hP : P (M.runFrom (roundOrbit M τ c r) u).workTapePos := by
    rcases hru with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
    · exact (hround r hr).1.2.2.2.2.2 u hu
    · rcases Nat.eq_zero_or_pos r with rfl | hpos
      · exact h0
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hR := (hround r' (by omega)).1
        have hend := hR.2.2.2.2.2 _ le_rfl
        rw [hR.2.2.1] at hend
        exact hend
  have he : (fun j : Fin k => p j.castSucc) = (M.runFrom (roundOrbit M τ c r) u).workTapePos :=
    funext hj
  rw [he]
  exact hP

/-- **The counter loop's segment with the shared witness, escaping round** (fit test against
`Turing.counterLoopTMVia_run_escape`): rounds `0` to `r₀` of the body orbit are rounds with escape
`{some ex}`, round `r₀` escaping, with `r₀` below the counter's value. Then the host run is a
segment ending at `escape`, live and off both exits before its end, with the public theorem's
joint relation: the counter interval and one shared round and offset for all body heads.

**Proof sketch.** The round cut gives the public escape theorem's hypothesis; its conclusion is
the segment, and the live endpoint adds liveness. -/
theorem counterLoopTMVia_escape_witness {S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat)) {P : (Fin k → ℤ) → Prop}
    (hround : ∀ r ≤ r₀, Round M a {some ex} P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r)))
    (hexit : (roundOrbit M τ c (r₀ + 1)).state = some ex) :
    Segment (counterLoopTMVia e M a (some ex)) {none, some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        ∃ r u, ((r ≤ r₀ ∧ u ≤ τ (roundOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
          ∀ j : Fin k, p j.castSucc = (M.runFrom (roundOrbit M τ c r) u).workTapePos j)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .escape) (roundOrbit M τ c (r₀ + 1))
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
          then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp)
      (∑ r ∈ Finset.range (r₀ + 1), τ (roundOrbit M τ c r) + counterOverhead w (r₀ + 1)) := by
  have hr : ∀ r ≤ r₀,
      (roundOrbit M τ c r).state = some a ∧ 0 < τ (roundOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (roundOrbit M τ c r) →
        ∃ s, (M.runFrom (roundOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex) := by
    intro r hr
    obtain ⟨hc, ht, -, -, -, -⟩ := hround r hr
    refine ⟨hc, ht, fun u hu hut => ?_⟩
    obtain ⟨s, hs, hsa, hsE⟩ := (hround r hr).cut_some u hu hut
    exact ⟨s, hs, hsa, fun h => hsE (by rw [h]; rfl)⟩
  obtain ⟨hrun, hcut, hctr, hbody⟩ := counterLoopTMVia_run_escape e M a ex hea τ c w ct cp hw r₀
    hr₀ hr hexit _ rfl
  have h : Segment (counterLoopTMVia e M a (some ex)) {some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        ∃ r u, ((r ≤ r₀ ∧ u ≤ τ (roundOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
          ∀ j : Fin k, p j.castSucc = (M.runFrom (roundOrbit M τ c r) u).workTapePos j)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .escape) (roundOrbit M τ c (r₀ + 1))
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
          then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp)
      (∑ r ∈ Finset.range (r₀ + 1), τ (roundOrbit M τ c r) + counterOverhead w (r₀ + 1)) := by
    refine ⟨hrun, fun t ht hm => ?_, fun t ht => ⟨hctr t ht, hbody t ht⟩⟩
    rcases hm with hm | hm
    · exact (hcut t ht).1 hm
    · exact (hcut t ht).2 hm
  exact h.live (Option.some_ne_none _)

/-- **The counter loop's segment, escaping round, with the body relation**: the corollary of
`Turing.counterLoopTMVia_escape_witness` with the shared witness used up.

**Proof sketch.** At the witness, the body heads lie in a round, where `P` holds, or at the end
of round `r₀`. -/
theorem counterLoopTMVia_escape_segment {S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat)) {P : (Fin k → ℤ) → Prop}
    (hround : ∀ r ≤ r₀, Round M a {some ex} P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r)))
    (hexit : (roundOrbit M τ c (r₀ + 1)).state = some ex) :
    Segment (counterLoopTMVia e M a (some ex)) {some .done, some .escape}
      (fun p => p (Fin.last k) ∈ Finset.Icc (cp - 1) (cp + (w.length : ℤ)) ∧
        P fun j => p j.castSucc)
      (counterLoopCfg (some (.dec .run)) c ct cp)
      (counterLoopCfg (some .escape) (roundOrbit M τ c (r₀ + 1))
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
          then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp)
      (∑ r ∈ Finset.range (r₀ + 1), τ (roundOrbit M τ c r) + counterOverhead w (r₀ + 1)) := by
  refine (counterLoopTMVia_escape_witness e M a ex hea τ c w ct cp hw r₀ hr₀ hround hexit).mono
    (Set.subset_insert _ _) fun p ⟨hc, r, u, hru, hj⟩ => ⟨hc, ?_⟩
  have hP : P (M.runFrom (roundOrbit M τ c r) u).workTapePos := by
    rcases hru with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
    · exact (hround r hr).2.2.2.2.2 u hu
    · have hR := hround r₀ le_rfl
      have hend := hR.2.2.2.2.2 _ le_rfl
      rw [hR.2.2.1] at hend
      exact hend
  have he : (fun j : Fin k => p j.castSucc) = (M.runFrom (roundOrbit M τ c r) u).workTapePos :=
    funext hj
  rw [he]
  exact hP

/-- The body configuration of a counter-loop host configuration: the first `k` tapes and heads,
the input position and the output, at the body anchor `a`. -/
def counterLoopBody {S : Type} {x : List Γ} (a : S) (d : Cfg (k + 1) Γ (CounterLoopState S) x) :
    Cfg k Γ S x :=
  ⟨some a, d.inputPos, fun j => d.workTapes j.castSucc, fun j => d.workTapePos j.castSucc,
    d.output⟩

/-! The body configuration's fields, as equations (the specification API, the briefs' pre-ship
inventories, 2026-10-16): generated by `simps` without the `simp` attribute. -/
attribute [simps (config := { isSimp := false })] counterLoopBody

/-- **The counter-loop host layout is an R1 reconstruction** (a seventh member of the family:
`CounterLoop`'s private `counter_layout`, `Build/CounterLoop.lean:650`): every host configuration
is the counter-loop configuration of its body, its counter tape and its counter head.

**Proof sketch.** `Turing.counterLoopCfg` is the forwarding embedding along `Fin.castSucc`,
relabelled and with its state replaced. `Turing.embedEmitCfg_eq` identifies the embedding with
`d`'s tapes and heads: the selected ones are the body's, and the only unselected tape is the
last, which is the counter. -/
theorem counterLoopCfg_body {S : Type} {x : List Γ} (a : S)
    (d : Cfg (k + 1) Γ (CounterLoopState S) x) :
    counterLoopCfg d.state (counterLoopBody a d) (d.workTapes (Fin.last k))
      (d.workTapePos (Fin.last k)) = d := by
  have hlast : ∀ j : Fin (k + 1), j ∉ Set.range (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) →
      j = Fin.last k := by
    intro j hj
    induction j using Fin.lastCases with
    | last => rfl
    | cast i => exact absurd ⟨i, rfl⟩ hj
  have h := embedEmitCfg_eq (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
    (fun _ => d.workTapes (Fin.last k)) (fun _ => d.workTapePos (Fin.last k)) []
    (counterLoopBody a d)
    (⟨some a, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ : Cfg (k + 1) Γ S x)
    rfl rfl rfl (fun _ => ⟨rfl, rfl⟩)
    (fun j hj => by rw [hlast j hj]; exact ⟨rfl, rfl⟩)
  unfold counterLoopCfg
  rw [h]
  rfl

/-- The value of a counter word. -/
def counterValue (w : List Bool) : ℕ :=
  Nat.ofDigits 2 (w.map Bool.toNat)

/-- **The counter value is the parser's binary value**: the `foldr` of `Nat.bit` over a word, its
value as a little-endian binary numeral (`Turing.codeBitsNat`), is `Nat.ofDigits 2` of its bits,
the value `Turing.counterValue` that the counter loop counts down. (Moved unchanged, as a public
lemma, from the private `canonBits_value` of `TuringMachine/CodeSimulator.lean`, whose canonizer
still uses it.)

**Proof sketch.** `Nat.ofDigits 2` is a `foldr` of `b + 2·n` over the mapped digits; fuse the
map into the fold, and `b.toNat + 2·n` is `Nat.bit b n`. -/
theorem foldr_bit_eq_ofDigits (w : List Bool) :
    w.foldr Nat.bit 0 = Nat.ofDigits 2 (w.map Bool.toNat) := by
  rw [Nat.ofDigits_eq_foldr, List.foldr_map]
  have step : (fun (bit : Bool) (tail : ℕ) => (bit.toNat : ℕ) + 2 * tail) = Nat.bit := by
    funext bit tail
    cases bit <;> simp [Nat.bit, Nat.add_comm]
  simpa only [Nat.cast_id] using
    congrArg (fun f : Bool → ℕ → ℕ => w.foldr f 0) step.symm

/-- **The counter word of `t` has value `t`**: the canonical little-endian binary word `t.bits`,
used as a counter word, has `Turing.counterValue` exactly `t` (`0` for the empty word). It is the
value hypothesis of the counter loop's contracts (`Turing.counterLoopTM_run_done`, and
`Turing.StepBlock.loopTM_run`'s `ht`) for the deadline counter `bits t`.

**Proof sketch.** The counter value is the parser's binary value (`foldr_bit_eq_ofDigits`), and
binary reconstruction inverts `Nat.bits` (`Turing.codeBitsNat_bits`). -/
theorem counterValue_bits (t : ℕ) : counterValue t.bits = t := by
  rw [counterValue, ← foldr_bit_eq_ofDigits]
  exact codeBitsNat_bits t

/-- **The counter loop over a round contract, every round returning** (design §16a item 2; the
contract-level composition over the round layer). The index is the body data `i` and the counter
word `w`. An admissible host start holds `w`, delimited, at its counter head, and every one of
the `value w` rounds of the body orbit from its body (each round lasting the round contract's
time) is admissible and returns. The host then reaches `done` at the public theorem's exact time,
with the orbit after `value w` rounds as its body and the counter filled with `true`. The counter
head stays in `[cp - 1, cp + |w|]`, and the body heads in the hull of the rounds' envelopes and
the final body head (`Turing.RoundContract.hullLo`, `hullHi`).

**Proof sketch.** A segment to a first exit, so `Turing.Contract.ofSegment`. The host start is the
counter-loop configuration of its body (`Turing.counterLoopCfg_body`). The orbit's rounds are
rounds under the hull box (`Turing.RoundContract.orbit_round`) and return, so
`Turing.counterLoopTMVia_done_segment` gives the segment, with the counter interval and the hull
box on the body heads, which combine into the host box (`Turing.headBox_lastCases`). The endpoint
is at `done`. -/
noncomputable def RoundContract.counterLoopDone {S : Type} [DecidableEq S] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : MultiTapeTM k Γ S} {a : S} {exit : Option S} {ι : Type} {x : List Γ}
    (R : RoundContract M a {exit} ι x) :
    Contract (counterLoopTMVia e M a exit) (.dec .run) {some .done, some .escape}
      (ι × List Bool) x :=
  Contract.ofSegment
    (fun p d =>
      (∀ q : ℤ, -1 ≤ q → q ≤ (p.2.length : ℤ) →
        d.workTapes (Fin.last k) (d.workTapePos (Fin.last k) + q) =
          FinTM.bufferTape (p.2.map e) q) ∧
      ∀ r < counterValue p.2,
        R.pre p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r) ∧
        (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)).state = some a)
    (fun p d => ∑ r ∈ Finset.range (counterValue p.2),
      R.time p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r) +
      counterOverhead p.2 (counterValue p.2 + 1))
    (fun p d => counterLoopCfg (some .done)
      (roundOrbit M (R.time p.1) (counterLoopBody a d) (counterValue p.2))
      (fun q => if d.workTapePos (Fin.last k) ≤ q ∧
          q < d.workTapePos (Fin.last k) + (p.2.length : ℤ)
        then some (e true) else d.workTapes (Fin.last k) q)
      (d.workTapePos (Fin.last k)))
    (fun p d => Fin.lastCases (motive := fun _ => ℤ) (d.workTapePos (Fin.last k) - 1)
      (R.hullLo p.1 (counterLoopBody a d) (counterValue p.2)))
    (fun p d => Fin.lastCases (motive := fun _ => ℤ)
      (d.workTapePos (Fin.last k) + (p.2.length : ℤ))
      (R.hullHi p.1 (counterLoopBody a d) (counterValue p.2)))
    (fun p d hd hp => by
      have hc : (counterLoopBody a d).state = some a := rfl
      have hpre := fun r hr => (hp.2 r hr).1
      have hret : ∀ r, r + 1 < counterValue p.2 →
          (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)).state = some a :=
        fun r hr => (hp.2 r (by omega)).2
      have hseg := counterLoopTMVia_done_segment e M a exit (R.time p.1) (counterLoopBody a d)
        p.2 (d.workTapes (Fin.last k)) (d.workTapePos (Fin.last k)) hp.1 (counterValue p.2) rfl
        (R.orbit_start p.1 _ hc _ hpre hret) (fun r hr =>
          ⟨R.orbit_round p.1 _ hc _ hpre hret r hr, by
            rw [roundOrbit_succ, R.run p.1 _ (R.orbit_anchor p.1 _ hc _ hpre hret r hr)
              (hpre r hr)]
            exact (hp.2 r hr).2⟩)
      rw [← hd, counterLoopCfg_body] at hseg
      exact hseg.mono subset_rfl fun q hq => headBox_lastCases hq.1 hq.2)
    (fun _ _ _ _ => Set.mem_insert _ _)

/-- **The counter loop over a round contract, escaping at round `r₀`** (the contract-level
composition over the round layer). The index is the body data, the counter word and the escaping
round `r₀`, below the counter's value. Rounds `0` to `r₀` of the body orbit are admissible, the
first `r₀` return and round `r₀` escapes. The host reaches `escape` at the public theorem's exact
time, with the orbit after `r₀ + 1` rounds as its body and the counter decremented `r₀ + 1`
times; the envelope is the hull of the `r₀ + 1` round boxes, as in
`Turing.RoundContract.counterLoopDone`.

**Proof sketch.** As for `Turing.RoundContract.counterLoopDone`, through
`Turing.counterLoopTMVia_escape_segment`; the escape is the endpoint of round `r₀`, the next orbit
point. -/
noncomputable def RoundContract.counterLoopEscape {S : Type} [DecidableEq S] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : MultiTapeTM k Γ S} {a ex : S} (hea : ex ≠ a) {ι : Type} {x : List Γ}
    (R : RoundContract M a {some ex} ι x) :
    Contract (counterLoopTMVia e M a (some ex)) (.dec .run) {some .done, some .escape}
      (ι × List Bool × ℕ) x :=
  Contract.ofSegment
    (fun p d =>
      (∀ q : ℤ, -1 ≤ q → q ≤ (p.2.1.length : ℤ) →
        d.workTapes (Fin.last k) (d.workTapePos (Fin.last k) + q) =
          FinTM.bufferTape (p.2.1.map e) q) ∧
      p.2.2 < counterValue p.2.1 ∧
      (∀ r < p.2.2 + 1, R.pre p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)) ∧
      (∀ r, r + 1 < p.2.2 + 1 →
        (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)).state = some a) ∧
      (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) p.2.2)).state = some ex)
    (fun p d => ∑ r ∈ Finset.range (p.2.2 + 1),
      R.time p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r) +
      counterOverhead p.2.1 (p.2.2 + 1))
    (fun p d => counterLoopCfg (some .escape)
      (roundOrbit M (R.time p.1) (counterLoopBody a d) (p.2.2 + 1))
      (fun q => if d.workTapePos (Fin.last k) ≤ q ∧
          q < d.workTapePos (Fin.last k) + (p.2.1.length : ℤ)
        then FinTM.bufferTape ((counterWord p.2.1 (p.2.2 + 1)).map e)
          (q - d.workTapePos (Fin.last k))
        else d.workTapes (Fin.last k) q)
      (d.workTapePos (Fin.last k)))
    (fun p d => Fin.lastCases (motive := fun _ => ℤ) (d.workTapePos (Fin.last k) - 1)
      (R.hullLo p.1 (counterLoopBody a d) (p.2.2 + 1)))
    (fun p d => Fin.lastCases (motive := fun _ => ℤ)
      (d.workTapePos (Fin.last k) + (p.2.1.length : ℤ))
      (R.hullHi p.1 (counterLoopBody a d) (p.2.2 + 1)))
    (fun p d hd hp => by
      obtain ⟨hw, hr₀, hpre, hret, hesc⟩ := hp
      have hc : (counterLoopBody a d).state = some a := rfl
      have hexit : (roundOrbit M (R.time p.1) (counterLoopBody a d) (p.2.2 + 1)).state =
          some ex := by
        rw [roundOrbit_succ, R.run p.1 _ (R.orbit_anchor p.1 _ hc _ hpre hret p.2.2 (by omega))
          (hpre p.2.2 (by omega))]
        exact hesc
      have hseg := counterLoopTMVia_escape_segment e M a ex hea (R.time p.1)
        (counterLoopBody a d) p.2.1 (d.workTapes (Fin.last k)) (d.workTapePos (Fin.last k)) hw
        p.2.2 hr₀ (fun r hr => R.orbit_round p.1 _ hc _ hpre hret r (by omega)) hexit
      rw [← hd, counterLoopCfg_body] at hseg
      exact hseg.mono subset_rfl fun q hq => headBox_lastCases hq.1 hq.2)
    (fun _ _ _ _ => Set.mem_insert_of_mem _ rfl)

/-! The brief-inventory API (user 2026-10-16; its gate, finding 2): the two contract-level
counter loops' data fields as equations, generated by `simps!` (their bodies are
`Turing.Contract.ofSegment` applications) without the `simp` attribute. -/
attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  RoundContract.counterLoopDone RoundContract.counterLoopEscape

/-- **The counter loop's contract keeps the shared witness** (MIG-0a gate, round 2): the
contract-level joint trajectory of `Turing.RoundContract.counterLoopDone` is the public theorem's
relation, one round `r` and offset `u` at which every body head is the body's own, beyond the
per-tape hull that its envelope states.

**Proof sketch.** The same segment as the contract's, with the unweakened relation
(`Turing.counterLoopTMVia_done_witness`), from the host start rewritten as the counter-loop
configuration of its body. -/
theorem RoundContract.counterLoopDone_traj {S : Type} [DecidableEq S] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : MultiTapeTM k Γ S} {a : S} {exit : Option S} {ι : Type} {x : List Γ}
    (R : RoundContract M a {exit} ι x) :
    (R.counterLoopDone e).Traj fun p d q => ∃ r u,
      ((r < counterValue p.2 ∧
          u ≤ R.time p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)) ∨
        (r = counterValue p.2 ∧ u = 0)) ∧
      ∀ j : Fin k, q j.castSucc =
        (M.runFrom (roundOrbit M (R.time p.1) (counterLoopBody a d) r) u).workTapePos j := by
  intro p d hd hp u hu
  have hc : (counterLoopBody a d).state = some a := rfl
  have hpre := fun r hr => (hp.2 r hr).1
  have hret : ∀ r, r + 1 < counterValue p.2 →
      (R.post p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)).state = some a :=
    fun r hr => (hp.2 r (by omega)).2
  have hseg := counterLoopTMVia_done_witness e M a exit (R.time p.1) (counterLoopBody a d)
    p.2 (d.workTapes (Fin.last k)) (d.workTapePos (Fin.last k)) hp.1 (counterValue p.2) rfl
    (fun r hr =>
      ⟨R.orbit_round p.1 _ hc _ hpre hret r hr, by
        rw [roundOrbit_succ, R.run p.1 _ (R.orbit_anchor p.1 _ hc _ hpre hret r hr)
          (hpre r hr)]
        exact (hp.2 r hr).2⟩)
  rw [← hd, counterLoopCfg_body] at hseg
  exact (hseg.2.2 u hu).2

/-- **The escaping counter loop's contract keeps the shared witness**: as
`Turing.RoundContract.counterLoopDone_traj`, for `Turing.RoundContract.counterLoopEscape`.

**Proof sketch.** The contract's segment with the unweakened relation
(`Turing.counterLoopTMVia_escape_witness`). -/
theorem RoundContract.counterLoopEscape_traj {S : Type} [DecidableEq S] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : MultiTapeTM k Γ S} {a ex : S} (hea : ex ≠ a) {ι : Type} {x : List Γ}
    (R : RoundContract M a {some ex} ι x) :
    (R.counterLoopEscape e hea).Traj fun p d q => ∃ r u,
      ((r ≤ p.2.2 ∧ u ≤ R.time p.1 (roundOrbit M (R.time p.1) (counterLoopBody a d) r)) ∨
        (r = p.2.2 + 1 ∧ u = 0)) ∧
      ∀ j : Fin k, q j.castSucc =
        (M.runFrom (roundOrbit M (R.time p.1) (counterLoopBody a d) r) u).workTapePos j := by
  intro p d hd hp u hu
  obtain ⟨hw, hr₀, hpre, hret, hesc⟩ := hp
  have hc : (counterLoopBody a d).state = some a := rfl
  have hexit : (roundOrbit M (R.time p.1) (counterLoopBody a d) (p.2.2 + 1)).state =
      some ex := by
    rw [roundOrbit_succ, R.run p.1 _ (R.orbit_anchor p.1 _ hc _ hpre hret p.2.2 (by omega))
      (hpre p.2.2 (by omega))]
    exact hesc
  have hseg := counterLoopTMVia_escape_witness e M a ex hea (R.time p.1)
    (counterLoopBody a d) p.2.1 (d.workTapes (Fin.last k)) (d.workTapePos (Fin.last k)) hw
    p.2.2 hr₀ (fun r hr => R.orbit_round p.1 _ hc _ hpre hret r (by omega)) hexit
  rw [← hd, counterLoopCfg_body] at hseg
  exact (hseg.2.2 u hu).2

end Turing
