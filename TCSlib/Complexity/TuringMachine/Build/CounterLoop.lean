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
  sorry

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
  sorry

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
  sorry

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

/-- Decrements preserve the counter's width.

**Proof sketch.** `decFixed` preserves length, by induction on the word, and
`Option.getD` keeps the word otherwise; induct on `r`. -/
theorem counterWord_length (w : List Bool) (r : ℕ) :
    (counterWord w r).length = w.length := by
  sorry

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
  sorry

/-- **Prefix amortization.** The first `r` decrements, for `r` at most the
counter's value, cost at most `4r + 2|w|`.

**Proof sketch.** The `j`th decrement acts on a word of value `n - j`
(`Turing.counterWord_value`), where `n` is the counter's value, and its
`false` prefix is the number of trailing zero bits of that value. Summed over
`r` consecutive values below `2^|w|`, the trailing zeros total
`ν₂(r!) + ν₂(binom) ≤ (r - 1) + (|w| - 1)` by Legendre and Kummer, so the
cost is at most `4r + 2|w| - 4` once `r ≥ 1`. -/
theorem counterOverhead_le_of_le (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r ≤ 4 * r + 2 * w.length := by
  sorry

/-- **Whole-run amortization** (design §12.7, decision 12.7.6). Counting a
counter of value `n` down to zero and through the final underflow costs at
most `4n + 2|w| + 2`.

**Proof sketch.** The successful decrements act on the values `n, …, 1`,
whose trailing zeros sum to `n - s₂(n) ≤ n` (Legendre), so they cost at most
`4n`. The final word is all `false` (`Turing.counterWord_value`), so the
underflow sweep costs `2|w| + 2` (`Turing.counterWord_length`). -/
theorem counterOverhead_le (w : List Bool) :
    counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) ≤
      4 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

end Turing
