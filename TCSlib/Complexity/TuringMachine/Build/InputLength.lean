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
# Machine-construction library: the input length in binary (§12.8, R8.5c)

The native-input row R8.5c of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §3, §12.8b): count the native input into a
little-endian binary word on a dedicated work tape, `Nat.bits |x|`, in linear
time and logarithmic work space. It is a `Bool` module; a rich host runs it
lifted along its digit embedding (`Turing.MultiTapeTM.liftSymbols`), with
unchanged time and space. The record template and the initial record
(`Build/RecordTable.lean`) take their position width from it, and the
space-constructibility witnesses of chapter 4 count with it.

**Status: statement.** The row is an existential module in the
`Turing.exists_inputSeekTM` style, sorried with a construction sketch, pending
the §12.8b fill.

## Design

* **Own module** (§12.8b decision proposal W1-5): the natural home is beside
  `Turing.exists_inputSeekTM` in `Build/InputCall.lean`, which an in-flight fill
  batch owns. This module imports only `Build/CounterLoop`, so the
  constructibility files can import it without the record layer; 12.2c may fold
  it into `Build/InputCall.lean`.
* **Framed output.** The dedicated tape need only be blank on the interval the
  word and its two delimiters occupy, so the module also runs on a tape that
  carries unrelated data elsewhere.
* **Input position.** The module starts with the input head at `1` and returns it
  there, as `Turing.inputCopyTM` and `Turing.inputFoldTM` do.

## Main results

* `Turing.exists_inputLengthTM` — write `Nat.bits |x|` on a dedicated tape
  (statement).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3 and §4.1: a machine counts its input
  length in binary with a work-tape counter in `O(log n)` space; p. 79, the
  space-constructibility of `log n`.)
-/

namespace Turing

/-- **R8.5c, the input length** (design §12.8a §3, §12.8b). There is a `Bool`
module with an entry and an exit state and `K + 1` tapes with the following
contract. Start it at its entry with the input head at position `1`, tape `0`
blank on the `|bits |x|| + 2` cells from one left of its head to one right of
where the word will end, and the other tapes blank. It reaches its exit within
`C·(|x| + 1)` steps, and not earlier. At that point tape `0` holds
`Nat.bits |x|` from its head, and every other cell, every head, the input
position and the output are as they were. Up to the exit every work head stays
within `C·(|bits |x|| + 1)` cells of its entry position, so the work space is
logarithmic in `|x|` however far the input head travels. At `x = []` nothing is
written, since `Nat.bits 0 = []`.

**Proof sketch.** One pass over the input drives an in-place binary counter on
tape `0`. For each input symbol, move the input head right and increment the
counter: the carry turns the maximal `true` prefix to `false` and writes `true`
on the next cell, which is the blank just after the word when the counter
overflows, so the width grows by one cell exactly at the powers of two. A
return pass brings the counter head back to its first cell, guided by the
blank delimiter on its left. At the input's right end marker, walk the input
head back to position `1` (the `Turing.inputFoldTM_run_ofCfg` return) and exit.
The increments from `0` to `|x|` cost `Σ_v (2·p_v + 2)` for the true-prefix
lengths `p_v`, which telescopes against twice the number of `true` cells, as
in `Turing.counterOverhead_le_of_le` mirrored, so the total is linear in
`|x|`. Route: the counting phase is the transition table of Catalog's private
`f2_counterTM` without its emission, framed; no public input-driven loop host
exists (`Turing.counterLoopTM` needs its round count on a tape, which is what
is being computed), so the fill proves the framed round induction for this
table directly and records the pair with `f2_counterTM` for 12.2c, which can
re-derive `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed` from this row.
The counter head stays in `[pos - 1, pos + |bits |x||]`. -/
theorem exists_inputLengthTM :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM (K + 1) Bool S)
      (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} (d : Cfg (K + 1) Bool S x), d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((Nat.bits x.length).length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 1),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((Nat.bits x.length).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + ((Nat.bits x.length).length : ℤ)
                  then FinTM.bufferTape (Nat.bits x.length) (q - d.workTapePos j)
                else d.workTapes j q } := by
  sorry

end Turing
