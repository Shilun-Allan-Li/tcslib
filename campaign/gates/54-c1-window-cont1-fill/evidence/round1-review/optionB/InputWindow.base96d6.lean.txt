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
# The bounded input window copier

A counter-driven copy of a bounded window of the native input onto a work tape (user decision 5
of 2026-10-13; the C1 design note §2.2 step U7 and §3.4 device (i)). The universal NDTM cannot
copy its whole input `x`, since its time bound has no `|x|` term; it copies the window
`x.take t` instead, and the input-locality lemma `Turing.NDTM.runWith_initCfg_take` shows that
the window is enough for `t` simulated steps. The in-place suffix device stays with the
universal machine U-1, whose `universal` has no deadline to truncate by.

## Main definitions

No new definitions: the copier is the existential contract `Turing.exists_inputWindowCopyTM`.

## Main results

* `Turing.exists_inputWindowCopyTM` — the window copier's contract (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the read-only input tape.)
-/

namespace Turing

/-- **The bounded input window copier.** For work tapes `j ≠ dst` there is a machine with an
entry state `entry`, a live exit `done` and a constant `C` such that: started at `entry` with its
input head at native position `p + 1` (on the `p`-th input symbol) and a delimited binary counter
word `w` of value `d` on tape `j` from its head (little-endian, blanks at both ends, the
convention of `Turing.counterLoopTM`), it copies the window `y = (z.drop p).take d` (the next
`d` input symbols, fewer if the input ends) onto tape `dst` from that tape's head. It reaches
`done` within `C·(|y| + 1) + 2|w|` steps, and not before, with the input head just after the
window, the head of `dst` just after the copy, the counter head back at its start, the counter
word replaced by some word of the same width, and every other tape, head and the output
unchanged. No `|z|` term. (A leaf row of the construction layer; [AB09, §1.2].)

**Proof sketch.** `Turing.counterLoopTM` over a one-step body on the native input and tape
`dst`: at an input symbol, write it on `dst` and move both heads right, returning to the body's
anchor; at the input's right end, escape. Each round costs a fixed number of steps; the round
count is `|y|`, or `|y| + 1` when the input ends first. The counter ledger has two cases. On
exhaustion (`|y| = d`), the whole counter overhead of the `d + 1` decrements, the final
underflow included, is at most `4d + 2|w| + 2` (`Turing.counterOverhead_le`, used once). On
early input end (`|y| < d`), the loop escapes in round `r = |y| + 1 ≤ d`, after `r`
decrements, which cost at most `4r + 2|w|` (`Turing.counterOverhead_le_of_le`). Either way the
total is at most `C·(|y| + 1) + 2|w|`. The exit-time and endpoint clauses are those of
`Turing.counterLoopTM_run_done` and `Turing.counterLoopTM_run_escape`. -/
theorem exists_inputWindowCopyTM (k : ℕ) (j dst : Fin k) (hjd : j ≠ dst) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (W : MultiTapeTM k Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {z : List Bool} (d : Cfg k Bool Q z) (p : ℕ) (w : List Bool),
        d.state = some entry → d.inputPos.val = p + 1 →
        (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
          d.workTapes j (d.workTapePos j + q) = FinTM.bufferTape w q) →
        let y := (z.drop p).take (Nat.ofDigits 2 (w.map Bool.toNat))
        ∃ T ≤ C * (y.length + 1) + 2 * w.length, ∃ w' : List Bool, w'.length = w.length ∧
          (W.runFrom d T).state = some done ∧
          (W.runFrom d T).inputPos.val = p + 1 + y.length ∧
          (W.runFrom d T).workTapes =
            Function.update (Function.update d.workTapes dst (fun q =>
              if d.workTapePos dst ≤ q ∧ q < d.workTapePos dst + (y.length : ℤ) then
                FinTM.bufferTape y (q - d.workTapePos dst)
              else d.workTapes dst q)) j (fun q =>
              if d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then
                FinTM.bufferTape w' (q - d.workTapePos j)
              else d.workTapes j q) ∧
          (W.runFrom d T).workTapePos =
            Function.update d.workTapePos dst (d.workTapePos dst + (y.length : ℤ)) ∧
          (W.runFrom d T).output = d.output ∧
          ∀ u < T, (W.runFrom d u).state ≠ some done := by
  sorry

end Turing
