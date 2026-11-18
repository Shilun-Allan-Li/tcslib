/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.InputLength

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2's simulation: the start-up

Before the first instruction, the simulating machine computes the word size `W = W (|x|)` with
the word-size witness, prepares its eight tapes and installs the start memory: the cell `-1`
holds `|x|` modulo `2^W` and every other cell `0` (`WordRAM.initMem`). This file states that
start-up for any word-size witness `Mw`; its extra tapes hold `Mw`'s tapes, and its output, which
is captured on a work tape.

## Main results

* `WordRAM.Sim.exists_startup`: the start-up reaches a configuration encoding
  `XCfg.init W |x|` within `tw + O(|x| + W² + 1)` steps and `sw + O(W + log |x| + 1)` cells,
  where `Mw` writes `Nat.bits W` within `tw` steps and `sw` cells.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §4.1, space-constructible functions.)
-/

namespace WordRAM.Sim

open Turing

/-- **The start-up.** For `a ≥ 1`, an output mode `fn` and a word-size witness `Mw`, there is a
machine with the eight tapes of `WordRAM.Sim.Encodes` first and `k'` more, and a constant `C`, such
that: whenever `Mw`, run on `x`, writes `Nat.bits W` within `tw` steps having visited at most `sw`
work cells, the machine, started at its entry on `x` with blank tapes, reaches its exit at some
time `t ≤ tw + C·(|x| + W² + 1)`, not earlier, in a configuration whose first eight tapes encode
`XCfg.init W |x|` over the cells `{-1}` with some origins, having visited at most
`sw + C·(W + log |x| + 1)` work cells. [AB09, Exercise 1.9]

**Proof sketch.**
1. Run `Mw` with its output captured on a work tape (`Turing.embedSilentTM`, its tapes and the
   capture tape among the `k'`), within `tw` steps and `sw` cells, plus the capture's
   `|Nat.bits W| + 1` cells.
2. Make the three word registers and the key register: expand `Nat.bits W` into `W` cells of `0`
   (`Turing.expandTM` with the pattern `[false]`, `O(W)` steps plus the counter overhead), copy
   it to the other registers, and extend the key register by `a` cells.
3. Rewind the input head and count `|x|` onto tape `5` (`Turing.exists_inputLengthTM`, `O(|x|)`
   steps, `O(log |x|)` cells).
4. Install the table `[(keyBits a W (-1), bvBits (wd W |x|))]`: the key by the integer-constant
   row with `c = -1`, the value by copying the low `W` bits of `Nat.bits |x|` into a register
   padded with zeros (modulo `2^W`), then the keyed assignment into the empty table.
   `TableOf` holds: `-1` is in range because `a ≥ 1`, and `initMem` is `0` elsewhere.
5. Return every head to its origin, clear the scratch tapes, and exit.
Each stage after the first costs `O(|x| + W² + 1)` steps and `O(W + log |x| + 1)` cells. -/
theorem exists_startup (a : ℕ) (ha : 1 ≤ a) (fn : Bool) (Mw : FinTM Bool) :
    ∃ (k' : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (8 + k') Bool S) (entry exit : S) (C : ℕ),
      ∀ (x : List Bool) (W tw sw : ℕ), Mw.ComputesInTime x (Nat.bits W) tw →
        Mw.tm.spaceUsed (Mw.tm.initCfg x) tw ≤ sw →
        ∃ (t : ℕ) (o : Fin 8 → ℤ), t ≤ tw + C * (x.length + W ^ 2 + 1) ∧
          (∀ s < t, (R.runFrom (Turing.Cfg.init entry x) s).state ≠ some exit) ∧
          (R.runFrom (Turing.Cfg.init entry x) t).state = some exit ∧
          Encodes a fn {-1} (XCfg.init W x.length) (Fin.castAddEmb k') o
            (R.runFrom (Turing.Cfg.init entry x) t) ∧
          R.spaceUsed (Turing.Cfg.init entry x) t ≤
            sw + C * (W + (Nat.bits x.length).length + 1) := by
  sorry

end WordRAM.Sim
