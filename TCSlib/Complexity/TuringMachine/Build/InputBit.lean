/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.WordArith
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.InputLength

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading an input bit at a position held in a word

The input of a machine is read in place: its head moves, and nothing is copied to a work tape.
This file states the row that reads the input bit at a position given as a signed word on a work
tape, with the input's length in binary on another: it writes the word `1` if the position lies
on the input and the bit there is `true`, and the word `0` otherwise, off the input and at
negative positions included. Its work-tape space is `O(W + log n)`, not `O(n)`, so a logarithmic
space bound survives it. It is the `rdIn` instruction of a word RAM run on a Turing machine
(`WordRAM.exists_simulation`).

## Main results

* `Turing.exists_inputBitTM`: the row, within `O(W + n)` steps and `O(W + log n)` cells of
  radius.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: the read-only input of a space-bounded machine;
  Exercise 1.9.)
-/

namespace Turing

/-- **Reading an input bit at a word's position.** A five-tape machine over `Bool`. From the entry,
with a word `u` of `W` bits on tape `0`, the input length `Nat.bits |x|` on tape `1`, a register
word of `W` cells on tape `2` and blank scratch tapes (`Turing.ScratchBlank`), the input head
anywhere: the row writes on tape `2` the word `1` if `0 ≤ u.toInt` and the input bit at position
`u.toInt` is `true`, and the word `0` otherwise (positions past the input read `false`), and
stops at its exit within `C·(W + |x| + 1)` steps, every work head within `C·(W + log |x| + 1)`
cells and back where it started. The input head ends somewhere. [AB09, §4.1, Exercise 1.9]

**Proof sketch.** Sign test (`Turing.exists_wordSignTM`): a negative position reads `0`.
Otherwise compare `u`'s value with `|x|` (both little-endian; a lockstep comparison of different
lengths, the longer word's excess bits deciding when nonzero): a position `≥ |x|` reads `0`.
Otherwise copy `u` to a scratch tape, increment it once (the input head's position `p + 1` holds
bit `p`; no overflow, since `u.toInt < |x|` and the sign bit is clear), and seek the input head
there with `Turing.exists_inputSeekTM`, whose work envelope is `O(W)` and time
`O(W + pos + p + 1) = O(W + |x|)`. Read the bit under the input head and write `1` or `0` over
the register (`Turing.exists_wordIntTM`). Clear the scratch tapes and return the heads. -/
theorem exists_inputBitTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (Nat.bits x.length) →
        WordAt d 2 w → w.length = W → ScratchBlank d →
        ∃ ip : Fin (x.length + 2),
          ReachesWithin R d {some exit} (C * (W + x.length + 1))
            (C * (W + (Nat.bits x.length).length + 1))
            { d with state := some exit, inputPos := ip,
                     workTapes := wordWrite d 2 (bvBits
                       (if 0 ≤ u.toInt ∧ x.getD u.toInt.toNat false = true then (1 : BitVec W)
                        else 0)) } := by
  sorry

end Turing
