/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Constructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The word size of a simulated word RAM

Stage 2 (backlog PROG-4) runs a word-RAM program with a word size `W` that depends on the input
length, and its machine computes `W (|x|)` itself, once, at the start (design §16b item 1). The
hypothesis is `WordRAM.WordSizeComputable W TW SW` (user decision, 2026-10-12): some machine
writes `W (|x|)` in binary within `TW (|x|)` steps and `SW (|x|)` work cells. Two bridges supply
it for the two kinds of consumer:

* `wordSizeComputable_logSpace`: `W = c · logSpace`, in linear time and logarithmic space, for
  the P and L grades (from the input-length counter R8.5c);
* `wordSizeComputable_of_spaceConstructible`: `W = c · S` in space `O(S)`, for Savitch's shape
  (from the constructibility witness of `S`).

`Complexity.SpaceConstructible` is not used directly: it has no time clause, so the P grade could
not use it, and it carries the conjunct `logSpace ≤ S`, which stage 2 does not need.

## Main definitions

* `WordRAM.WordSizeComputable`.

## Main results (statements gated 2026-10-14, `audits/stage2-statements-findings.md`; proofs pending)

* `WordRAM.WordSizeComputable.mono`.
* `WordRAM.wordSizeComputable_logSpace`, `WordRAM.wordSizeComputable_of_spaceConstructible`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3 and §4.1, p. 79: time- and space-constructible
  functions.)
-/

namespace WordRAM

/-- **The word size is computable within `TW` and `SW`**: some finite binary machine, on every
input `x`, halts within `TW |x|` steps with the binary representation of `W (|x|)` on its output
tape (`Nat.bits`, as in `Complexity.SpaceConstructible` and `Complexity.TimeConstructible`), having
visited at most `SW |x|` work cells up to then. The stage-2 machine runs it once, at the start,
with its output captured on a work tape, and pays `TW` and `SW` once. Deviation: it bounds time
and space together, where [AB09] has separate time- and space-constructibility (§1.3, §4.1);
design §16b item 1. -/
def WordSizeComputable (W TW SW : ℕ → ℕ) : Prop :=
  ∃ M : Turing.FinTM Bool, ∀ x : List Bool, ∃ t ≤ TW x.length,
    M.ComputesInTime x (W x.length).bits t ∧ M.tm.spaceUsed (M.tm.initCfg x) t ≤ SW x.length

/-- A word size computable within `TW` and `SW` is computable within any larger bounds.

**Proof sketch.** The same machine and halting times; `t ≤ TW n ≤ TW' n`, and the space bound
weakens pointwise. -/
theorem WordSizeComputable.mono {W TW SW TW' SW' : ℕ → ℕ} (h : WordSizeComputable W TW SW)
    (hT : ∀ n, TW n ≤ TW' n) (hS : ∀ n, SW n ≤ SW' n) : WordSizeComputable W TW' SW' := by
  sorry

/-- **Logarithmic word sizes** (the P and L grades): for every `c`, the word size
`c · (⌊log₂ n⌋ + 1)` is computable in linear time and logarithmic space.

**Proof sketch.** R8.5c (`Turing.exists_inputLengthTM`, `Build/InputLength.lean:473`) writes
`Nat.bits |x|` on a work tape within `C·(|x| + 1)` steps and `C·(|bits |x|| + 1)` cells; setting
its first cell to `true` gives a word of length `logSpace |x|` at every length, `|x| = 0`
included. This is the route of `Complexity.spaceConstructible_logSpace`
(`SpaceComplexity/Constructible.lean:485`), whose private machine `b3a_log_machine` (`:329`)
bounds the space but states no time, so the fill states its time or re-derives it from
`Turing.FinTM.computesFunInTime_lengthBits_spaceUsed` (`Build/Catalog.lean:4318`). A counter pass
over that word writes its length in binary, a carry pass multiplies it by `c`, and the result is
emitted. Time `O(|x| + 1)`; space `O(logSpace |x|)`, since `logSpace n ≥ 1`. -/
theorem wordSizeComputable_logSpace (c : ℕ) :
    ∃ a : ℕ, WordSizeComputable (fun n => c * Complexity.logSpace n) (fun n => a * (n + 1))
      (fun n => a * Complexity.logSpace n) := by
  sorry

/-- **Space-constructible word sizes** (Savitch's shape): if `S` is space-constructible, then for
every `c` the word size `c · S(n)` is computable in space `O(S(n))`, within some time bound `TW`
that is not controlled and that the space grades do not need.

**Proof sketch.** Run the constructibility witness with its output captured on a work tape (the
R1 silent embedding `Turing.embedSilentTM`, `Build/Embed.lean:241`), multiply by `c` with a carry
pass, and emit. Space: `c_S·S + O(log (c·S) + 1) ≤ a·S`, since `S ≥ logSpace ≥ 1` (a conjunct of
`Complexity.SpaceConstructible`). Time: the witness halts on every input, since
`Turing.FinTM.ComputesInSpace` asks for a halting time; so the largest halting time over the
`2^n` inputs of length `n`, plus the multiplication, is a bound `TW n`. -/
theorem wordSizeComputable_of_spaceConstructible {S : ℕ → ℕ}
    (hS : Complexity.SpaceConstructible S) (c : ℕ) :
    ∃ (a : ℕ) (TW : ℕ → ℕ), WordSizeComputable (fun n => c * S n) TW (fun n => a * S n) := by
  sorry

end WordRAM
