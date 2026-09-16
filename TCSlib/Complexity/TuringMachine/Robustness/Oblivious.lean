/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines

A machine is *oblivious* if its head movements depend only on the input length, not on
the input itself [AB09, Remark 1.7 and Exercise 1.5]. Obliviousness will matter for
the Cook-Levin theorem (Chapter 2), where the tableau of an oblivious computation has
input-independent structure.

## Design

* Configurations are indexed by their input, so head positions of runs on different
  inputs live in different types only for the input head; obliviousness compares
  `Fin`-valued input positions through `ℕ` and work positions (in `ℤ`) directly.
* Because halting is absorbing, a machine's head positions freeze when it halts.
  Consequently an oblivious machine necessarily halts after a number of steps that
  depends only on the input length (else two same-length inputs would freeze heads at
  different positions at large `t` — unless the frozen positions happen to agree).
  This is why the simulation below carries a `TimeConstructible` hypothesis, matching
  [AB09, Exercise 1.5]: the simulator must pad its own running time to an
  input-length-determined step count.
* We state the quadratic version (Exercise 1.5); the `O(T log T)` sharpening
  (Exercise 1.6) is a stretch goal alongside §1.7, off the critical path.

## Main definitions

* `Turing.FinTM.Oblivious` — [AB09, Remark 1.7].

## Main results

* `Complexity.oblivious_of_mem_DTIME` — [AB09, Exercise 1.5]: every language decidable
  in time-constructible time `T` is decided by an oblivious machine in `O((T + 1)²)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, p. 17; Exercise 1.5, p. 34.)
-/

namespace Turing.FinTM

/-- A machine is *oblivious* if, at every step, its head positions on two inputs of
the same length agree: they are a function of the input length and the time only.
[AB09, Remark 1.7] -/
def Oblivious {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (x y : List Γ), x.length = y.length → ∀ t : ℕ,
    (((M.tm.runFrom (M.tm.initCfg x) t).inputPos : ℕ) =
      ((M.tm.runFrom (M.tm.initCfg y) t).inputPos : ℕ)) ∧
    (M.tm.runFrom (M.tm.initCfg x) t).workTapePos =
      (M.tm.runFrom (M.tm.initCfg y) t).workTapePos

end Turing.FinTM

namespace Complexity

open Turing

/-- **Oblivious simulation** [AB09, Exercise 1.5]: for time-constructible `T`, every
language in `DTIME T` is decided by an *oblivious* machine within `c · (T n + 1)²`.

**Proof sketch.** Take a decider `M` for `L` within `a · T n`. The oblivious simulator
first runs the `TimeConstructible` witness to obtain `⌞T n⌟` on a work tape — its head
movements on this phase are made length-determined by sweeping to the input boundary
rather than reacting to symbols. It then performs `Θ(T n)` full sweeps over a zone of
size `Θ(T n)`, one sweep per simulated step of the one-work-tape form of `M`
(`Turing.FinTM.one_work_tape_binary`), always sweeping the whole zone regardless of
where the simulated head sits, and continues sweeping idly (ignoring the halted
simulated configuration) until a step counter derived from `⌞T n⌟` expires, emitting
the answer in a final length-determined flourish. Every head trajectory is a function
of `n` and `t` alone; the cost is `Θ((T n + 1)²)`. -/
theorem oblivious_of_mem_DTIME {L : Language Bool} {T : ℕ → ℕ}
    (hT : TimeConstructible T) (hL : L ∈ DTIME T) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.Oblivious ∧ M.DecidesInTime L fun n => c * (T n + 1) ^ 2 := by
  sorry

end Complexity
