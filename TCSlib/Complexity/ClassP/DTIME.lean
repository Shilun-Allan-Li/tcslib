/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  sorry

end Complexity
