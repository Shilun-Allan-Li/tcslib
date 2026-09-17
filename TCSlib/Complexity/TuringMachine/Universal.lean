/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The universal Turing machine

[AB09, §1.4.1 and Theorem 1.9, relaxed form]: there is a single machine `U` that, given
`⟨x, α⟩`, simulates the machine coded by `α` on input `x` — with the simulation
overhead depending only on the coded machine, not on the input.

## Design and deviations from [AB09]

* Everything is stated relative to an arbitrary representation scheme
  (`Turing.MachineCode`), with the input convention `Turing.pairEncode x ⌞M⌟`.
* **The core simulation is linear, not quadratic**: coded machines (`Turing.CodeTM`)
  are already in one-work-tape binary normal form, so `U` pays only a constant factor
  `C` (depending on the coded machine) per simulated step — `C · (t + 1)`. [AB09]'s
  relaxed quadratic bound reappears in `universal_quadratic`, where an *arbitrary*
  binary machine is first normal-formed via [AB09, Claims 1.5-1.6]
  (`Turing.FinTM.one_work_tape_binary`), and that is where the `(t + 1)²` comes from.
  The `O(T log T)` sharpening ([AB09, §1.7], Hennie-Stearns) is the phase-5 stretch
  goal, off the critical path.
* **The timed machine's failure convention**: `U` outputs `true :: output` when the
  simulated machine halts within the budget with output `output`, and `[false]` on
  timeout — a concrete rendering of [AB09]'s "special failure symbol" (§1.4.1,
  "Universal TM with time bound"). Its budget is quadratic because maintaining the
  binary step counter costs `O(log t)` per simulated step.

## Main results

* `Turing.universal` — [AB09, Theorem 1.9] for coded machines, linear overhead.
* `Turing.universal_quadratic` — [AB09, Theorem 1.9, relaxed form] for arbitrary
  binary machines.
* `Turing.timed_universal` — the time-bounded universal machine [AB09, §1.4.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21; Figure 1.6.)
-/

namespace Turing

/-- **The universal machine** [AB09, Theorem 1.9, for coded machines]: for any
representation scheme there is a single machine `U` such that for every coded machine
`M` there is a constant `C` (depending only on `M`) with: whenever `M` halts on `x`
within `t` steps with output `output`, `U` on `⟨x, ⌞M⌟⟩` halts within `C · (t + 1)`
steps with the same output.

**Proof sketch** (after [AB09, Figure 1.6], simplified because `M` is already in
one-work-tape binary normal form). `U` has three work tapes: a *table* tape, a *state*
tape, and a *work* tape mirroring `M`'s work tape. Startup: `U` scans its input past
the doubled-bit region to the separator, decodes `α` onto the table tape (as the
fixed-width record table of the scheme's parse) and writes `M`'s initial state on the
state tape — cost bounded by a constant depending on `|⌞M⌟|`, absorbed into `C`. To
read `M`'s input bit `i`, `U` positions its input head at cell `2i` of the doubled
region (its simulated input-head position is maintained by moving two cells per
simulated move; the separator marks the boundary blank). Each simulated step: read the
work-tape symbol under the mirrored head and the simulated input symbol, scan the
table for the record matching (state, input read, work read) — at most the table
length, a constant in `t` — then apply the record: update the state tape, write/move
on the mirrored work tape, emit `M`'s emission verbatim. Halting and output transfer,
and the total is `C · (t + 1)`. -/
theorem universal (c : MachineCode) :
    ∃ U : FinTM Bool, ∀ M : CodeTM, ∃ C : ℕ, ∀ (x output : List Bool) (t : ℕ),
      M.toFinTM.ComputesInTime x output t →
      U.ComputesInTime (pairEncode x (c.encode M)) output (C * (t + 1)) := by
  sorry

/-- **The universal machine, relaxed quadratic form** [AB09, Theorem 1.9 as proved in
§1.4.1]: for every binary machine computing a function `f` within `T`, there is a code
`α` and a constant `C` such that the *same* universal machine `U` computes `f x` from
`⟨x, α⟩` within `C · (T |x| + 1)²`.

**Proof sketch.** Normal-form the machine with `Turing.FinTM.one_work_tape_binary`
(quadratic, [AB09, Claims 1.5-1.6]), relabel its states with `Turing.exists_codeTM`,
take `α` to be that coded machine's code, and apply `Turing.universal`; the constants
compose as `C_U · (c₁ · (T n + 1)² + 1) ≤ C · (T n + 1)²`. -/
theorem universal_quadratic (c : MachineCode) :
    ∃ U : FinTM Bool, ∀ (M₀ : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ),
      M₀.ComputesFunInTime f T →
      ∃ (α : List Bool) (C : ℕ), ∀ x : List Bool,
        U.ComputesInTime (pairEncode x α) (f x) (C * (T x.length + 1) ^ 2) := by
  sorry

/-- **The time-bounded universal machine** [AB09, §1.4.1, "Universal TM with time
bound"]: a single machine that, given `⟨x, ⟨⌞t⌟, ⌞M⌟⟩⟩`, simulates `M` on `x` for at
most `t` steps, reporting success (`true :: output`) or timeout (`[false]`).

**Proof sketch.** Extend the simulation of `Turing.universal` with a binary countdown
clock on a fourth work tape, initialized from `⌞t⌟` (parsed from the doubled-bit
region of the second pairing). Each simulated step decrements the clock
(`O(log t + 1)` amortized-to-worst-case per step, whence the quadratic budget) and
`U` buffers `M`'s emissions on a work tape instead of emitting them. If `M` halts
before the clock expires, `U` emits `true` and then flushes the buffered output; if
the clock reaches zero first, `U` emits `false` and halts. The two cases below are
exhaustive: "`M` halts on `x` within `t` steps with some output" or not. -/
theorem timed_universal (c : MachineCode) :
    ∃ U : FinTM Bool, ∀ M : CodeTM, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      (∀ output : List Bool, M.toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode x (pairEncode (Nat.bits t) (c.encode M)))
          (true :: output) (C * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬M.toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode x (pairEncode (Nat.bits t) (c.encode M)))
          [false] (C * (t + 1) ^ 2)) := by
  sorry

end Turing
