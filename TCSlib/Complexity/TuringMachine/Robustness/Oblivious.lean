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
* `Oblivious` constrains *represented* head trajectories only — the input head and
  the work heads. Our model has no output-head position (output is an append-only
  stream), so emission schedules are deliberately unconstrained; [AB09]'s read-write
  output head is covered by this reading only via a bridge, e.g. a machine that emits
  once at a fixed final time, as the decider produced below does.
* `Oblivious` does **not** imply that the halting time is determined by the input
  length: heads freeze on halting, but frozen positions can coincidentally agree — a
  stationary-head machine can halt after one or two steps depending on its first
  input bit while satisfying `Oblivious` (phase-2 audit, finding 1, with an explicit
  counterexample in `audits/phase2-findings.md`). The `TimeConstructible` hypothesis
  below is required by the *construction* (the simulator derives a length-determined
  step budget and pads its schedule to it), not forced by the definition. If a
  downstream use (the Cook-Levin tableau, Ch. 2) needs length-determined halting or a
  simultaneous one-work-tape oblivious normal form (`M.k = 1 ∧ M.Oblivious`), those
  are separate conjuncts for that normal-form theorem.
* We state the quadratic version — Exercise 1.5's *first assertion*, adapted to this
  model; the exercise's final two-tape normal form is **not** included here. The
  `O(T log T)` sharpening (Exercise 1.6) is a stretch goal alongside §1.7, off the
  critical path.

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

/-- **Oblivious simulation** — the first assertion of [AB09, Exercise 1.5], adapted
to this model: for time-constructible `T`, every language in `DTIME T` is decided by
an *oblivious* machine within `c · (T n + 1)²`. (The exercise's additional two-tape
normal form is not part of this statement.)

**Proof sketch** (corrected per the phase-2 audit, finding 2: the construction must
not invoke `one_work_tape_binary` per simulated step — that composes quadratics into
a quartic — must not run the constructibility witness verbatim, which need not be
oblivious, and must park the real input head). Take a decider for `L` within
`a · T n` and a constructibility witness within `b · (T n + 1)`.

1. Run the witness with every non-blank input symbol *read as `false`* (substituted
   in its transition table): its entire run — trajectories, emissions, halting time —
   then coincides with its run on the all-`false` input of length `n`, hence depends
   only on `n`, and it still computes `⌞T n⌟`; store the budget on a work tape.
2. Copy the real input to a work tape in one fixed scan and rewind (cost
   `O(n + 1)`, absorbed since `n ≤ T n`), then park the real input head for good.
3. Set `B n = (a + 1) · (T n + 1)` macrosteps and prepare a marked layout of size
   `O(B n)` holding the decider's work tapes, the virtual input copy, virtual head
   markers, and a step counter.
4. Each macrostep simulates one step of the decider by a fixed number of full sweeps
   of the layout — tape data affects writes, simulated state, and markers, never the
   sweep path or its duration — idling identically once the simulated machine halts,
   for exactly `B n` macrosteps (counter maintenance within the per-macrostep linear
   allowance; fixed-duration binary block coding throughout, so no appeal to the
   existential `alphabet_reduction` is needed to stay binary and oblivious).
5. Emit the stored answer bit at a fixed final time and halt.

Every head trajectory and the halting time are then functions of `n` and `t` alone,
and the total cost is `O(b · (T n + 1) + (B n)²) = O((T n + 1)²)`. -/
theorem oblivious_of_mem_DTIME {L : Language Bool} {T : ℕ → ℕ}
    (hT : TimeConstructible T) (hL : L ∈ DTIME T) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.Oblivious ∧ M.DecidesInTime L fun n => c * (T n + 1) ^ 2 := by
  sorry

end Complexity
