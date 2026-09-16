/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Order.Monotone.Defs
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition of Turing machine computations

Basic computability combinators for the bundled machines: the identity and constant
functions are linear-time computable, and time-bounded computability is closed under
composition. Composition is the load-bearing lemma of the whole development — the
universal machine (phase 3) and the `HALT` reduction (phase 4) are built from it — and
it is the part [AB09] never spells out, dispatching it with "high-level descriptions"
of machines. The Isabelle AFP `Cook_Levin` entry spends a large fraction of its effort
exactly here.

## Design

Composition is stated at the *specification* level (`ComputesFunInTime`), not as an
operator on raw machines: the composed machine is existentially produced. Internally
(proof obligation, not API) the construction simulates `M₁` with its emissions
redirected to a fresh work tape, then simulates `M₂` reading that tape in place of its
input tape.

**Convention obligation status** (phase-1 audit finding 4; phase-2 audit finding 3):
this file does *not* formally discharge the append-only vs read-write output-tape
bridge. Every statement here — hypotheses and conclusions alike — lives in the
append-only model, and [AB09]'s read-write-output machine is not formalized in this
development, so no simulation between the two conventions can even be stated yet. The
obligation is recorded in the plan's decision log as **waived**, with the compensating
restriction that no exact-step-count transfer from [AB09] is ever claimed: all bounds
carry existential constants and every result is self-contained in-model. A formal
bridge (a read-write-output machine variant plus a simulation theorem) will be added
if and only if a downstream result needs it. What this file *does* provide is the
buffer-and-flush technique — an emission can be deferred to a work tape and flushed at
the end — which is the in-model reason the append-only convention costs no generality.

## Main results

* `Complexity.TuringMachine`-level combinators (all over the binary alphabet):
  `Turing.FinTM.computesFunInTime_id`, `Turing.FinTM.computesFunInTime_const`,
  `Turing.FinTM.computesFunInTime_comp`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
* [Balbach22] F. J. Balbach, *The Cook-Levin theorem*, Archive of Formal Proofs
  (Isabelle), 2022 — the composition-combinator architecture this file follows in
  spirit.
-/

namespace Turing.FinTM

/-- The identity function is computable in linear time.

**Proof sketch.** A zero-work-tape machine with one state: on reading an input bit,
emit that bit and move right; on reading the boundary blank, halt. It halts within
`n + 1` steps having emitted its input verbatim. -/
theorem computesFunInTime_id :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id fun n => c * (n + 1) := by
  sorry

/-- Every constant function is computable in linear time (in fact in time `|w| + 1`,
which the stated bound dominates once `c ≥ |w| + 1`).

**Proof sketch.** A zero-work-tape machine with `|w| + 1` states `s₀, …, s_{|w|}`:
state `sᵢ` emits the `i`-th symbol of `w` and moves to `s_{i+1}`, ignoring the input;
`s_{|w|}` halts. -/
theorem computesFunInTime_const (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) fun n => c * (n + 1) := by
  sorry

/-- **Composition.** If `f` is computable within `T₁` and `g` within a monotone `T₂`,
then `g ∘ f` is computable within `c · (T₁ n + T₂ (T₁ n) + 1)`.

The inner bound `T₂ (T₁ n)` is valid because the intermediate string is no longer than
the time that produced it: `|f x| ≤ T₁ |x|` by `Turing.MultiTapeTM.output_length_le`.
Monotonicity of `T₂` is genuinely needed to convert that length bound into a time
bound.

**Proof sketch.** Build `M` with `M₁.k + M₂.k + 1` work tapes over `Bool`. Phase one
simulates `M₁` step for step on the true input, with `M₁`'s emissions written instead
onto the dedicated intermediate tape (constant overhead per step; this is the
append-only-output buffering discussed in the module docstring). Phase two rewinds the
intermediate tape head (at most `T₁ n` steps) and simulates `M₂` step for step, with
`M₂`'s input-head reads served from the intermediate tape and `M₂`'s emissions going to
the real output tape. Phase two costs constant overhead per step of `M₂`, which halts
within `T₂ |f x| ≤ T₂ (T₁ n)` steps. Bookkeeping (phase switching, boundary detection
on the intermediate tape) is absorbed into `c`. -/
theorem computesFunInTime_comp {M₁ M₂ : FinTM Bool} {f g : List Bool → List Bool}
    {T₁ T₂ : ℕ → ℕ}
    (h₁ : M₁.ComputesFunInTime f T₁) (h₂ : M₂.ComputesFunInTime g T₂)
    (hT₂ : Monotone T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (g ∘ f) fun n => c * (T₁ n + T₂ (T₁ n) + 1) := by
  sorry

end Turing.FinTM
