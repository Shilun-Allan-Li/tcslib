/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.Uncomputability.Computable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uncomputability by diagonalization

[AB09, §1.5, Theorem 1.10]: the diagonal function `UC` is not computable. This is
the theorem the whole encoding layer (`TCSlib.Complexity.TuringMachine.Encoding`)
has been building toward: it needs machines-as-strings and nothing else — not even
the universal machine.

## Design and deviations from [AB09]

* `UC` is defined relative to an **arbitrary** representation scheme
  `Turing.MachineCode`, and Theorem 1.10 is stated at that generality: the
  diagonalization *chooses* one fixed code — `c.encode` of the hypothetical
  decider's normal form — inside a mathematical contradiction, and no machine ever
  computes `encode` or `decode` (phase-3 audit, round 2, Argument F). Effectivity
  (`Turing.EffectiveMachineCode`) is needed only where a machine must *run* codes:
  the universal machine, and the `HALT` reduction of
  `TCSlib.Complexity.Uncomputability.Halting`.
* Output convention: [AB09] writes `M_α(α) = 1`; in this model that is the completed
  singleton output `[true]`. Accordingly `UC c α = true` covers divergence *and*
  every completed output other than `[true]` — exactly the complement of the book's
  acceptance condition (Argument F's reading).
* [AB09] fixes one standing representation once and for all; here the scheme is a
  parameter, so `UC` is a family of functions and Theorem 1.10 a family of
  theorems, each an instance of the book's.

## Main definitions

* `Complexity.UC` — the diagonal function. [AB09, §1.5]

## Main results

* `Complexity.UC_not_computable` — [AB09, Theorem 1.10].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.5, Theorem 1.10, pp. 21-22.)
-/

namespace Complexity

open Turing

open Classical in
/-- The diagonal function `UC` of a representation scheme [AB09, §1.5]: `UC c α` is
`false` iff the machine `α` denotes *accepts its own representation* — that is,
`(c.decode α).toFinTM` halts on input `α` with completed output `[true]`. On
divergence, and on any completed output other than `[true]`, the value is `true`.
([AB09] writes: `UC(α) = 0` if `M_α(α) = 1`, and `UC(α) = 1` otherwise.) -/
noncomputable def UC (c : MachineCode) (α : List Bool) : Bool :=
  if ∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t then false else true

/-- Unfolding lemma: `UC c α = false` iff the denoted machine accepts its own
representation. -/
theorem UC_eq_false_iff (c : MachineCode) (α : List Bool) :
    UC c α = false ↔ ∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t := by
  unfold UC
  split <;> simp_all

/-- Unfolding lemma: `UC c α = true` iff the denoted machine does not accept its own
representation — it diverges on it, or completes with an output other than
`[true]`. -/
theorem UC_eq_true_iff (c : MachineCode) (α : List Bool) :
    UC c α = true ↔ ¬∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t := by
  unfold UC
  split <;> simp_all

/-- **`UC` is not computable** [AB09, Theorem 1.10] — for every representation
scheme, effective or not.

**Proof sketch** (diagonalization, [AB09, proof of Theorem 1.10]; blueprint:
phase-3 audit round 2, Argument F). Suppose some machine computes
`fun α => [UC c α]`. `Turing.FinTM.Computes.exists_computesFunInTime` supplies a
time bound; `Turing.FinTM.one_work_tape_binary` normal-forms the machine into a
one-work-tape binary machine computing the same function; `Turing.exists_codeTM`
relabels that into a coded machine `N` with the same input-by-input `ComputesInTime`
relation. Set `α₀ := c.encode N`, so `c.decode α₀ = N` by
`Turing.MachineCode.decode_encode`, and `N.toFinTM` halts on `α₀` with completed
output `[UC c α₀]`. If `UC c α₀ = false`, then `Complexity.UC_eq_false_iff` (read
through `decode_encode`) says `N.toFinTM` also halts on `α₀` with `[true]`, and
`Turing.FinTM.ComputesInTime.output_unique` forces `[false] = [true]` — absurd. If
`UC c α₀ = true`, then `N.toFinTM` halts on `α₀` with `[true]`, so
`UC_eq_false_iff` gives `UC c α₀ = false` — absurd. No step computes `encode` or
`decode`: the code `α₀` is chosen inside the contradiction. -/
theorem UC_not_computable (c : MachineCode) : ¬Computable fun α => [UC c α] := by
  sorry

end Complexity
