/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.Uncomputability.Halting

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A function that is not time-constructible

[AB09, Exercise 3.5]: not every function is time-constructible. Stated
non-trivially: `Complexity.TimeConstructible` already packages the growth
condition `∀ n, n ≤ T n`, so a function violating that (`T = 0`, say) fails
for a vacuous reason; the statement below therefore demands a function
*dominating the identity* that still fails constructibility, pinning the
failure on the computability half — a constructibility witness for the
exhibited `T` would decide the halting problem.

## Design

* The witness oscillates between `n` and `n + 1` according to the halting
  function `Complexity.HALT` at the campaign's fixed effective scheme
  `Complexity.TimeHierarchy.code` (reused, not re-chosen), evaluated on the
  `n`-th binary string in the length-lexicographic (dyadic) order. The
  definition is classical and noncomputable — legitimate, since it lives
  inside an existence proof.
* The refutation uses only the *computability* of a constructibility witness
  (a machine computing `(T |x|).bits` on every input), not its time bound:
  `Complexity.Computable` carries no clock, so even the exponentially long
  intermediate strings of the reduction are harmless.

## Main results (sorried; phase-P3.2 statement)

* `Complexity.exists_not_timeConstructible` — some `T` with `∀ n, n ≤ T n` is
  not time-constructible. [AB09, Exercise 3.5]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Chapter 3, Exercise 3.5; §1.5.1,
  Theorem 1.11.)
-/

namespace Complexity

open Turing

/-- **Not every function is time-constructible** [AB09, Exercise 3.5]: there
is a function `T` dominating the identity (`∀ n, n ≤ T n` — so the failure is
not the vacuous growth-condition one, see the module docstring) that is not
time-constructible.

**Proof sketch.** Fix the campaign's effective scheme
`c := Complexity.TimeHierarchy.code` and the length-lexicographic (dyadic)
enumeration `str : ℕ → List Bool` of binary strings — the rank of a string
`s` is the value of `s` with a `1` prepended, read in binary, minus one, so
rank and un-rank are both bit-rewrites. Define, classically,

  `T n := n + (if HALT c.toMachineCode (str n) = true then 1 else 0)`.

Then `∀ n, n ≤ T n` by construction. Suppose `TimeConstructible T` held, with
witness machine `M` computing `(T |x|).bits` on every input `x` (the clock
`c₀ · (T n + 1)` of `Complexity.TimeConstructible` is not even needed — only
the witness's totality). Then `fun s => [HALT c.toMachineCode s]` would be
computable, contradicting `Complexity.HALT_not_computable c`: on input `s`,
(i) compute the rank word `(rank s).bits` (the dyadic bit-rewrite — the
string-of-index bridge obligation); (ii) emit a string of length `rank s`,
say `1^(rank s)`, by a binary-countdown unary emitter (the
`TimeHierarchy.ClockMachine`/`ClockLoop` counter precedent;
`Complexity.Computable` has no time bound, so the exponential length is
harmless); (iii) run `M` on it, producing `(T (rank s)).bits`; (iv) compare
that word against `(rank s).bits` (equality-test tail,
`Turing.FinTM.computesFunInTime_ifEq` precedent — for an even rank this is
[AB09]'s "read the low bit of `(T n).bits`", and the full equality test also
covers the odd-rank carry), outputting `[true]` exactly when the two differ,
i.e. when `T (rank s) = rank s + 1`, i.e. when `HALT c.toMachineCode s =
true`. Assemble the stages with `Turing.FinTM.exists_comp_partial`, collapsing
intermediate outputs by determinism (`Turing.FinTM.ComputesInTime.output_unique`),
exactly as in `Complexity.UC_computable_of_HALT_computable`. Fill obligations,
named for the brief: the rank machine and the unary emitter (i)-(ii); the
comparison tail (iv); the composition assembly; and the final classical case
split on `HALT` identifying the composite's output with the halting bit. -/
theorem exists_not_timeConstructible :
    ∃ T : ℕ → ℕ, (∀ n, n ≤ T n) ∧ ¬TimeConstructible T := by
  sorry

end Complexity
