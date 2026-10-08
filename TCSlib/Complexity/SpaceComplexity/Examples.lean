/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logspace examples: the parity language

[AB09, Example 4.7]: `EVEN = {x : x has an even number of 1s}` is in `L`. (The
example's second language, `MULT`, needs the campaign's number-triple encoding
conventions and is scheduled with the logspace-reduction phase — phase P4.4 of
`AroraBarakChapters3-4Plan.md` — rather than here.) A worked ARM-compiled
example of a `LOGSPACE` membership already exists in the received surface
(`Complexity.dblLang_mem`, `TCSlib.Complexity.SpaceComplexity.Machines.DblLang`);
parity is the book's own first example and gets the direct statement.

## Main definitions

* `Complexity.evenLang` — the even-parity language. [AB09, Example 4.7]

## Main results (sorried; phase-P4.1 statement)

* `Complexity.evenLang_mem_LOGSPACE` — parity is decidable in logarithmic
  space. [AB09, Example 4.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Example 4.7.)
-/

namespace Complexity

open Turing

/-- **The parity language** `EVEN`: binary strings containing an even number of
`1`s (rendered as `true`s). [AB09, Example 4.7] -/
def evenLang : Language Bool :=
  {x | x.count true % 2 = 0}

/-- **Parity is decidable in logarithmic space** — in fact in constant space,
which the `c · logSpace n` budget absorbs since `logSpace n ≥ 1`.
[AB09, Example 4.7]

**Proof sketch.** A two-state one-work-tape machine scans the input left to
right, keeping the running parity in its control state, never moving its work
head (one visited cell), and at the end-of-input emits `[true]` iff the parity
state is even. Space: `1 ≤ 1 · logSpace n` visited cells; halting at time
`n + O(1)`. The machine is a `Turing.FinTM` built directly (the
`Turing.MultiTapeTM.indicator` output convention of
`Turing.FinTM.DecidesInSpace`); correctness is a single left-to-right scan
invariant — parity of the consumed prefix — in the style of the received
`Complexity.dblLang_mem` but without the ARM layer. -/
theorem evenLang_mem_LOGSPACE : evenLang ∈ LOGSPACE := by
  sorry

end Complexity
