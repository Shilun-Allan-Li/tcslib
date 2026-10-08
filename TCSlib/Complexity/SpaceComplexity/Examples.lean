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

**Proof sketch.** A direct `Turing.FinTM` with the running parity in control:
either the two-state **zero-work-tape** scanner (space `0`, the round-2 P0
witness construction — `Complexity.exists_zeroTape_parity_decider` in
`SpaceComplexity/ZeroSpace.lean` states exactly this machine, and that file
imports this one, so this proof must be **direct rather than derived from it**:
the reverse dependency would be an import cycle, P4.1 round 1, finding 4) or
the one-work-tape variant (one visited cell); either is within
`1 ≤ 1 · logSpace n`. Correctness is the left-to-right scan invariant —
parity of the consumed prefix — with the final emission
`[Turing.MultiTapeTM.indicator evenLang x]` at the input boundary, halting at
time `n + O(1)`. -/
theorem evenLang_mem_LOGSPACE : evenLang ∈ LOGSPACE := by
  sorry

end Complexity
