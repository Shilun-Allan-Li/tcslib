/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multiplication in logarithmic space

[AB09, Example 4.7], second language: `MULT = {⟨n, m, nm⟩}` is in `L` by the
grade-school method. Deferred from phase P4.1 to P4.4
(`AroraBarakChapters3-4Plan.md`) for the number-triple encoding conventions,
which the logspace phase fixes: binary components in nested aligned pairs,
little-endian (`Nat.bits`), membership by existential witness over genuine
encodings — the same pattern as `Complexity.PATH`'s instance encoding.

## Main definitions

* `Complexity.multLang` — the triples `⟨a, b, a·b⟩`. [AB09, Example 4.7]

## Main results (sorried; phase-P4.4 statement)

* `Complexity.multLang_mem_LOGSPACE` — grade-school multiplication runs in
  logarithmic space. [AB09, Example 4.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Example 4.7.)
-/

namespace Complexity

open Turing

/-- **The language `MULT`** [AB09, Example 4.7]: encodings of triples
`⟨a, b, a·b⟩`, components in little-endian binary, nested aligned pairs.
Strings encoding no such triple are not members. -/
def multLang : Language Bool :=
  {z | ∃ a b : ℕ,
    z = pairEncode (Nat.bits a) (pairEncode (Nat.bits b) (Nat.bits (a * b)))}

/-- **Multiplication verifies in logarithmic space** ([AB09, Example 4.7];
spec, fill pending — phase P4.4): the grade-school method checks the third
component bit by bit with carry and index counters only.

**Proof sketch.** The verifier computes each bit of `a · b` on demand:
bit `j` of the product is determined by the column sums
`∑_{p+q=j'} a_p · b_q` for `j' ≤ j` propagated through the carry — maintain
the carry (of `O(logSpace n)` bits, since a column sum is at most the input
length) and two index counters, re-reading `a`'s and `b`'s bits from the
input by position arithmetic on the nested pair layout (through `whole`-mode
calls to the input-access languages `Complexity.inputBitLang` and
`Complexity.inputLenLang` of phase P4.4b; the received
`Machines/Parse2`/`ParseCmp` toolkit reads only unary-first inputs
`⟨1ⁿ, ⟨u, w⟩⟩` and does not apply); compare each computed bit against the
third component's bit and reject on mismatch or malformed shape; accept when
every column through `|a| + |b|` matches (missing result bits read as `0`, a
longer result field rejected) and no carry remains. Registers: carry, two
indices, a column cursor — `O(logSpace n)` cells; assembled by the received
`arm_decides_poly`. Fill obligations, named: the column-sum/carry invariant;
the position arithmetic into the nested pairs; the shape validator; the
`DecidesInSpace` packaging. (Sketch prose corrected at phase P4.4b; the
statement is unchanged.) -/
theorem multLang_mem_LOGSPACE : multLang ∈ LOGSPACE := by
  sorry

end Complexity
