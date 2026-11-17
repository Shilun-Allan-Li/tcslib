<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.size_truncateWidth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Under Width Truncation

**Claim.** Retaining only the terms of width at most $w$ gives a formula whose size is at most the size of the original formula.

**Proof.** Width truncation filters the original term list, retaining those terms whose width is at most $w$. A filtered list has length no greater than the list from which it was formed (`List.length_filter_le`). Since formula size is term-list length, the truncated formula’s size is at most the original size.
