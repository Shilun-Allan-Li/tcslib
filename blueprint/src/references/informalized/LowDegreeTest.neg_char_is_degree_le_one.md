<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.neg_char_is_degree_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negated characters have degree one

**Claim.** For every subset $S$, the negated Walsh character $-\chi_S$ has degree at most one.

**Proof.** The Walsh character itself has degree at most one (`LowDegreeTest.char_is_degree_le_one`). The order-two Gowers product of its negative is unchanged: the two vertex values each acquire a factor of $-1$, and their product cancels those signs. Hence the negated character also satisfies the defining degree-one condition.

**Key facts.** `LowDegreeTest.char_is_degree_le_one`.
