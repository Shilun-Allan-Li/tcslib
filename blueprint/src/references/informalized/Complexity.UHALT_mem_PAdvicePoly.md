<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.UHALT_mem_PAdvicePoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Halting with Polynomial Advice

**Claim.** For every machine representation scheme $c$, the unary language of numbers whose binary expansions begin with $1s$, where $s$ encodes an advice string and an input on which the machine decoded from that advice halts, belongs to polynomial-time with polynomial-length advice.

**Proof.** First, `UHALT_le_allOnes` establishes that every word in this language consists entirely of ones. The general theorem `mem_PAdvicePoly_of_le_allOnes` then shows that any language contained in the all-ones language has polynomial-time decision with polynomial-length advice. Applying it to this inclusion gives the result.

**Key facts.** `Complexity.UHALT_le_allOnes`, `Complexity.mem_PAdvicePoly_of_le_allOnes`.
