<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.replicate_numOfString_mem_UHALT_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Encoding of Halting

**Claim.** The unary word whose length is the integer encoded by a leading $1$ followed by $s$ belongs to the unary halting language exactly when the halting predicate on $s$ is true.

**Proof.** Membership of a replicated all-ones word in a unary language is equivalent to its length belonging to the language's defining set (`Language.replicate_mem_unary_iff`). Here that length is `numOfString s`. By the binary-expansion identity, the binary expansion of this integer is exactly $true::s$ (`Complexity.binaryExpansion_numOfString`). Thus membership reduces to the existence of a string $s'$ with that same leading-bit expansion and with the halting predicate true on $s'$. Equality of the tails forces $s'=s$, proving the forward implication. For the reverse implication, choose $s'=s$; the expansion identity gives the required witness directly.

**Key facts.** `Language.replicate_mem_unary_iff`, `Complexity.binaryExpansion_numOfString`.
