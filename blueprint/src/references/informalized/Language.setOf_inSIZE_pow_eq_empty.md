<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: Language.setOf_inSIZE_pow_eq_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-size language set is empty

**Claim.** No language of Boolean lists is recognized by a family of fan-in-two acyclic Boolean circuits whose size is bounded by \(n^c\) for every input length, for any natural number \(c\).

**Proof.** Extensionality reduces the claimed equality of sets of languages to showing that no language belongs to the displayed set. If a language belonged, there would be an exponent \(c\) for which it had the specified polynomial-size circuit family. The theorem that no Boolean-list language has such a circuit family for any exponent (`Language.not_inSIZE_pow`) rules this out. Hence the set is empty.

**Key facts.** `Language.not_inSIZE_pow`.
