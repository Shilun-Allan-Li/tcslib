<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.unary_inLayeredPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary languages have polynomial layered size

**Claim.** For every set \(S\subseteq\mathbb N\), the language of all-true Boolean lists whose lengths lie in \(S\) has finite layered circuits using only identity, NOT, and unbounded-fan-in AND gates, with polynomial size.

**Proof.** Every string in the unary language determined by \(S\) is, by definition, an all-true string. Thus this language is contained in the all-ones language (`Language.unary_le_allOnes`). The theorem that every language contained in the all-ones language has polynomial-size layered circuits (`Language.inLayeredPPoly_of_le_allOnes`) now gives the required family and polynomial bound.

**Key facts.** `Language.unary_le_allOnes`, `Language.inLayeredPPoly_of_le_allOnes`.
