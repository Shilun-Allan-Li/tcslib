<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.inAC_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-Zero Circuit Equivalence

**Claim.** A Boolean language is recognized by a well-formed polynomial-size DAG circuit family of depth bounded by a constant times $(\log_2 n+1)^0$ exactly when it is recognized by a polynomial-size tree-circuit family with the same depth bound.

**Proof.** For the forward implication, apply the depth-zero conversion theorem: any language in the DAG class at depth parameter zero belongs to the corresponding tree class (`Language.InAC.inTreeAC_zero`). For the reverse implication, use the general inclusion of the tree class in the DAG class, which preserves the depth parameter and therefore applies at zero (`Language.InTreeAC.inAC`). Together these give the equivalence.

**Key facts.** `Language.InAC.inTreeAC_zero`, `Language.InTreeAC.inAC`.
