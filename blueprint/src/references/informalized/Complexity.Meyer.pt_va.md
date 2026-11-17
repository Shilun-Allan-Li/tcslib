<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_va -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Nested Projection

**Claim.** The function that takes the total second projection of a bit string, then its total first projection, then its total second projection is polynomial-time computable.

**Proof.** Each total projection is polynomial-time computable: the first projection has this property (`polyTimeComputable_pairFstD`), as does the second (`polyTimeComputable_pairSndD`). Polynomial-time computability is preserved under composition (`PolyTimeComputable.comp`). Applying that closure first to the second projection after the first, and then to the resulting function after the second projection, gives the stated nested function. The total projections return the empty word when parsing fails, as in their definitions.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.
