<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_vj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Nested Projection

**Claim.** The function that takes the total second projection twice and then the total first projection is polynomial-time computable.

**Proof.** The total second projection and the total first projection are each polynomial-time computable (`polyTimeComputable_pairSndD` and `polyTimeComputable_pairFstD`). Polynomial-time computability is closed under composition (`PolyTimeComputable.comp`). Compose the second projection with itself, then compose the first projection with that result. This is the stated function, including the empty-word outputs when a pair parse fails.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`.
