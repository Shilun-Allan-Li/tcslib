<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_vt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Nested Projection

**Claim.** Taking the total second projection, followed by the total first projection twice, defines a polynomial-time computable function.

**Proof.** The total second and total first projections are polynomial-time computable (`polyTimeComputable_pairSndD` and `polyTimeComputable_pairFstD`). Closure under composition (`PolyTimeComputable.comp`) first combines the first projection after the second, and then combines another first projection after that result. This gives the claimed order of operations; failed parses return the empty word by the definitions of the total projections.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.
