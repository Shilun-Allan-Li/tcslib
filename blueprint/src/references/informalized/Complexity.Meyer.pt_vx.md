<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_vx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Repeated First Projection

**Claim.** Applying the total first projection of the pair encoding twice defines a polynomial-time computable function on bit strings.

**Proof.** The total first projection is polynomial-time computable (`polyTimeComputable_pairFstD`). Polynomial-time computability is closed under composition (`PolyTimeComputable.comp`), so composing this projection with itself proves the claim. If either parse fails, the total projection supplies the empty word as specified by its definition.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.
