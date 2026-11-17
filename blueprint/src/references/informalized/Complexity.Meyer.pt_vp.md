<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_vp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Repeated Projection

**Claim.** Taking the total second projection of a bit string three times, with a failed pair parse producing the empty word at that stage, defines a polynomial-time computable function.

**Proof.** The total second projection is polynomial-time computable (`polyTimeComputable_pairSndD`). Polynomial-time computability is preserved by composition (`PolyTimeComputable.comp`). Composing this projection with itself gives two applications, and composing it once more gives the three applications in the claim. The total projection already returns the empty word when parsing fails.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`.
