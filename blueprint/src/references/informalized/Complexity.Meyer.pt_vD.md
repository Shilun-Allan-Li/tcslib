<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_vD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marker removal

**Claim.** The function that takes the second component of the total first projection of $z$, applies the total second projection, and then removes the marker by the specified left-to-right process is polynomial-time computable.

**Proof.** The total first projection and total second projection are polynomial-time computable (Complexity.polyTimeComputable_pairFstD and Complexity.polyTimeComputable_pairSndD). Their composition therefore computes the nested parsing step in polynomial time. The marker-removal transduction is also polynomial-time computable (Complexity.KarpLipton.polyTimeComputable_dropMarker); composing it with the two projections, using closure under composition (Complexity.PolyTimeComputable.comp), proves the claim.

**Key facts.** `Complexity.KarpLipton.polyTimeComputable_dropMarker`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_pairFstD`.
