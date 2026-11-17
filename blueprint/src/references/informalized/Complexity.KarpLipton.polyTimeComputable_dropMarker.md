<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.polyTimeComputable_dropMarker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of Marker Dropping

**Claim.** The marker-dropping function is polynomial-time computable.

**Proof.** The marker-dropping function is the transduction specified by the two-state transition and output rules, started in state $0$. The general theorem that any such finite-state transduction is polynomial-time computable (`polyTimeComputable_transduce`) applies directly, with these transition and output functions and initial state.

**Key facts.** `Complexity.polyTimeComputable_transduce`.
