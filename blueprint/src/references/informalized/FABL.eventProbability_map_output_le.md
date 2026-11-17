<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.eventProbability_map_output_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapped Output Bad Event Bound

**Claim.** If every mapped output satisfying the target bad predicate comes from an original output satisfying the source bad predicate, then the mapped program’s bad-event probability is at most the original program’s source bad-event probability.

**Proof.** Use the equality for mapped output event probabilities (`eventProbability_map_output_eq`) to express the mapped bad-event probability as the original program’s probability of the pulled-back event, namely that the mapped value satisfies the target predicate. By hypothesis, this event implies that the original value satisfies the source predicate. Monotonicity of event probabilities under event inclusion (`LearningProgram.eventProbability_mono`) then gives the stated inequality.

**Key facts.** `FABL.eventProbability_map_output_eq`, `FABL.LearningProgram.eventProbability_mono`.
