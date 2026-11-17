<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.eventProbability_map_output_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapped Output Event Probability

**Claim.** Applying a map to a learning program’s output preserves the probability of an event when the mapped event is tested by pulling its predicate back along that map.

**Proof.** The law of the mapped program’s output and cost is the image, under the map that changes the output and leaves the cost unchanged, of the original law (`LearningProgram.runWithCost_map`). The probability of an event under an image measure is the probability of its inverse image (`PMF.toOuterMeasure_map_apply`). The inverse-image event is precisely that the original output satisfies the predicate after applying the output map, proving the equality.

**Key facts.** `FABL.LearningProgram.runWithCost_map`.
