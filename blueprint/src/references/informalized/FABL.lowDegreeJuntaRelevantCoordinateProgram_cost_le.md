<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaRelevantCoordinateProgram_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relevant-Coordinate Program Cost

**Claim.** Every outcome in the support of the relevant-coordinate program uses at most the uniform bound on random examples, makes no membership queries, and uses at most the uniform work bound.

**Proof.** Let $M$ be the restricted sample count. The program first runs the restriction sampler and then runs its continuation on the sampler’s outcome. The cost law for a bind decomposes a supported outcome into a supported sampler outcome and a supported continuation outcome, with their costs added (`LearningProgram.runWithCost_bind`). Every sampler outcome has exactly the specified number of random examples, zero queries, and work equal to that sample count plus the restriction-sampling work (`juntaRestrictionSampleProgram_cost_eq`). If sampling returns no matched batch, the continuation is pure, so it adds no cost. If it returns a batch, the continuation charges the node-analysis work for the projected batch; this is bounded by the uniform node-analysis bound (`lowDegreeJuntaNodeAnalysisWork_le`). In either case, the random-example count and work are bounded by the corresponding bounds for this particular $P$, and those are at most the supremum over all coordinate sets, by the definition of the uniform bounds. Queries remain zero throughout.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.juntaRestrictionSampleProgram_cost_eq`, `FABL.lowDegreeJuntaNodeAnalysisWork_le`.
