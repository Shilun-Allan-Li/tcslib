<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.map_uniformPMF_rawProjectedJuntaRestrictionBatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distribution of Raw Projected Restrictions

**Claim.** The distribution of the raw projected restriction batch from a uniform batch of full sign vectors equals the distribution obtained by independently sampling uniform fixed-coordinate and free-coordinate batches, combining their entries, and applying the same projection.

**Proof.** Split each full sign vector in the batch into its fixed-coordinate and free-coordinate parts. This is a bijective change of representation, so the batch remains uniform (`map_uniformPMF_equiv`). A uniform batch of pairs has the same law as first choosing a uniform fixed-coordinate batch and then, independently, a uniform free-coordinate batch (`uniformPMF_bind_map_pair`). Finally, splitting and recombining are inverse operations, so applying the raw projection after recombination gives exactly the same output as applying it to the original batch. The resulting laws therefore agree.

**Key facts.** `FABL.map_uniformPMF_equiv`, `FABL.uniformPMF_bind_map_pair`.
