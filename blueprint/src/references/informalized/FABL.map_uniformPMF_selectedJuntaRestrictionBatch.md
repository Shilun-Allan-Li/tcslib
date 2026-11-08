<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.map_uniformPMF_selectedJuntaRestrictionBatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distribution of Selected Restrictions

**Claim.** For any fixed batch of assignments on $P$ with at least $M$ entries equal to $z$, selecting $M$ matching entries in the specified order and forming their labeled restrictions from a uniform free-coordinate batch yields the same distribution as labeling a uniform batch of $M$ free-coordinate assignments.

**Proof.** Let $e$ be the specified injection from the $M$ selected positions into the original $R$ positions. The selected free-coordinate batch is precisely the original batch evaluated at those positions. Thus the map that first projects along $e$ and then labels each assignment by its restriction is the same as the map that selects and labels directly. Projection of a uniform function-valued batch along an injection is uniform (`map_uniformPMF_injection_projection`); applying the labeling map to both sides preserves equality of distributions. This proves the claim.

**Key facts.** `FABL.map_uniformPMF_injection_projection`.
