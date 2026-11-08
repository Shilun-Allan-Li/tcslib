<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.juntaRestriction_empty_juntaFreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction with no fixed coordinates

**Claim.** When the fixed coordinate set is empty, the restriction evaluated at the free-coordinate part of a cube point equals the original function at that point.

**Proof.** Because there are no fixed coordinates, every point vacuously agrees with the fixed assignment. The recombination lemma for a point matching the fixed assignment (`combineJuntaAssignment_freePart_of_matches`) says that recombining its free-coordinate part with the fixed assignment recovers the original point. The restriction is the target evaluated at this recombined point, hence equals the target at the original point.

**Key facts.** `FABL.combineJuntaAssignment_freePart_of_matches`.
