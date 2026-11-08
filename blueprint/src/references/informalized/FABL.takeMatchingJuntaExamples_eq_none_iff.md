<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.takeMatchingJuntaExamples_eq_none_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When matching examples are unavailable

**Claim.** The procedure returns no selection exactly when fewer than $M$ examples match the prescribed assignment on all coordinates in $P$.

**Proof.** By definition, the procedure returns a selection when the match count is at least $M$, and returns none otherwise. In the first case, the left side is not none, while the right side is false. In the second case, the left side is none and the match count is less than $M$. These two cases establish the equivalence.
