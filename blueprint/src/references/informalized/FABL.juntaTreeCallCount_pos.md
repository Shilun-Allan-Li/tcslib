<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaTreeCallCount_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive junta tree call count

**Claim.** The junta tree call count is positive at every depth.

**Proof.** At depth zero the count is $1$, which is positive. At a successor depth it is $1$ plus twice the preceding count, and hence is positive. These are exactly the defining cases of the call count.
