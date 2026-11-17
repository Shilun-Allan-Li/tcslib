<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaTreeCallCount_mul_perCallFailure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta tree failure allocation

**Claim.** The junta tree call count multiplied by the per-call failure parameter equals the total failure parameter.

**Proof.** The call count is positive (`juntaTreeCallCount_pos`), so it is nonzero as a rational number. By the definition of the per-call parameter (`juntaTreePerCallFailure_value`), it is the total failure parameter divided by the call count. Multiplying by the call count cancels this nonzero denominator and gives the total failure parameter.

**Key facts.** `FABL.juntaTreeCallCount_pos`, `FABL.juntaTreePerCallFailure_value`.
