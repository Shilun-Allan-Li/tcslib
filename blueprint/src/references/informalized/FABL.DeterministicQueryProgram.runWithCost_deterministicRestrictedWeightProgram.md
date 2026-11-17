<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.DeterministicQueryProgram.runWithCost_deterministicRestrictedWeightProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Weight Program Output and Cost

**Claim.** Running the deterministic restricted weight program returns the restricted Fourier weight estimate for the target on the chosen coordinates and frequency, together with the prescribed cost.

**Proof.** The program charges its construction work, queries the target at the prescribed finite batch of points, and then charges its local estimation work before returning the estimate computed from the answers. Its query answers are exactly the target values at those points. The identity connecting this answer-based estimate to the restricted Fourier weight (`deterministicRestrictedWeightEstimateFromOracle_eq`) identifies the resulting output with the stated restricted Fourier weight estimate. The program’s explicit charges are the construction charge, the batch query charge, and the local-work charge, which together are the prescribed cost.

**Key facts.** `FABL.deterministicRestrictedWeightEstimateFromOracle_eq`.
