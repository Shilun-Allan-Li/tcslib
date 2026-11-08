<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.runWithCost_restrictedFourierWeightObservationBatchProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Observation Batch

**Claim.** For fixed input sequences, the observation batch program returns its prescribed list of restricted Fourier observations with probability one, at cost $(0,2m,m(2+2n+2|S|+1))$.

**Proof.** The result follows by specializing the theorem for the batch program with an arbitrary continuation to the pure continuation that returns the accumulated list (`runWithCost_restrictedFourierWeightObservationBatchProgramWith_pure`). Under this specialization, the auxiliary output list is exactly the observation batch output, and the batch cost is the stated cost.

**Key facts.** `FABL.runWithCost_restrictedFourierWeightObservationBatchProgramWith_pure`.
