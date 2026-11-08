<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.scheduledFourierCoeffEstimatorProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduled Fourier Estimator Cost

**Claim.** Every outcome in the support of the scheduled Fourier coefficient estimator has cost $(m,0,m+m(|S|+1))$, where $m$ is its scheduled sample count.

**Proof.** The run law for the scheduled estimator expresses its output distribution as the image of a uniform sample batch, with the cost component fixed at $(m,0,m+m(|S|+1))$ (`FABL.runWithCost_scheduledFourierCoeffEstimatorProgram`). Membership of the given outcome in the support of this image distribution implies that it is the image of some sample batch (`PMF.mem_support_map_iff`). Substituting that witness into the run-law expression shows that its cost component is the stated fixed value.

**Key facts.** `FABL.runWithCost_scheduledFourierCoeffEstimatorProgram`.
