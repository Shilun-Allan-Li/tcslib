<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples_uniformMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform matrix estimator law

**Claim.** The queried finite-family estimator with samples has the law of a uniformly random family-indexed matrix of cube inputs mapped to the estimator output and its specified cost.

**Proof.** The preceding run-law theorem expresses the program’s law as the uniform law on input sequences, mapped to the queried estimator output and cost. The map of a uniform sequence law under the finite-family indexing equivalence is the uniform law on family-indexed matrices (map of uniform law under finiteFamilyLinearToMatrixEquiv). Applying the output-and-cost map to both sides preserves equality of laws. The reshaped estimator output agrees with the finite-family output by unfolding the definition of the queried output, so the resulting law is the one claimed.

**Key facts.** `FABL.map_uniformPMF_finiteFamilyLinearToMatrixEquiv`, `FABL.runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples`.
