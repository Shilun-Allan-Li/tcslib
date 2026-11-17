<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Fourier-Estimator Cost

**Claim.** Every outcome in the support of the confidence-parameter finite-family Fourier estimator’s run-with-cost distribution has cost $(0,|\mathcal F|m,|\mathcal F|mn+|\mathcal F|m+|\mathcal F|m(n+1))$, where $m$ is its prescribed sample count per family member.

**Proof.** Unfold the confidence-parameter program to see that it is the samples-based program with the prescribed sample count. The run-with-cost formula for that program expresses its distribution as the uniform input-batch law mapped to pairs consisting of an output and the estimator’s fixed cost (`runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples`). Membership of an outcome in the support of this mapped distribution implies that it is the image of some sample input. Its cost component is therefore exactly the fixed cost in that image. Substituting the definition of the estimator’s cost gives the three stated coordinates.

**Key facts.** `FABL.runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples`.
