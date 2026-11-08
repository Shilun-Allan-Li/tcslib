<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.restrictedFourierWeightEstimatorProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator Program Cost

**Claim.** Every outcome in the support of the estimator program's cost distribution has cost component equal to the restricted Fourier weight estimator cost.

**Proof.** The program's cost distribution is a sequence of three uniform-input batches, followed by a point mass whose output is the estimator output and whose cost is the restricted Fourier weight estimator cost (FABL.runWithCost_restrictedFourierWeightEstimatorProgram). Membership in the support of each bind forces the corresponding batch input to have positive probability and reduces support membership to the next stage. After removing all three batches, support membership in the point mass forces the outcome to equal that point. Its cost component is therefore exactly the stated estimator cost.

**Key facts.** `FABL.runWithCost_restrictedFourierWeightEstimatorProgram`.
