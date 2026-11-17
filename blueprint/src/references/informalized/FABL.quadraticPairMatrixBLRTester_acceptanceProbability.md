<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticPairMatrixBLRTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix Tester Acceptance Probability

**Claim.** For any functions ℓ on binary vectors and q on binary matrices, the matrix tester has the same acceptance probability as the BLR tester on the function that applies q to the reshaped input.

**Proof.** Expand both acceptance probabilities as expectations over their seed pairs. In each tester, the seeds are independent uniform elements of the same space of binary words of length n². For each seed pair, the matrix tester queries the reshaped first seed, reshaped second seed, and reshaped sum; the other tester applies q to those same reshaped words. Reshaping preserves addition, so the three answers agree pointwise, and both testers accept exactly when the first two answers sum to the third. Thus the summands in the two expectations agree for every seed pair, giving equal acceptance probabilities.
