<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.addressRecursiveMajorityThreeTopCoeff_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Majority Top Coefficient

**Claim.** The top coefficient of the depth-zero recursively composed three-input majority function is $1$.

**Proof.** At depth zero there is a single input sign, so the top correlation is the uniform average of the square of that sign. Re-index the average over functions on the singleton address set as an average over the two possible signs. Each sign has square $1$, and hence their average is $1$.
