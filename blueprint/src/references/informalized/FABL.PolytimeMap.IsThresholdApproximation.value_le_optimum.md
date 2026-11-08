<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PolytimeMap.IsThresholdApproximation.value_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Feasible Value Is Bounded by the Optimum

**Claim.** On every valid instance, the value of the solution output by a threshold approximation algorithm is at most the instance's optimum.

**Proof.** Fix a valid instance. The approximation guarantee includes that the algorithm's output on this instance is feasible. By the defining upper-bound property of the encoded maximization problem, every feasible solution has value at most the stated optimum. Applying this property to the algorithm's output proves the claim.
