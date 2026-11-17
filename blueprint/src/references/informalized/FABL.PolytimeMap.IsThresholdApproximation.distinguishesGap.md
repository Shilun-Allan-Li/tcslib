<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PolytimeMap.IsThresholdApproximation.distinguishesGap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinguishing a Gap Promise

**Claim.** An $(\alpha,\beta)$-threshold approximation algorithm, together with the exact test of whether its output value reaches the output threshold, distinguishes instances whose optimum is at least the completeness threshold from those whose optimum is at most the soundness threshold.

**Proof.** For a promised YES instance, the instance is well formed and its optimum is at least the completeness threshold. Since the optimum threshold is at most the completeness threshold, the approximation guarantee applies and the algorithm's value is at least the output threshold. The value-threshold test therefore answers YES. For a promised NO instance, the instance is again well formed. The algorithm outputs a feasible solution, whose value is at most the optimum by the defining feasibility bound. The optimum is at most the soundness threshold, which is strictly below the output threshold; hence the solution's value is strictly below that threshold, and the test answers NO.
