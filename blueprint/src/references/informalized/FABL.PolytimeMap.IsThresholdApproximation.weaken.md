<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PolytimeMap.IsThresholdApproximation.weaken -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weakening Approximation Thresholds

**Claim.** If the output threshold is lowered and the required optimum threshold is raised, a threshold approximation guarantee remains valid.

**Proof.** Fix a valid instance. The original guarantee supplies feasibility and, whenever the optimum reaches the original optimum threshold, the required lower bound on the output value. Feasibility is unchanged. If the optimum reaches the raised threshold, it also reaches the original threshold; the original output lower bound then applies, and the lowered output threshold is no greater than that bound. Thus the weakened guarantee holds.
