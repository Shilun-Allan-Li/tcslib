<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.lowDegreeFourierEstimatorProgram_of_monotone_deterministicDepth_failure_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning monotone functions of bounded depth

**Claim.** For a monotone Boolean function whose deterministic decision-tree depth is at most $k$, the low-degree Fourier estimator at the monotone decision-tree learning degree has failure probability at most $1/10$.

**Proof.** A theorem for monotone Boolean functions bounds total influence by the square root of their deterministic decision-tree depth. Since the depth is at most $k$, the target’s total influence is at most $\sqrt{k}$. Apply the estimator guarantee for functions with total influence at most $t$, taking $t=\sqrt{k}$. Its degree parameter is the total-influence learning degree at this value, which is exactly the monotone decision-tree learning degree by definition. The resulting failure probability is at most $1/10$.

**Key facts.** `FABL.totalInfluence_le_sqrt_deterministicDepth_of_monotone`, `FABL.lowDegreeFourierEstimatorProgram_of_totalInfluence_failure_le_one_tenth`.
