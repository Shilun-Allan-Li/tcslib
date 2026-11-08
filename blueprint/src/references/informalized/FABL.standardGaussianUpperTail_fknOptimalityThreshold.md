<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.standardGaussianUpperTail_fknOptimalityThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail at the Optimality Threshold

**Claim.** For every natural number $q$, the standard Gaussian upper-tail probability at the threshold corresponding to Gaussian mass $1/(q+2)$ is exactly $1/(q+2)$.

**Proof.** The upper-tail quantile identity says that the tail evaluated at the quantile associated with any point of $(0,1)$ equals that point (`standardGaussianUpperTail_quantile`). Apply it to the Gaussian mass $1/(q+2)$, which is the point used to define the optimality threshold. Unfolding that threshold gives the asserted equality.

**Key facts.** `FABL.standardGaussianUpperTail_quantile`.
