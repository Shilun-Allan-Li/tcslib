<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlationKeepProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for the keep probability

**Claim.** For every real number $\rho\in[-1,1]$, the probability $(1+\rho)/2$ is at most $1$.

**Proof.** The upper endpoint condition gives $\rho\le 1$. Hence $1+\rho\le 2$, and dividing by the positive number $2$ yields $(1+\rho)/2\le 1$. This is the corresponding inequality for the real value underlying the keep probability, and therefore also holds for that value viewed as a nonnegative real.
