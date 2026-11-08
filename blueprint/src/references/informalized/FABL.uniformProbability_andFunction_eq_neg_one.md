<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.uniformProbability_andFunction_eq_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of the all-negative input

**Claim.** For every $w\ge0$, the uniform probability that the AND function on the sign cube outputs $-1$ is $2^{-w}$.

**Proof.** The AND function outputs $-1$ exactly when every input coordinate is $-1$. There is exactly one such vector among the $2^w$ vectors in the sign cube. Its uniform probability is therefore $1/2^w$.
