<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.affineCoordinateCorrectionProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correction Probability Is At Most One

**Claim.** For every sign-valued function on $(\mathbb{F}_2)^n$, coordinate $i$, and Boolean value $b$, the probability that local correction in coordinate $i$ agrees with the sign encoded by $b$ is at most $1$.

**Proof.** The probability is the uniform expectation of an indicator: at each input the integrand is either $0$ or $1$, hence is at most the constant function $1$. Taking expectations preserves this pointwise inequality, and the uniform expectation of the constant function $1$ is $1$.
