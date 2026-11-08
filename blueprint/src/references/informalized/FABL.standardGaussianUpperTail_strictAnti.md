<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperTail_strictAnti -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Decrease of the Gaussian Upper Tail

**Claim.** The standard Gaussian upper-tail probability is strictly decreasing as a function of the real threshold.

**Proof.** Take $x<y$. The standard Gaussian CDF is strictly increasing, so its value at $x$ is strictly less than its value at $y$. The upper-tail probabilities are obtained by subtracting these CDF values from $1$, which reverses the strict inequality. Thus the upper tail at $x$ is strictly greater than at $y$.

**Key facts.** `FABL.strictMono_standardGaussianCDF`.
