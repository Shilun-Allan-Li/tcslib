<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperTail_lt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Upper Tail Below One

**Claim.** For every real number $t$, the standard Gaussian upper-tail probability at $t$ is strictly less than $1$.

**Proof.** The standard Gaussian cumulative distribution function is strictly increasing (`strictMono_standardGaussianCDF`). In particular, its value at $t$ is strictly greater than its value at $t-1$. The CDF is nonnegative, so its value at $t$ is strictly positive. Since the upper tail is one minus this CDF value, it is strictly less than $1$.

**Key facts.** `FABL.strictMono_standardGaussianCDF`.
