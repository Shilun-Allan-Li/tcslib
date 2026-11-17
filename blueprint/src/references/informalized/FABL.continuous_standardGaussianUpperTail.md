<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.continuous_standardGaussianUpperTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian upper tail

**Claim.** The standard Gaussian upper-tail function, which assigns to each real number $t$ the probability that a standard Gaussian random variable exceeds $t$, is continuous on $\mathbb{R}$.

**Proof.** The upper-tail function is $1$ minus the standard Gaussian cumulative distribution function. The latter is continuous, so subtracting it from the constant function $1$ preserves continuity.

**Key facts.** `FABL.continuous_standardGaussianCDF`.
