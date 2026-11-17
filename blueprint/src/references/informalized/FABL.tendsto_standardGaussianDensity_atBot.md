<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.tendsto_standardGaussianDensity_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density at Negative Infinity

**Claim.** The standard Gaussian density on $\mathbb R$ tends to $0$ as its argument tends to $-\infty$.

**Proof.** As $t\to-\infty$, $-t\to+\infty$, so the standard Gaussian density evaluated at $-t$ tends to $0$ (`FABL.tendsto_standardGaussianDensity_atTop`). The standard Gaussian density is even, meaning its value at $-t$ equals its value at $t$ (`FABL.standardGaussianDensity_neg`). Replacing the argument by its negative therefore identifies this limit with the density's limit as its argument tends to $-\infty$, as required.

**Key facts.** `FABL.tendsto_standardGaussianDensity_atTop`, `FABL.standardGaussianDensity_neg`.
