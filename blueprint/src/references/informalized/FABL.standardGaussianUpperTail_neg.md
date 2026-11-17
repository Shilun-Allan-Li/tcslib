<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperTail_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Upper-Tail Symmetry

**Claim.** For every real number $t$, the standard Gaussian upper-tail probability at $-t$ equals one minus the standard Gaussian upper-tail probability at $t$.

**Proof.** By definition, the upper tail at $-t$ is one minus the Gaussian CDF at $-t$. The symmetry identity for the standard Gaussian CDF identifies that CDF value with the upper-tail probability at $t$ (`standardGaussianCDF_neg`). Substituting gives the desired equality.

**Key facts.** `FABL.standardGaussianCDF_neg`.
