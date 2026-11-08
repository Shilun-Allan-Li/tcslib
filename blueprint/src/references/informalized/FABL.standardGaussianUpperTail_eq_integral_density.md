<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianMillsRatio.lean :: FABL.standardGaussianUpperTail_eq_integral_density -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail Density Integral Identity

**Claim.** For every real number $t$, the standard Gaussian upper-tail probability at $t$ equals the integral of the standard Gaussian density over $(t,\infty)$.

**Proof.** Rewrite the tail as the real-valued Gaussian measure of $(t,\infty)$ using the tail-measure identity (`standardGaussianUpperTail_eq_measureReal_Ioi`). The Gaussian measure of this set is its density integral. Since the Gaussian density is nonnegative, that integral is nonnegative, which justifies converting the extended-real integral to the stated real-valued integral.

**Key facts.** `FABL.standardGaussianUpperTail_eq_measureReal_Ioi`.
