<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.standardGaussianUpperTail_eq_integral_Ioi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail as a Density Integral

**Claim.** For every real number $t$, the standard Gaussian upper-tail probability at $t$ equals the integral of the standard Gaussian density over $(t,\infty)$.

**Proof.** First express the upper-tail probability as the real-valued Gaussian measure of $(t,\infty)$, by the tail-measure identity (`standardGaussianUpperTail_eq_measureReal_Ioi`). The Gaussian measure of this set is given by integrating its density over the set. Passing from the extended-real integral to the real integral is valid because the density is nonnegative, so the integral is nonnegative and the extended-real-to-real conversion applies.

**Key facts.** `FABL.standardGaussianUpperTail_eq_measureReal_Ioi`.
