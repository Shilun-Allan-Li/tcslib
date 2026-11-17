<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperQuantile_upperTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper quantile inverts the Gaussian tail

**Claim.** For every real $t$, the standard Gaussian upper quantile evaluated at the standard Gaussian upper-tail probability of $t$ equals $t$.

**Proof.** The upper-tail probability of $t$ lies in $(0,1)$, so it defines a valid input to the quantile. By the definition of the tail map into this interval, that input is exactly the image of $t$ under the order isomorphism from the order dual of the reals to $(0,1)$. The quantile is the inverse of this isomorphism, so applying it recovers $t$.

**Key facts.** `FABL.standardGaussianUpperTail_pos`, `FABL.standardGaussianUpperTail_lt_one`.
