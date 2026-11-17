<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperTail_quantile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Tail at Its Quantile

**Claim.** For every $\alpha\in(0,1)$, the standard Gaussian upper-tail probability at the upper quantile corresponding to $\alpha$ is exactly $\alpha$.

**Proof.** Apply the order isomorphism from the real line to $(0,1)$ and then its inverse to $\alpha$. The inverse-after-map identity says the result is $\alpha$. Taking the real value of this subtype equality, and using that the order isomorphism acts as the standard Gaussian upper-tail function while its inverse defines the upper quantile, yields the asserted identity.

**Key facts.** `FABL.standardGaussianUpperTailOrderIso_apply`.
