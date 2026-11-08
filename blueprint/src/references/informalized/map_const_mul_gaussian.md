<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean :: map_const_mul_gaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling a Gaussian random variable

**Claim.** If the law of a measurable real random variable $X$ is the centered Gaussian with variance parameter $\sigma_0$, then the law of $cX$ is the centered Gaussian with variance parameter $c^2\sigma_0$.

**Proof.** The map sending $\omega$ to $cX(\omega)$ is the composition of $X$ with the scaling map $r\mapsto cr$. The law of a measurable composition is the pushforward of the original law by the outer map. Thus the law of $cX$ is obtained by scaling a centered Gaussian of variance parameter $\sigma_0$. The Gaussian scaling formula (`gaussianReal_map_const_mul`) identifies this pushforward as the centered Gaussian with variance parameter $c^2\sigma_0$.

**Caveat.** The invoked Gaussian scaling formula is not listed in the supplied upstream facts.
