<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: hasSubgaussianMGF_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling a Sub-Gaussian Variable

**Claim.** If $X$ has a sub-Gaussian moment-generating function with variance proxy $\sigma$, then for every real $c$, the variable $cX$ has one with variance proxy $c^2\sigma$.

**Proof.** For each parameter $t$, the exponential moment of $cX$ at $t$ is the exponential moment of $X$ at $tc$, since $t(cX)=(tc)X$. Its integrability therefore follows from the assumed integrability for $X$. The assumed moment-generating-function bound at parameter $tc$ is $\exp((tc)^2\sigma/2)$, which equals $\exp(t^2(c^2\sigma)/2)$. This is the required bound.
