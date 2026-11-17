<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.continuous_standardGaussianUpperQuantile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian upper quantile

**Claim.** For each probability level $\alpha\in(0,1)$, let $q(\alpha)$ be the unique real number whose standard Gaussian upper-tail probability is $\alpha$. The function $q:(0,1)\to\mathbb{R}$ is continuous.

**Proof.** The upper quantile is the inverse of the order isomorphism from the real line to $(0,1)$ given by the standard Gaussian upper-tail function. An order isomorphism and its inverse are continuous in the order topologies; identifying the order topology on the real line with its usual topology gives the claimed continuity.
