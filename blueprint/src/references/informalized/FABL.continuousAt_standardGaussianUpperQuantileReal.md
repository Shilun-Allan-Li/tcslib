<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.continuousAt_standardGaussianUpperQuantileReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian Upper Quantile

**Claim.** For every $\alpha\in(0,1)$, the standard Gaussian upper quantile, extended as a real-valued function by the given definition, is continuous at $\alpha$.

**Proof.** The real-valued quantile function is continuous on $(0,1)$ by the stated continuity result (continuousOn_standardGaussianUpperQuantileReal). Since $(0,1)$ is open, the point $\alpha$ has a neighborhood contained in this interval. Restricting the continuous-on statement to that neighborhood gives continuity at $\alpha$.

**Key facts.** `FABL.continuousOn_standardGaussianUpperQuantileReal`.
