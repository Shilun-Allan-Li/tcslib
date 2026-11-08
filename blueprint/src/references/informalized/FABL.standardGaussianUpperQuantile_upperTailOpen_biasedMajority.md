<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.standardGaussianUpperQuantile_upperTailOpen_biasedMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantile of the Gaussian upper tail

**Claim.** For every real $t$, the standard Gaussian upper quantile at the standard Gaussian upper-tail probability of $t$ is $t$.

**Proof.** The interval-valued upper-tail map sends the order-dual point corresponding to $t$ to the interval point whose value is the upper-tail probability of $t$. The positivity and strict upper bound for that probability ensure it is a point of $(0,1)$. Thus the quantile at the displayed interval-valued tail probability is the same as the quantile at the subtype point built from that probability. The upper quantile inverts the upper tail, so this value is $t$ (\texttt{standardGaussianUpperQuantile\_upperTail}).

**Key facts.** `FABL.standardGaussianUpperQuantile_upperTail`.
