<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.tendsto_standardGaussianUpperQuantileReal_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper quantile near unit tail probability

**Claim.** As $\alpha$ tends to $1$ from below, the extended standard Gaussian upper quantile tends to $-\infty$.

**Proof.** On the interval $0<\alpha<1$, the extended quantile agrees with the quantile defined on that interval (\texttt{FABL.standardGaussianUpperQuantileReal\_eq}). The quantile is the inverse of the strictly increasing order isomorphism from the oppositely ordered real line to $(0,1)$ given by the upper-tail probability. Consequently, as its argument approaches the upper endpoint $1$ in the usual order on $(0,1)$, this inverse tends to the bottom of the usual real line, that is, to $-\infty$. The standard result transporting endpoint limits through the interval parametrization then gives the asserted one-sided limit for the extended quantile.

**Key facts.** `FABL.standardGaussianUpperQuantileReal_eq`.
