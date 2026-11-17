<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.tendsto_standardGaussianUpperQuantileReal_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper quantile near zero tail probability

**Claim.** As $\alpha$ tends to $0$ from above, the extended standard Gaussian upper quantile tends to $+\infty$.

**Proof.** For $0<\alpha<1$, the extended quantile agrees with the quantile defined on that interval (\texttt{FABL.standardGaussianUpperQuantileReal\_eq}). The quantile is the inverse of the upper-tail order isomorphism. As the argument approaches the lower endpoint $0$ of $(0,1)$, the inverse tends to the top of the usual real line, namely $+\infty$. Transferring this endpoint limit to the one-sided limit of the extended quantile proves the claim.

**Key facts.** `FABL.standardGaussianUpperQuantileReal_eq`.
