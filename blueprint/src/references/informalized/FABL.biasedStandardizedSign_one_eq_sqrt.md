<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedStandardizedSign_one_eq_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standardized Sign at One

**Claim.** When $0<p<1$, the standardized sign evaluated at $1$ equals $\sqrt{p/(1-p)}$.

**Proof.** By the identity for the standardized sign at $1$ (`FABL.biasedStandardizedSign_one_eq`), it suffices to show that $2p/\mathrm{biasSigma}(p)$ equals the stated square root. Both quantities are nonnegative: $p>0$ and the scale is positive (`FABL.biasSigma_pos`), while the square root is nonnegative. Thus it is enough to compare their squares. The scale-square identity (`FABL.biasSigma_sq`) gives $\mathrm{biasSigma}(p)^2=4p(1-p)$, and the square of $\sqrt{p/(1-p)}$ is $p/(1-p)$. Since $p$ and $1-p$ are nonzero, clearing denominators reduces the equality of squares to $4p^2(1-p)=4p^2(1-p)$, as required.

**Key facts.** `FABL.biasedStandardizedSign_one_eq`, `FABL.biasSigma_pos`, `FABL.biasSigma_sq`.
