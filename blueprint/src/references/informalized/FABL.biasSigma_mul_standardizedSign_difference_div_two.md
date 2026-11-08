<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasSigma_mul_standardizedSign_difference_div_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Difference of Standardized Signs

**Claim.** For $0<p<1$, the bias scale times the difference of the standardized signs at $1$ and $-1$, divided by $2$, equals $1$.

**Proof.** The standardized values at the two signs are $2p/\sigma_p$ and $-2(1-p)/\sigma_p$, respectively (\texttt{biasedStandardizedSign\_one\_eq}, \texttt{biasedStandardizedSign\_neg\_one\_eq}). Their difference is $2/\sigma_p$. Since $\sigma_p>0$ (\texttt{biasSigma\_pos}), it is nonzero; multiplying this difference by $\sigma_p$ and dividing by $2$ gives $1$.

**Key facts.** `FABL.biasedStandardizedSign_one_eq`, `FABL.biasedStandardizedSign_neg_one_eq`, `FABL.biasSigma_pos`.
