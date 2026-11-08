<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_abs_biasedStandardizedSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Moment of a Standardized Sign

**Claim.** For $0<p<1$, the expected absolute value of the standardized biased sign is $\sigma=\sqrt{4p(1-p)}$.

**Proof.** The biased sign distribution gives expectation $(1-p)g(1)+pg(-1)$ for any function $g$ (\texttt{pmfExpectation\_biasedSignPMF}). Apply this to the absolute value of the standardized sign, and substitute its values at $1$ and $-1$: these are $2p/\sigma$ and $-2(1-p)/\sigma$, respectively. Since $\sigma>0$ (\texttt{biasSigma\_pos}) and $0<p<1$, their absolute values are $2p/\sigma$ and $2(1-p)/\sigma$. The weighted sum is therefore $4p(1-p)/\sigma$. The identity $\sigma^2=4p(1-p)$ (\texttt{biasSigma\_sq}) and $\sigma\ne0$ simplify this to $\sigma$.

**Key facts.** `FABL.pmfExpectation_biasedSignPMF`, `FABL.biasedStandardizedSign_one_eq`, `FABL.biasedStandardizedSign_neg_one_eq`, `FABL.biasSigma_pos`, `FABL.biasSigma_sq`.
