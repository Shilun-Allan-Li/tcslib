<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_biasedSignPMF_sign_mul_standardized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign–standardized sign expectation

**Claim.** For a sign chosen with mean $1-2p$, the expectation of the sign times its standardized value is $[?]$

**Proof.** Pointwise, write the sign as its mean plus its deviation from that mean. Since the standardized sign is the deviation divided by $\sigma$, this gives $X Z=(1-2p)Z+\sigma Z^2$. Taking expectations and using that the standardized sign has mean zero and second moment one yields $\mathbb{E}[XZ]=(1-2p)\cdot 0+\sigma\cdot 1=\sigma$. The division is valid because $0<p<1$ implies $\sigma>0$.

**Key facts.** `FABL.biasSigma_pos`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_biasedStandardizedSign`, `FABL.pmfExpectation_biasedStandardizedSign_sq`.
