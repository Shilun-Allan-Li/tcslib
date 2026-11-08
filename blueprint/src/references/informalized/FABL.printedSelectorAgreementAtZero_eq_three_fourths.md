<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoise.lean :: FABL.printedSelectorAgreementAtZero_eq_three_fourths -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selector agreement at zero

**Claim.** For independent uniform bits $U,V$ and independent uniform signs $X,Y$, selecting $U$ for sign $1$ and $V$ for sign $-1$ gives agreement probability $3/4$, averaged over all four choices.

**Proof.** Replace each uniform finite expectation by the corresponding average over its finite set, and express a uniform sign average as the average of the values at $1$ and $-1$ (`pmfExpectation_uniformPMF_eq_expect`, `expect_sign`). For fixed bits $U,V$, if $U=V$, the two selections always agree, contributing probability $1$. If $U\ne V$, the selections agree exactly when $X=Y$, which occurs in two of the four equally likely sign pairs, contributing $1/2$. Averaging these cases over the four equally likely choices of $(U,V)$ gives $(2\cdot1+2\cdot\tfrac12)/4=3/4$.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_sign`.
