<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.productMean_biasedSignPMF_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Mean of a Sign Monomial

**Claim.** For independent signs with probability $p$ of being $-1$, the mean of the sign monomial indexed by $S$ is $(1-2p)^{|S|}$.

**Proof.** Write the monomial as a product over all coordinates, taking the factor at coordinate $i$ to be the sign itself when $i\in S$ and $1$ otherwise. The expectation of a product of coordinate functions under an independent product distribution factors as the product of their individual expectations (`pmfExpectation_independentProductPMF_prod`). At a coordinate in $S$, the sign has mean $1-2p$ (`pmfExpectation_biasedSignPMF_signValue`); at a coordinate outside $S$, the factor is constantly $1$ and has mean $1$ (`pmfExpectation_const`). Thus the product of coordinate means has one factor $1-2p$ for each element of $S$, and equals $(1-2p)^{|S|}$.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_biasedSignPMF_signValue`, `FABL.pmfExpectation_const`.
