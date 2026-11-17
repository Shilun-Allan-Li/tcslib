<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_abs_heterogeneousBiasedMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Moment of a Heterogeneous Monomial

**Claim.** For independent biased signs with parameters $p_i\in(0,1)$ and any index set $S$, the expected absolute value of their standardized monomial is $\prod_{i\in S}\sigma_i$.

**Proof.** Write the joint law as the independent product of the coordinate laws. The absolute value of a product is the product of the absolute values, and coordinates outside $S$ can be assigned the factor $1$. The expectation of a product of coordinate functions under the independent product law factors into the product of their coordinate expectations (\texttt{pmfExpectation\_independentProductPMF\_prod}). For each $i\in S$, the one-coordinate absolute moment is $\sigma_i$ by \texttt{pmfExpectation\_abs\_biasedStandardizedSign}; for $i\notin S$, the coordinate function is constantly $1$, whose expectation is $1$ (\texttt{pmfExpectation\_const\_one}). Multiplying these factors gives the product over $S$.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_abs_biasedStandardizedSign`, `FABL.pmfExpectation_const_one`.
