<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_heterogeneousBiasedSignPMF_discreteDerivative_mul_sign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative and coordinate sign correlation

**Claim.** Under the independent product distribution with coordinate parameters $p_j\in(0,1)$, the expectation of the product of the discrete derivative in coordinate $i$ and the $i$th coordinate sign is $(1-2p_i)$ times the expectation of that discrete derivative.

**Proof.** Expand the discrete derivative in its Fourier sum over subsets containing $i$. Multiplying each term by the sign in coordinate $i$ turns the monomial on $S\setminus\{i\}$ into the monomial on $S$; this is the monomial deletion-and-coordinate identity (\texttt{FABL.monomial_erase_mul_coordinate}). Thus the product is a sum whose terms are the Fourier coefficient for $S$ times the monomial on $S$. Take expectations term by term. For each $S$ containing $i$, the monomial expectation is the product of the coordinate means over $S$ (\texttt{FABL.pmfExpectation_heterogeneousBiasedSignPMF_monomial}). Factoring out the mean in coordinate $i$ leaves the corresponding product over $S\setminus\{i\}$, exactly the term obtained from the expected discrete derivative expansion. The common factor is $1-2p_i$.

**Key facts.** `FABL.discreteDerivative_eq_fourier_sum`, `FABL.monomial_erase_mul_coordinate`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_heterogeneousBiasedSignPMF_discreteDerivative`, `FABL.pmfExpectation_heterogeneousBiasedSignPMF_monomial`.
