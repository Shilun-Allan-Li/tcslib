<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_discreteDerivative_mul_coordinateIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative Expectation with a Coordinate Indicator

**Claim.** Under the heterogeneous product distribution on the biased sign cube, the expectation of the discrete derivative in coordinate $i$ times the indicator that $X_i=b$ equals the probability of $b$ at coordinate $i$ times the expectation of that derivative.

**Proof.** For signs $b$ and $X_i$, express the indicator of $X_i=b$ as $(1+bX_i)/2$ (`FABL.sign_eq_indicator_formula`). Multiplying by the discrete derivative writes the integrand as half the derivative plus half of $b$ times the derivative multiplied by $X_i$. Linearity of expectation and extraction of constant factors (`FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_mul`) reduce the claim to the expectation of the derivative times $X_i$ (`FABL.pmfExpectation_heterogeneousBiasedSignPMF_discreteDerivative_mul_sign`). That identity gives the factor $1-2p_i$, the mean of the $i$th sign. Substituting $b=1$ and $b=-1$ in turn and simplifying yields respectively the masses $1-p_i$ and $p_i$, exactly as claimed.

**Key facts.** `FABL.sign_eq_indicator_formula`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_heterogeneousBiasedSignPMF_discreteDerivative_mul_sign`.
