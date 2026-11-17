<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.sum_biasedFourierCoeff_singleton_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Biased Fourier Coefficients

**Claim.** The sum of the singleton biased Fourier coefficients of $f$ equals the product-measure expectation of $f$ multiplied by the biased linear score.

**Proof.** Replace each singleton biased Fourier coefficient by its expectation formula (`FABL.biasedFourierCoeff_eq_expect`). The coefficient indexed by $\{i\}$ uses the biased monomial on that singleton; the singleton monomial formula (`FABL.biasedMonomial_apply`) identifies it with the standardized sign in coordinate $i$. Thus the sum of coefficients is the expectation of the sum, over coordinates $i$, of $f(x)$ times that standardized sign. Since multiplication distributes over a finite sum, this integrand is $f(x)$ times the biased linear score. Linearity of the finite PMF expectation (`FABL.pmfExpectation_sum`) identifies the sum of the individual expectations with the expectation of this summed integrand, yielding the claimed identity.

**Key facts.** `FABL.biasedFourierCoeff_eq_expect`, `FABL.pmfExpectation_sum`, `FABL.biasedMonomial_apply`.
