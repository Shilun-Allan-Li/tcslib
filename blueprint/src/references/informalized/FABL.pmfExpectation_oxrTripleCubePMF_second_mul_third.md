<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_oxrTripleCubePMF_second_mul_third -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second and Third Query Correlation

**Claim.** The expectation of the product of $f$ on the second and third query vectors under the specified triple distribution equals the noise stability of $f$ at correlation $-\delta$.

**Proof.** Expand each copy of $f$ in its Fourier basis. Multiplying the two expansions expresses the expectation as a double sum of products of Fourier coefficients times the expected product of the corresponding two monomials. Insert the constant monomial on the first query, which does not change that product. The monomial expectation formula for the triple distribution (`pmfExpectation_oxrTripleCubePMF_monomials`) then vanishes unless the two index sets agree; in that case its value is $(-\delta)^{|S|}$. Thus the double sum reduces to $\sum_S (-\delta)^{|S|}\widehat f(S)^2$. The Fourier formula for noise stability (`noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`), applied at $\rho=-\delta$, identifies this sum with the claimed noise stability.

**Key facts.** `FABL.fourier_expansion`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_oxrTripleCubePMF_monomials`, `FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`.
