<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Fourier coefficients

**Claim.** For any two functions $f$ and $g$ on the product space, the Fourier coefficient of $f+g$ at a multi-index is the sum of their Fourier coefficients at that index.

**Proof.** By definition, the coefficient of $f+g$ is the expectation of $(f+g)$ times the corresponding product basis function. Distributing multiplication expresses the integrand as the sum of $f$ and $g$ times that basis function. Expectation under a finite probability measure is additive (\texttt{pmfExpectation_add}), so the coefficient is the sum of the two separate coefficients.

**Key facts.** `FABL.pmfExpectation_add`.
