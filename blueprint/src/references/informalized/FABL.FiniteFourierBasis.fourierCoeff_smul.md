<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling of Fourier coefficients

**Claim.** For a real scalar $c$, the Fourier coefficient of $cf$ at $a$ is $c$ times the Fourier coefficient of $f$ at $a$.

**Proof.** In the defining expectation, the integrand for the coefficient of $cf$ is pointwise $c$ times the integrand for the coefficient of $f$, by associativity and commutativity of real multiplication. Expectation under a probability mass function pulls out a constant factor (FABL.pmfExpectation_const_mul), giving the claimed identity.

**Key facts.** `FABL.pmfExpectation_const_mul`.
