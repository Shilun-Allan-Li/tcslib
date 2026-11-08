<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.fourierCoeff_parityTimes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity multiplication shifts coefficients

**Claim.** Multiplying a Boolean function by the parity character on $S$ shifts its Fourier coefficient at $T$ to the Fourier coefficient of the original function at $S\triangle T$.

**Proof.** The real-valued form of the product is the product of the monomial on $S$ and the original real-valued function (`parityTimes_toReal`). In the expectation defining the coefficient at $T$, combine the two monomial factors: the product of the monomials on $S$ and $T$ is the monomial on their symmetric difference (`monomial_mul_monomial`). The resulting expectation is exactly the coefficient of the original function at $S\triangle T$.

**Key facts.** `FABL.parityTimes_toReal`, `FABL.monomial_mul_monomial`.
