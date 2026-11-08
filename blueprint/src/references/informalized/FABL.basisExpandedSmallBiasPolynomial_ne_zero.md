<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.basisExpandedSmallBiasPolynomial_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of the expanded polynomial

**Claim.** If the coordinate vector is nonzero, then its basis-expanded polynomial is nonzero.

**Proof.** A nonzero coordinate vector has at least one nonzero grouped coefficient, say the coefficient in block $i$ (\(\texttt{exists\_basisExpandedGroupedCoefficient\_ne\_zero}\)). In the polynomial, the coefficient of $X^{i+1}$ is exactly that grouped coefficient: the summand indexed by $i$ contributes it, while all other summands have different exponents. Thus this polynomial coefficient is nonzero. The zero polynomial has every coefficient zero, so the polynomial cannot be zero.

**Key facts.** `FABL.exists_basisExpandedGroupedCoefficient_ne_zero`.
