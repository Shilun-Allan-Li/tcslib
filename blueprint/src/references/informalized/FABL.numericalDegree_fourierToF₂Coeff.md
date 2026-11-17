<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.numericalDegree_fourierToF₂Coeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of normalized Fourier coefficients

**Claim.** The numerical degree of the coefficient function obtained by taking half the difference between the empty-set indicator and the Fourier-substitution coefficient equals the Fourier degree of $p$.

**Proof.** For the upper bound, suppose a coefficient at $T$ is nonzero and that $|T|$ exceeds the Fourier degree. The Fourier-substitution coefficient at $T$ must vanish: otherwise its numerical degree would be at least $|T|$, contradicting the degree identity for Fourier substitution (which itself follows from the Fourier degree). Also, $T$ cannot be empty, since its size exceeds the nonnegative Fourier degree. Thus both terms in the defining half-difference vanish, contradicting the assumed nonzero coefficient. The numerical-degree criterion (`numericalDegree_le_iff`) gives the upper bound. If the Fourier degree is zero, the reverse bound is immediate. Otherwise choose a set $S$ of size equal to that degree with nonzero Fourier coefficient (`exists_top_fourierCoeff`). The sum over supersets of $S$ reduces to that coefficient (`sum_fourierCoeff_supersets_eq_self_of_card_eq_degree`), so the Fourier-substitution coefficient at $S$ is nonzero. Since $|S|>0$, the empty-set indicator term is zero, and the normalized coefficient at $S$ is therefore nonzero as well. The numerical-degree criterion gives degree at least $|S|$, proving equality.

**Key facts.** `FABL.numericalDegree_le_iff`, `FABL.numericalDegree_fourierSubstitutionCoeff`, `FABL.exists_top_fourierCoeff`, `FABL.sum_fourierCoeff_supersets_eq_self_of_card_eq_degree`.
