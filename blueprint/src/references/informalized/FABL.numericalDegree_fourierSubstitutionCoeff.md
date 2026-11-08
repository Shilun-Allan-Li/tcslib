<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.numericalDegree_fourierSubstitutionCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree under Fourier substitution

**Claim.** The numerical degree of the coefficient function formed by weighting each sum of Fourier coefficients over supersets of a set $T$ by $(-2)^{|T|}$ equals the Fourier degree of $p$.

**Proof.** First, every nonzero substituted coefficient is indexed by a set whose size is at most the Fourier degree. Indeed, if $|T|$ were larger, every superset $S\supseteq T$ would also have size larger than the Fourier degree, so its Fourier coefficient would vanish by the characterization of Fourier degree (`fourierDegree_le_iff`). The sum defining the coefficient at $T$ would therefore be zero, a contradiction. The characterization of numerical degree (`numericalDegree_le_iff`) then gives the upper bound. For the reverse bound, if the Fourier degree is zero, the desired inequality is immediate. Otherwise, choose a set $S$ of size equal to the Fourier degree with nonzero Fourier coefficient (`exists_top_fourierCoeff`). Since no strict superset of $S$ can have a nonzero Fourier coefficient, the sum over supersets of $S$ reduces to its own Fourier coefficient (`sum_fourierCoeff_supersets_eq_self_of_card_eq_degree`). The factor $(-2)^{|S|}$ is nonzero, so the substituted coefficient at $S$ is nonzero. The numerical degree is at least $|S|$ by `numericalDegree_le_iff`, giving the reverse bound and hence equality.

**Key facts.** `FABL.numericalDegree_le_iff`, `FABL.fourierDegree_le_iff`, `FABL.exists_top_fourierCoeff`, `FABL.sum_fourierCoeff_supersets_eq_self_of_card_eq_degree`.
