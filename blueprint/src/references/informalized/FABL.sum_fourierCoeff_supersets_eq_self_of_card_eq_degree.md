<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.sum_fourierCoeff_supersets_eq_self_of_card_eq_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients Above Maximal Degree

**Claim.** If a set $S$ has cardinality equal to the Fourier degree of $p$, then the sum of the Fourier coefficients indexed by sets containing $S$ equals the coefficient indexed by $S$.

**Proof.** In the sum over all supersets of $S$, the term indexed by $S$ is present. Any other such set $U$ strictly contains $S$, so $|U|>|S|$, and hence $|U|$ exceeds the Fourier degree. By the characterization of Fourier degree, every coefficient indexed by a set whose size exceeds that degree is zero (`FABL.fourierDegree_le_iff`). Thus all terms other than the one indexed by $S$ vanish, leaving precisely its Fourier coefficient.

**Key facts.** `FABL.fourierDegree_le_iff`.
