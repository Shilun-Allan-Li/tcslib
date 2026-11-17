<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.fourierDegree_partitionPolynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a partition polynomial

**Claim.** If $p$ has Fourier degree at most $k$, then for any point $z$ and map $\pi$, the partition polynomial formed from $p,z,\pi$ also has Fourier degree at most $k$.

**Proof.** By the Fourier degree criterion, it is enough to show that every Fourier coefficient indexed by a set $T$ with $|T|>k$ vanishes. Fourier expansion uniqueness identifies the defining coefficients of the partition polynomial with its actual Fourier coefficients. For such a $T$, each term in its defining coefficient sum comes from a set $S$ whose identified frequency is $T$. The identified frequency has size at most $|S|$ (`identifiedFrequency_card_le`), so $|S|\ge |T|>k$. The degree criterion for $p$ therefore makes the Fourier coefficient of $p$ at $S$ zero, and hence every term of the sum vanishes.

**Key facts.** `FABL.fourier_expansion_unique`, `FABL.identifiedFrequency_card_le`, `FABL.fourierDegree_le_iff`.
