<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/JuntaStableInfluence.lean :: FABL.fourierDegree_sub_const_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier degree under constant shifts

**Claim.** Subtracting a constant from a function of Fourier degree at most $k$ leaves its Fourier degree at most $k$.

**Proof.** By the Fourier degree criterion, consider any set $S$ with $|S|>k$. It is nonempty. The Fourier coefficient of the shifted function is the coefficient of $f$ minus the coefficient of the constant function (`fourierCoeff_sub`). The first term is zero by the assumed degree bound. For the second, the constant factors out of the expectation, and the expected monomial on a nonempty set is zero (`expect_monomial`). Thus the shifted function's coefficient at $S$ vanishes, as required.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.fourierCoeff_sub`, `FABL.expect_monomial`.
