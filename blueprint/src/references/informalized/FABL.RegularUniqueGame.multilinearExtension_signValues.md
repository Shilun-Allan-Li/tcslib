<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.multilinearExtension_signValues -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multilinear extension at sign inputs

**Claim.** At the real values of a sign tuple, the multilinear extension of a sign predicate's acceptance indicator equals that indicator evaluated on the tuple.

**Proof.** Expand the multilinear extension as the sum of Fourier coefficients times the corresponding coordinate monomials. At the real values of the signs, each monomial is exactly the sign-cube monomial of the tuple. The Fourier expansion reconstructs the acceptance indicator at that tuple (\texttt{FABL.fourier\_expansion}); applying it gives the claimed equality.

**Key facts.** `FABL.fourier_expansion`.
