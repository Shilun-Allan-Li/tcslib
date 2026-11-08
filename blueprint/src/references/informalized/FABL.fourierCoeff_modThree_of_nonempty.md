<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.fourierCoeff_modThree_of_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Mod-Three Coefficients

**Claim.** For nonempty $S$, the Fourier coefficient of the mod-three function is the stated expression when $|S|$ is even, and is zero when $|S|$ is odd.

**Proof.** Use the formula for all mod-three Fourier coefficients (\(\texttt{FABL.fourierCoeff_modThree}\)) and substitute the definition of the candidate coefficient. Since $S$ is nonempty, its empty-set indicator vanishes. What remains is precisely the parity-dependent expression in the claim.

**Key facts.** `FABL.fourierCoeff_modThree`.
