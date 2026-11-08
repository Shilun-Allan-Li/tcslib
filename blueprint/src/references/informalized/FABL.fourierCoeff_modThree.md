<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.fourierCoeff_modThree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mod-Three Fourier Coefficients

**Claim.** The Fourier coefficient of the mod-three function at $S$ equals the stated candidate coefficient, including its empty-set term and its parity-dependent expression.

**Proof.** The candidate coefficients give a multilinear-polynomial expansion of the mod-three function (\(\texttt{FABL.modThree_eq_multilinearPolynomial}\)). Fourier expansion uniqueness says that any coefficients furnishing such an expansion must be the Fourier coefficients themselves (\(\texttt{FABL.fourier_expansion_unique}\)). Apply this uniqueness to the candidate coefficients and evaluate the resulting equality of coefficient functions at $S$; reversing the equality yields the claimed formula.

**Key facts.** `FABL.modThree_eq_multilinearPolynomial`, `FABL.fourier_expansion_unique`.
