<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.fourierOneNorm_toReal_le_of_spectralSparsity_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm from spectral sparsity

**Claim.** If the binary Fourier spectrum of a sign-valued function has at most $S$ nonzero coefficients, then the Fourier one-norm of its real sign representation is at most $S$.

**Proof.** Transfer the function to the binary cube and denote its real-valued representation by $g$. Parseval’s identity for a sign-valued function gives $\sum_\gamma \widehat g(\gamma)^2=1$ (\texttt{sum_sq_vectorFourierCoeff_signValue_eq_one}). Since each term is nonnegative, each individual squared coefficient is at most this sum; hence $|\widehat g(\gamma)|\le 1$. The Fourier one-norm on the sign cube equals the sum of these absolute binary Fourier coefficients, by the norm identifications (\texttt{fourierOneNorm_eq_spectralPNorm_one} and \texttt{spectralPNorm_one_eq_sum_abs}). Coefficients outside the support vanish, so the sum reduces to the support. Each term there is at most $1$, making the sum at most the support’s cardinality, which is the spectral sparsity (\texttt{spectralSparsity_eq_card_vectorFourierSupport}). The assumed sparsity bound completes the argument.

**Key facts.** `FABL.sum_sq_vectorFourierCoeff_signValue_eq_one`, `FABL.fourierOneNorm_eq_spectralPNorm_one`, `FABL.spectralPNorm_one_eq_sum_abs`, `FABL.spectralSparsity_eq_card_vectorFourierSupport`.
