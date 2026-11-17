<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualFourierCoeff_vectorDualEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients under vector space duality

**Claim.** For $f:\mathbb F_2^n\to\mathbb R$ and $\gamma\in\mathbb F_2^n$, the dual Fourier coefficient indexed by the functional corresponding to $\gamma$ equals the vector Fourier coefficient at $\gamma$.

**Proof.** Write the dual Fourier coefficient and the vector Fourier coefficient as expectations of $f(x)$ times their respective Walsh characters, using the coefficient-as-expectation identities (\texttt{FABL.dualFourierCoeff_eq_expect} and \texttt{FABL.vectorFourierCoeff_eq_expect}). The functional corresponding to $\gamma$ has the same Walsh character as the vector index $\gamma$ (\texttt{FABL.dualWalshCharacter_vectorDualEquiv}), so the two expectations agree.

**Key facts.** `FABL.dualFourierCoeff_eq_expect`, `FABL.vectorFourierCoeff_eq_expect`, `FABL.dualWalshCharacter_vectorDualEquiv`.
