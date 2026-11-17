<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.isFourierGranular_toReal_of_exactSparseSpectrumSparsity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Granularity from Sparse Spectrum

**Claim.** If the encoded Boolean function on $\mathbb F_2^n$ has spectral sparsity at most $2^{k+1}$, then every Fourier coefficient of the original sign-cube function is an integer multiple of $2^{-k}$.

**Proof.** Apply `isVectorFourierGranular_signValue_of_spectralSparsity_le` to the function obtained by evaluating the target after the bit-to-sign encoding. Its sparsity bound is the assumed one, and `exactSparseSpectrumSparsityBound_two_le` supplies the required lower bound of two on that bound. The resulting vector-granularity scale is `spectralSparsityGranularity` of the stated sparsity bound; `spectralSparsityGranularity_exactSparseSpectrumSparsityBound` identifies it with `degreeFourierGranularity (k+1)`, which is $2^{-k}$. Finally, the function on the sign cube associated to this encoded function is exactly the real-valued target: evaluating the encoding and then its inverse cancels. Thus the vector granularity conclusion is precisely the claimed granularity of the target.

**Key facts.** `FABL.exactSparseSpectrumSparsityBound_two_le`, `FABL.isVectorFourierGranular_signValue_of_spectralSparsity_le`, `FABL.spectralSparsityGranularity_exactSparseSpectrumSparsityBound`.
