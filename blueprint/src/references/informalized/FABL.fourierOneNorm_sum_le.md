<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.fourierOneNorm_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of a finite sum

**Claim.** The Fourier one-norm of a finite pointwise sum of real-valued functions is at most the sum of their Fourier one-norms.

**Proof.** For each frequency, the Fourier coefficient of the sum is the sum of the individual Fourier coefficients, by linearity of Fourier coefficients (\texttt{fourierCoeff_sum}). The triangle inequality bounds the absolute value of this coefficient sum by the sum of the absolute values. Summing this inequality over all frequencies and interchanging the two finite sums yields the sum of the individual Fourier one-norms.

**Key facts.** `FABL.fourierCoeff_sum`.
