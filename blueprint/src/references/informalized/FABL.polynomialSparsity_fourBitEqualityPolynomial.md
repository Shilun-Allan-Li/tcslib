<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdFunctions.lean :: FABL.polynomialSparsity_fourBitEqualityPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparsity of the Four-Bit Equality Polynomial

**Claim.** The four-bit equality polynomial has polynomial sparsity $7$.

**Proof.** The Fourier support of this polynomial consists of the empty set together with the six two-coordinate sets corresponding to pairs among the four coordinates ($\texttt{fourierSupport\_fourBitEqualityPolynomial}$). These are seven distinct frequencies. Since polynomial sparsity is the cardinality of the Fourier support, its value is $7$.

**Key facts.** `FABL.fourierSupport_fourBitEqualityPolynomial`.
