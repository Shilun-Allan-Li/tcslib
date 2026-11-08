<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdFunctions.lean :: FABL.fourierSupport_fourBitEqualityPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support of the four-bit equality polynomial

**Claim.** The Fourier support of the four-bit equality polynomial consists of the empty set and the six two-element subsets of the four coordinates.

**Proof.** Fix a subset of the four coordinates. Its membership in the Fourier support is equivalent to its Fourier coefficient being nonzero (`mem_fourierSupport`). The coefficient formula for this polynomial (`fourierCoeff_fourBitEqualityPolynomial`) identifies that coefficient with the stated coefficient function. Now split into whether the subset is empty and whether it belongs to the collection of six two-element subsets. In each of the resulting cases, the coefficient formula says precisely that the coefficient is nonzero for the empty set and those six pairs, and zero otherwise. Thus the support is exactly the asserted collection.

**Key facts.** `FABL.mem_fourierSupport`, `FABL.fourierCoeff_fourBitEqualityPolynomial`.
