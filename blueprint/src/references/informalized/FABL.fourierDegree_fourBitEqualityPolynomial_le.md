<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdFunctions.lean :: FABL.fourierDegree_fourBitEqualityPolynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the four-bit equality polynomial

**Claim.** The polynomial $P(x)=-3+\sum_{0\le i<j<4}x_i x_j$ on the four-dimensional Boolean cube has Fourier degree at most $2$.

**Proof.** By the degree criterion (`fourierDegree_le_iff`), it suffices to show that every Fourier coefficient indexed by a set $S$ with $|S|>2$ vanishes. The coefficient formula for this polynomial (`fourierCoeff_fourBitEqualityPolynomial`) reduces the coefficient to its explicitly computed coefficient table. The proof separates the empty set, the six quadratic frequencies, and all other frequencies. The empty set cannot have size greater than two, and none of the six quadratic frequencies can either. For every remaining set of size greater than two, the coefficient table gives zero. Thus all coefficients above degree two vanish, as required.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.fourierCoeff_fourBitEqualityPolynomial`.
