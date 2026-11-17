<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.fourierDegree_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier degree is bounded by dimension

**Claim.** For every function on the $n$-dimensional Boolean cube, its Fourier degree is at most $n$.

**Proof.** The degree criterion (`fourierDegree_le_iff`) reduces the claim to showing that any frequency set with cardinality greater than $n$ has zero coefficient. But every subset of the $n$ coordinates has cardinality at most $n$, so no such frequency set exists. The required vanishing condition is therefore vacuous.

**Key facts.** `FABL.fourierDegree_le_iff`.
