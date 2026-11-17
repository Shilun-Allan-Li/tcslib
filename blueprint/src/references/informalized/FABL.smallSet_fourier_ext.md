<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.smallSet_fourier_ext -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness from Fourier coefficients

**Claim.** If two real-valued functions on the Boolean cube have equal Fourier coefficients for every subset of coordinates, then the functions are equal.

**Proof.** Fix a point $x$ of the cube. The Fourier expansion formula expresses each function there as the sum, over all coordinate subsets $S$, of its Fourier coefficient at $S$ times the monomial indexed by $S$ (\texttt{FABL.fourier_expansion}). The monomials are the same for both functions, and the assumed coefficient equality makes the summands agree term by term. Thus the functions agree at every $x$, so they are equal.

**Key facts.** `FABL.fourier_expansion`.
