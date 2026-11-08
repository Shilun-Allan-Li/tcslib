<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.fourierCoeff_finset_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of a finite sum

**Claim.** The Fourier coefficient of a finite sum of functions at a fixed multi-index equals the sum of their Fourier coefficients at that index.

**Proof.** Induct on the finite set of summation indices. For the empty set both sides are zero. For a set obtained by adjoining a new index $k$ to $s$, the sum of functions is the function at $k$ plus the sum over $s$. Additivity of Fourier coefficients (\texttt{fourierCoeff_add}) turns its coefficient into the coefficient at $k$ plus the coefficient of the sum over $s$. The induction hypothesis identifies the latter with the sum of coefficients over $s$, giving the desired formula.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_add`.
