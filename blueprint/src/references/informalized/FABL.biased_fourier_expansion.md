<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biased_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Fourier Expansion

**Claim.** For every function on the sign cube, its value at any point is the sum of its biased Fourier coefficients multiplied by the corresponding biased monomials.

**Proof.** Apply the finite Fourier basis expansion (`FABL.FiniteFourierBasis.fourier_expansion`) to the biased site basis. This expresses the function as a sum over all multi-indices, with each term the corresponding Fourier coefficient times the product basis function. Reindex this finite sum by subsets of coordinates using the equivalence between subsets and binary multi-indices (`finsetEquivBinaryMultiIndex`). Under this correspondence, each coefficient and product basis function is exactly the biased Fourier coefficient and biased monomial indexed by that subset, yielding the claimed expansion.

**Key facts.** `FABL.FiniteFourierBasis.fourier_expansion`.
