<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_productFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of product basis functions

**Claim.** For multi-indices $a,b$, the Fourier coefficient at $a$ of the product basis function indexed by $b$ is $1$ when $a=b$ and $0$ otherwise.

**Proof.** Unfolding the Fourier coefficient identifies it with the product-probability expectation of the product of the basis functions indexed by $b$ and $a$. The product basis is orthonormal for this expectation (FABL.FiniteFourierBasis.productFunction_orthonormal), so this expectation is $1$ for equal indices and $0$ for distinct indices.

**Key facts.** `FABL.FiniteFourierBasis.productFunction_orthonormal`.
