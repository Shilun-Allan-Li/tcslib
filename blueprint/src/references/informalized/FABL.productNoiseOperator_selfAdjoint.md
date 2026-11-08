<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productNoiseOperator_selfAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-Adjointness of Product Noise

**Claim.** For any real-valued functions $f,g$ on $\Omega^n$, the product noise operator is self-adjoint for the product inner product weighted by $\pi^n$.

**Proof.** Apply the product Plancherel identity (FABL.FiniteFourierBasis.plancherel) to each inner product. Both sides become sums over multi-indices of products of Fourier coefficients. The noise operator multiplies the coefficient at index $a$ by $\rho^{\mathrm{order}(a)}$ (FABL.FiniteFourierBasis.fourierCoeff_productNoiseOperator). Thus each summand on either side is the same: the multiplier is attached to one of the two real factors, and multiplication is commutative. The sums, and therefore the inner products, agree.

**Key facts.** `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_productNoiseOperator`.
