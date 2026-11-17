<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.productMean_anisotropicProductNoiseOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Preservation by Anisotropic Noise

**Claim.** The anisotropic product noise operator preserves the product mean of every function on the product space, for arbitrary real coordinate parameters.

**Proof.** The product mean of a function is its Fourier coefficient at the all-constant multi-index (`fourierCoeff_zeroMultiIndex`). Thus it suffices to compare that coefficient before and after applying the anisotropic noise operator. The coefficient formula for this operator (`fourierCoeff_anisotropicProductNoiseOperator`) multiplies each Fourier coefficient by the product of the coordinate noise factors, using factor $1$ wherever the multi-index is constant. At the all-constant multi-index every factor is $1$, so this coefficient is unchanged. Translating back from the all-constant coefficient to the product mean proves the result.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_zeroMultiIndex`, `FABL.FiniteFourierBasis.fourierCoeff_anisotropicProductNoiseOperator`.
