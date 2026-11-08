<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.variance_pBiasedRandomFunction_fourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Random Fourier Coefficient

**Claim.** For the independent $p$-biased random Boolean function, the variance of its Fourier coefficient at any set of coordinates is $p(1-p)/2^n$.

**Proof.** Center each random bit by subtracting its mean $p$. The Fourier coefficient is then a deterministic offset—equal to $p$ for the empty set and zero otherwise—plus a sum of these centered bits weighted by the normalized monomial (`fourierCoeff_sub_pBiasedMean_eq_weightedCenteredSum`). The random function's measure is a product of the individual bit measures (`pBiasedRandomFunctionPMF_toMeasure`), so the centered contributions at distinct inputs are independent and their variances add. Scaling a centered bit by a weight scales its variance by the square of that weight; each bit has variance $p(1-p)$ (`variance_zeroOneValue_pBiasedBitPMF`). Thus the total variance is $p(1-p)$ times the sum of squared normalized monomial weights. That sum is the reciprocal of the cube's cardinality (`sum_sq_normalized_monomial`), and the cube has $2^n$ points, giving the stated result.

**Key facts.** `FABL.fourierCoeff_sub_pBiasedMean_eq_weightedCenteredSum`, `FABL.pBiasedRandomFunctionPMF_toMeasure`, `FABL.variance_zeroOneValue_pBiasedBitPMF`, `FABL.sum_sq_normalized_monomial`.
