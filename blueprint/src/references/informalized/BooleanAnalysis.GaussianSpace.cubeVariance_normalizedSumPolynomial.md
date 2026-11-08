<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedSums.lean :: BooleanAnalysis.GaussianSpace.cubeVariance_normalizedSumPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of the normalized cube sum

**Claim.** For $n>0$, the normalized sum polynomial evaluated on the Boolean cube has variance $1$.

**Proof.** The proof first identifies the variance with the total influence: the Fourier formula for variance sums squared Fourier coefficients over nonempty sets, while total influence sums each squared coefficient with its set size. For the evaluated polynomial, each Fourier coefficient is its defining polynomial coefficient, so it vanishes except on singleton sets, where it equals $1/\sqrt n$. Thus every nonzero term in either sum comes from a singleton, whose size is $1$, and the two sums agree. Finally, each coordinate has influence $1/n$; summing over the $n$ coordinates gives total influence $n(1/n)=1$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier`, `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval`, `BooleanAnalysis.GaussianSpace.influence_normalizedSumPolynomial`.
