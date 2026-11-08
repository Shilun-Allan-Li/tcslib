<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedSums.lean :: BooleanAnalysis.GaussianSpace.influence_normalizedSumPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of the Normalized Sum

**Claim.** For each coordinate $i$, the influence of the normalized-sum polynomial evaluated on the Boolean cube is $1/n$.

**Proof.** By the Fourier formula for influence (\texttt{influence_eq_sum_fourier}), the influence is the sum, over subsets containing $i$, of the squares of the Fourier coefficients. The Fourier coefficient of an evaluated multilinear polynomial at a subset is its polynomial coefficient (\texttt{MultilinearPolynomial.fourierCoeff_eval}). The normalized-sum polynomial has nonzero coefficients only on singleton subsets, each equal to $1/\sqrt n$. Among those singletons, the only one containing $i$ is $\{i\}$. Therefore the sum has just one nonzero term, equal to $(1/\sqrt n)^2=1/n$.

**Key facts.** `BooleanAnalysis.influence_eq_sum_fourier`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval`.
