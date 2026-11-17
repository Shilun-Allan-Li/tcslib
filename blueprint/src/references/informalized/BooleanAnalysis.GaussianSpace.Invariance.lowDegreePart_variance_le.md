<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceTruncation.lean :: BooleanAnalysis.GaussianSpace.Invariance.lowDegreePart_variance_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance Bound for a Low-Degree Truncation

**Claim.** The variance of the low-degree Fourier truncation of a Boolean function is at most the variance of the function.

**Proof.** Write each variance as the sum of squared nonconstant Fourier coefficients (\texttt{cubeVariance_eq_sum_nonempty_fourier}); the empty-set term is zero. For each nonempty subset $S$, the truncation coefficient is the original coefficient if $|S|\le d$, and zero otherwise (\texttt{KKL.fourierCoeff_lowDegreePart}). Its square is therefore either the original squared coefficient or zero, in either case no larger than the original squared coefficient. Summing this termwise comparison over all subsets proves the variance inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier`, `KKL.fourierCoeff_lowDegreePart`.
