<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceTruncation.lean :: BooleanAnalysis.GaussianSpace.Invariance.lowDegreePart_polynomial_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for a Low-Degree Truncation

**Claim.** The Fourier coefficient family of the degree-$d$ truncation vanishes on every subset of size greater than $d$, so it has degree at most $d$.

**Proof.** Let $S$ have cardinality greater than $d$. The Fourier coefficient of the truncation at $S$ equals the original coefficient when $|S|\le d$ and is zero otherwise (\texttt{KKL.fourierCoeff_lowDegreePart}). Here the latter case applies, so that coefficient vanishes. This holds for every such $S$, which is exactly the stated degree bound.

**Key facts.** `KKL.fourierCoeff_lowDegreePart`.
