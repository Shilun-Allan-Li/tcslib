<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.fourierOneNorm_lowDegreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of a low-degree part

**Claim.** The Fourier one-norm of the part of a function formed from Fourier terms indexed by subsets of size at most $k$ is the sum of the absolute values of its original Fourier coefficients over those subsets.

**Proof.** By the coefficient formula for the low-degree part, the Fourier coefficient at a set $S$ is the original coefficient when $|S|\le k$, and is zero otherwise ( `fourierCoeff_lowDegreePart`). Thus the Fourier one-norm is the sum over all $S$ of the absolute value of this piecewise coefficient. Filtering that sum to the sets with $|S|\le k$ leaves exactly the stated sum; the terms outside the filter vanish.

**Key facts.** `FABL.fourierCoeff_lowDegreePart`.
