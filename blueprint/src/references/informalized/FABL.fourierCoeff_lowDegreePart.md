<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.fourierCoeff_lowDegreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of the low-degree part

**Claim.** The Fourier coefficient at $T$ of the sum of the Fourier terms supported on sets of size at most $k$ equals the coefficient of the original function at $T$ if $|T|\le k$, and is zero otherwise.

**Proof.** Identify the low-degree part with the sparse Fourier approximation whose index family consists of sets of size at most $k$ (`FABL.lowDegreePart_eq_sparseFourierApproximation`). The coefficient formula for a sparse Fourier approximation says its coefficient at $T$ is the assigned coefficient when $T$ belongs to that family, and zero otherwise (`FABL.fourierCoeff_sparseFourierApproximation`). Membership here is exactly the condition $|T|\le k$, giving the result.

**Key facts.** `FABL.lowDegreePart_eq_sparseFourierApproximation`, `FABL.fourierCoeff_sparseFourierApproximation`.
