<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierEstimator.lean :: FABL.fourierOneNorm_pointwise_mul_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial multiplication preserves Fourier norm

**Claim.** For a real-valued function on the sign cube and any coordinate set $U$, multiplying the function pointwise by the monomial indexed by $U$ leaves its Fourier one-norm unchanged.

**Proof.** Multiplication by the monomial indexed by $U$ shifts the Fourier coefficient at $S$ to the original coefficient at $U\triangle S$ (`fourierCoeff_pointwise_mul_monomial`). The map $S\mapsto U\triangle S$ is a bijection on the coordinate subsets, since applying it twice returns $S$. Thus summing the absolute values of the shifted coefficients gives the same total as summing the absolute values of all original coefficients.

**Key facts.** `FABL.fourierCoeff_pointwise_mul_monomial`.
