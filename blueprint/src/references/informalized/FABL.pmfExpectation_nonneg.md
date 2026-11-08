<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative expectation

**Claim.** If a real-valued function is nonnegative at every point of a finite probability space, then its expectation is nonnegative.

**Proof.** The expectation of the constant-zero function is zero (`pmfExpectation_const`). Pointwise, the constant-zero function is at most $f$ by hypothesis. Monotonicity of expectation (`pmfExpectation_mono`) therefore gives $0=\mathbb E_p[0]\leq\mathbb E_p[f]$.

**Key facts.** `FABL.pmfExpectation_const`, `FABL.pmfExpectation_mono`.
