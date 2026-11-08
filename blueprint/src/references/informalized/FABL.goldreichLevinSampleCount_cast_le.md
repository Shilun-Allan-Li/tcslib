<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinSampleCount_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sample Count Bound

**Claim.** The rational sample count at the specified accuracy and confidence is at most $5120(n+1)(\mathrm{cap}(\tau)+1)/\tau^4$.

**Proof.** The estimator scheduling bound gives a sample count at most four times the failure-bit count divided by the square of the accuracy (`fourierEstimatorSampleCount_cast_le`). The specified confidence has failure-bit count at most $80(n+1)(\mathrm{cap}(\tau)+1)$ (`goldreichLevinCallConfidence_failureBits_le`). Substitute this bound and the accuracy $\tau^2/4$. The resulting expression is $4\cdot80(n+1)(\mathrm{cap}(\tau)+1)/(\tau^2/4)^2$, which simplifies to the claimed bound since $(\tau^2/4)^2=\tau^4/16$.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`, `FABL.goldreichLevinCallConfidence_failureBits_le`.
