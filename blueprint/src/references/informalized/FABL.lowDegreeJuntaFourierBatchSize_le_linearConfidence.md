<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaFourierBatchSize_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Batch Size Bound

**Claim.** The Fourier batch size is bounded by the stated coefficient times $(n+1)^{r+1}(b+1)$, with $r=\lfloor3k/4\rfloor$ and the coefficient defined in the statement.

**Proof.** Bound the size of the Fourier family by $(r+1)(n+1)^r$ using `card_lowDegreeJuntaFourierFamily_le`. Bound the sample count by $36\cdot4^k$ times its failure-bit count using `lowDegreeJuntaCoefficientSampleCount_le_failureBits`. The failure-bit count is at most the linear-confidence coefficient times $(n+1)(b+1)$ by `lowDegreeJuntaCoefficientFailureBits_le_linearConfidence`. Multiplying these nonnegative bounds gives the claimed product; the identity $(n+1)^r(n+1)=(n+1)^{r+1}$ and rearrangement of factors put it in the stated form.

**Key facts.** `FABL.card_lowDegreeJuntaFourierFamily_le`, `FABL.lowDegreeJuntaCoefficientSampleCount_le_failureBits`, `FABL.lowDegreeJuntaCoefficientFailureBits_le_linearConfidence`.

**Caveat.** The formal theorem uses the specific definitions `lowDegreeJuntaFourierBatchLinearCoefficient` and `lowDegreeJuntaLinearConfidenceCoefficient`; the informal statement abbreviates these by $A$ and $L$.
