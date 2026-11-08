<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumGoldreichLevinInput_threshold_le_granularity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold and Fourier Granularity

**Claim.** For natural numbers $n$ and $k$ with $n>0$, the threshold of the exact sparse-spectrum Goldreich–Levin input is at most the degree-$(k+1)$ Fourier granularity.

**Proof.** Let $I$ denote the input and let $M$ be its family-size bound. Its learning parameter is the degree-$(k+1)$ coefficient accuracy (`exactSparseSpectrumGoldreichLevinInput_learningParameter`), whose value is one quarter of the degree-$(k+1)$ granularity. The threshold formula (`DeterministicGoldreichLevinInput.threshold_cast`) gives the threshold as the learning parameter divided by $4M$. Positivity of the family-size bound (`DeterministicGoldreichLevinInput.familySizeBound_pos`) implies $M\geq 1$, hence $4M\geq 1$. The granularity is positive (`degreeFourierGranularity_pos`), so dividing its quarter by $4M$ gives a quantity at most that quarter, and therefore at most the granularity itself.

**Key facts.** `FABL.exactSparseSpectrumGoldreichLevinInput_learningParameter`, `FABL.DeterministicGoldreichLevinInput.familySizeBound_pos`, `FABL.DeterministicGoldreichLevinInput.threshold_cast`, `FABL.degreeFourierGranularity_pos`.
