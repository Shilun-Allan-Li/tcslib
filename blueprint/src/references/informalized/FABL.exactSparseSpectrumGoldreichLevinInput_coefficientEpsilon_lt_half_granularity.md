<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumGoldreichLevinInput_coefficientEpsilon_lt_half_granularity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Accuracy Bound

**Claim.** For natural numbers $n$ and $k$ with $n>0$, the coefficient accuracy of the exact sparse-spectrum Goldreich–Levin input is strictly less than half the degree-$(k+1)$ Fourier granularity.

**Proof.** Let $I$ be the exact sparse-spectrum input. Its learning parameter is the degree-$(k+1)$ coefficient accuracy (by `exactSparseSpectrumGoldreichLevinInput_learningParameter`). The coefficient-accuracy formula (`DeterministicGoldreichLevinInput.coefficientInput_epsilon`) expresses its coefficient error as the learning parameter divided by twice the active cap. The active cap is positive (`goldreichLevinActiveCap_pos`), so, being an integer, it is at least $1$; consequently twice the cap is at least $2$. The coefficient accuracy is therefore at most one half of the learning parameter. The degree-$(k+1)$ coefficient accuracy is one quarter of the corresponding granularity, as follows directly from its definition. Since that granularity is positive (`degreeFourierGranularity_pos`), one quarter of it is strictly less than one half. Combining these bounds proves the claim.

**Key facts.** `FABL.exactSparseSpectrumGoldreichLevinInput_learningParameter`, `FABL.DeterministicGoldreichLevinInput.coefficientInput_epsilon`, `FABL.goldreichLevinActiveCap_pos`, `FABL.degreeFourierGranularity_pos`.
