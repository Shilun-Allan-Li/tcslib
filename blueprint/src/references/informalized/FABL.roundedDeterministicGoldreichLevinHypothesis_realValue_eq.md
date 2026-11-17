<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.roundedDeterministicGoldreichLevinHypothesis_realValue_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of the real-valued target

**Claim.** Under the sparsity and family-completeness assumptions, the rounded hypothesis's real-valued Fourier sum equals the real-valued target at every point.

**Proof.** First, every nonzero Fourier coefficient belongs to the family: exact sparsity forces its magnitude to be at least the granularity (`degreeFourierGranularity_le_abs_fourierCoeff_of_exactSparseSpectrum`), and the input threshold is at most that granularity (`exactSparseSpectrumGoldreichLevinInput_threshold_le_granularity`), so family completeness applies. Fix a point of the sign cube. By exact coefficient recovery (`roundedDeterministicGoldreichLevinHypothesis_coefficient_cast_eq`), each term of the rounded hypothesis's finite sum is the corresponding target Fourier coefficient times its character. Extending that sum from the family to all subsets adds only zero terms, since every nonzero coefficient is already in the family. The full Fourier expansion of the target (`fourier_expansion`) identifies this sum with the target's real-valued function at the fixed point. Since the point was arbitrary, the functions agree everywhere.

**Key facts.** `FABL.degreeFourierGranularity_le_abs_fourierCoeff_of_exactSparseSpectrum`, `FABL.exactSparseSpectrumGoldreichLevinInput_threshold_le_granularity`, `FABL.roundedDeterministicGoldreichLevinHypothesis_coefficient_cast_eq`, `FABL.fourier_expansion`.
