<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.roundedDeterministicGoldreichLevinHypothesis_coefficient_cast_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact recovery of rounded coefficients

**Claim.** Under the sparsity assumption, rounding each empirical coefficient to granularity $2(1/2)^{k+1}$ recovers the corresponding real Fourier coefficient of the target.

**Proof.** The sparsity hypothesis bounds the target's Fourier $1$-norm by the Fourier bound of the exact sparse-spectrum input (`fourierOneNorm_toReal_le_of_spectralSparsity_le`). For the chosen subset $U$, exact sparse-spectrum sparsity also makes its Fourier coefficient an integer multiple of the granularity (`isFourierGranular_toReal_of_exactSparseSpectrum`); write it as $zg_{k+1}$. The deterministic small-bias estimate differs from the true coefficient by at most the input's error (`abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le`), and that error is strictly less than half the granularity (`exactSparseSpectrumGoldreichLevinInput_coefficientEpsilon_lt_half_granularity`). The rational empirical estimate, when viewed as real, is exactly the corresponding real small-bias estimate (`rationalSmallBiasFourierEstimate_cast`). Thus the empirical value lies within half a granularity of $zg_{k+1}$. The half-granularity rounding result (`roundToDegreeFourierGranularity_eq_of_close`) rounds it to that multiple, which is the true Fourier coefficient.

**Key facts.** `FABL.fourierOneNorm_toReal_le_of_spectralSparsity_le`, `FABL.isFourierGranular_toReal_of_exactSparseSpectrumSparsity`, `FABL.abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le`, `FABL.exactSparseSpectrumGoldreichLevinInput_coefficientEpsilon_lt_half_granularity`, `FABL.rationalSmallBiasFourierEstimate_cast`, `FABL.roundToDegreeFourierGranularity_eq_of_close`.
