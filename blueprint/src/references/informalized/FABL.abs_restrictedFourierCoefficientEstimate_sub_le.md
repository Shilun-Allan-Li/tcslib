<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.abs_restrictedFourierCoefficientEstimate_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Coefficient Estimation Error

**Claim.** Under the stated assumptions, the restricted Fourier coefficient estimate differs from the corresponding restricted Fourier coefficient by at most $\varepsilon/4$.

**Proof.** View the target restricted to the free coordinates, with the complementary signs fixed, as a function $g$ on a cube of dimension $|J|$. Reindexing the free coordinates identifies the given estimator with the small-bias Fourier estimate of $g$ at the corresponding frequency, and identifies its exact Fourier coefficient with the restricted coefficient. The restriction cannot increase the Fourier $1$-norm, so $\|\widehat g\|_1\le s$. The sample distribution is biased by at most $\delta=\varepsilon/(4s)$, which is nonnegative. The small-bias Fourier estimate theorem bounds the coefficient error by $\|\widehat g\|_1\delta$, hence by $s\cdot\varepsilon/(4s)=\varepsilon/4$.

**Key facts.** `FABL.restrictedWeightFreeSample_isBiased`, `FABL.fourierOneNorm_reindexedSignRestriction_le`, `FABL.restrictedFourierCoefficientEstimate_eq_smallBiasFourierEstimate`, `FABL.fourierCoeff_reindexedSignRestriction_freeFrequencyReindex`, `FABL.abs_smallBiasFourierEstimate_sub_fourierCoeff_le`.
