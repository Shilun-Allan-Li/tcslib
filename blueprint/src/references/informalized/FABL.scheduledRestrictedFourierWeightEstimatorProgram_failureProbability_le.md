<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Weight Failure Bound

**Claim.** The scheduled restricted Fourier weight estimator has failure probability at most $\delta$ for additive error $\varepsilon$.

**Proof.** The run of the estimator has the same law as applying the estimator output map to three independent uniform input batches, one each for $z$, $y$, and $y'$. The event that the returned rational estimate has error at least $\varepsilon$ therefore pulls back to the corresponding event for the real-valued estimator: the cast identity for the output shows these are the same failure event. For the uniform input law, its outer-measure probability agrees with its probability under the associated measure. The estimator's concentration bound then gives failure probability at most $2\exp(-m\varepsilon^2/2)$, where $m$ is the scheduled sample count; the parameter is nonnegative, and this sample count is positive. Finally, the chosen sample count ensures $2\exp(-m\varepsilon^2/2)\le\delta$, proving the result.

**Key facts.** `FABL.runWithCost_restrictedFourierWeightEstimatorProgram_uniformProduct`, `FABL.restrictedFourierWeightEstimatorOutput_cast`, `FABL.fourierEstimatorSampleCount_pos`, `FABL.positiveLearningParameter_toReal_mem_Ioc`, `FABL.measure_restrictedFourierWeightEstimatorOutput_failure_le`, `FABL.two_mul_exp_neg_fourierEstimatorSampleCount_le`.
