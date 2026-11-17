<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.abs_restrictedFourierWeightEstimate_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Weight Estimate Error

**Claim.** The restricted Fourier weight and its restricted Fourier weight estimate differ in absolute value by at most $\varepsilon$.

**Proof.** Insert the outer mean of the squared restricted Fourier coefficient as an intermediate quantity. The triangle inequality bounds the total error by the sum of the error from the restricted Fourier weight to this outer mean and the error from the outer mean to the estimate. The outer-mean approximation theorem bounds the first term by $\varepsilon/4$, and the estimate-to-outer-mean theorem bounds the second by $3\varepsilon/4$. Their sum is $\varepsilon$.

**Key facts.** `FABL.abs_restrictedFourierWeightOuterMean_sub_le`, `FABL.abs_restrictedFourierWeightEstimate_sub_outerMean_le`.
