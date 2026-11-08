<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.restrictedFourierWeightEstimatorOutput_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator Output as an Average

**Claim.** The rational restricted Fourier weight estimator output equals $\frac{1}{m}\sum_{i=0}^{m-1}r_i$, where $r_i$ is the rational restricted Fourier weight observation formed from the $i$th inputs and their target labels.

**Proof.** The batch-output list is the list, in index order, of the rational input-derived observations (FABL.restrictedFourierWeightObservationBatchOutput_eq_ofFn). The estimator is defined as the sum of this list divided by $m$. The sum of a list formed from a function on $\mathrm{Fin}(m)$ is the finite sum of that function's values, so the output is precisely the stated average.

**Key facts.** `FABL.restrictedFourierWeightObservationBatchOutput_eq_ofFn`.
