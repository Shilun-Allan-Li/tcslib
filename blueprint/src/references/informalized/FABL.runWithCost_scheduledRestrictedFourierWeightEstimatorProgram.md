<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.runWithCost_scheduledRestrictedFourierWeightEstimatorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduled Restricted Fourier Estimator Distribution

**Claim.** For the scheduled sample count, the restricted Fourier weight estimator has the distribution given by three successive independent uniform batches of cube inputs, followed by the estimator output computed from those batches, with cost given by the restricted Fourier weight estimator cost.

**Proof.** The scheduled program is the restricted Fourier weight estimator with the sample count prescribed by the schedule. Apply the distribution-and-cost formula for that estimator ( `runWithCost_restrictedFourierWeightEstimatorProgram`), which describes its run using three successive uniform batches and the deterministic output computed from them. Substituting the scheduled sample count for the general batch size gives exactly the claimed distribution and cost.

**Key facts.** `FABL.runWithCost_restrictedFourierWeightEstimatorProgram`.
