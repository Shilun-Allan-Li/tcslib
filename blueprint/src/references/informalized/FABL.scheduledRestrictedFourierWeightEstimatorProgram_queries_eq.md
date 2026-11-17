<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.scheduledRestrictedFourierWeightEstimatorProgram_queries_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduled Query Count

**Claim.** Every cost outcome in the support of the scheduled estimator has query count equal to twice its sample count.

**Proof.** The cost theorem for the estimator identifies every supported outcome's cost with the estimator's specified cost at sample size $m$. Its query component is $2m$, since each of the $m$ observations makes two target queries. Substituting the scheduled sample size $m=\text{fourierEstimatorSampleCount}(\varepsilon,\delta)$ gives the asserted equality.

**Key facts.** `FABL.restrictedFourierWeightEstimatorProgram_cost_eq`.
