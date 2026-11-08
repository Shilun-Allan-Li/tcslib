<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.measure_exactDegreeFourierEstimatorOutput_failure_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-degree estimator failure bound

**Claim.** When the target has Fourier degree at most $k$ and $k\ge1$, the probability that the exact-degree estimator fails to recover the target is at most $1/10$.

**Proof.** If none of the coefficient estimates lies in its bad set, every estimated coefficient is sufficiently accurate. Under the degree hypothesis and $k\ge1$, this guarantees that the estimator's sign-valued hypothesis equals the target (`FABL.exactDegreeFourierEstimatorOutput_evaluate_eq`). Thus the failure event is contained in the union of the coefficient bad events. The low-degree Fourier family is nonempty (`FABL.lowDegreeFourierFamily_nonempty`), so the finite-family failure estimate bounds the probability of that union by $1/10$ (`FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth`). Monotonicity of measure transfers this bound to the estimator's failure event.

**Key facts.** `FABL.exactDegreeFourierEstimatorOutput_evaluate_eq`, `FABL.lowDegreeFourierFamily_nonempty`, `FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth`.
