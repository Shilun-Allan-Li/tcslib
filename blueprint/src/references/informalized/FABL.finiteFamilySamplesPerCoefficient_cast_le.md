<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilySamplesPerCoefficient_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Samples per coefficient bound

**Claim.** The prescribed number of samples per coefficient is at most $16|\mathcal{F}|^2L/\varepsilon^2$, with $L$ the failure-bit count for the chosen confidence parameter.

**Proof.** The sample-count bound gives at most $4L$ divided by the square of the chosen coefficient accuracy (`fourierEstimatorSampleCount_cast_le`). That accuracy is $\varepsilon/(2|\mathcal{F}|)$, so its reciprocal square contributes the factor $4|\mathcal{F}|^2/\varepsilon^2$. Substituting yields the claimed bound. The nonzero family size and positive $\varepsilon$ justify the rational cancellation in this substitution.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`.
