<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.measure_finiteFamilyFourierEstimatorOutput_failure_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-family estimator failure bound

**Claim.** If the target's Fourier weight outside $\mathcal H$ is at most $\varepsilon/2$, then the probability that the finite-family Fourier estimator's sign hypothesis has relative Hamming error greater than $\varepsilon$ is at most $1/10$.

**Proof.** Suppose the sample array avoids every coefficient bad set. The deterministic error estimate (`FABL.relativeHammingDist_finiteFamilyFourierEstimatorOutput_le_of_no_bad`) then bounds the relative Hamming distance by $\varepsilon$, using the assumed concentration of Fourier weight outside the family. Consequently, the event of error strictly greater than $\varepsilon$ is contained in the union of the coefficient bad sets. The family is nonempty, so the finite-family union estimate bounds the measure of that union by $1/10$ (`FABL.measure_finiteFamily_someCoefficient_bad_le_one_tenth`). Measure monotonicity gives the same bound for the failure event.

**Key facts.** `FABL.relativeHammingDist_finiteFamilyFourierEstimatorOutput_le_of_no_bad`, `FABL.measure_finiteFamily_someCoefficient_bad_le_one_tenth`.
