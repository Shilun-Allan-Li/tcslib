<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.queriedFiniteFamilySamplesPerCoefficient_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sample Count Bound

**Claim.** The sample count per coefficient, viewed as a rational number, is at most $16|\mathcal F|^2L/\varepsilon^2$, where $L$ is the failure-bit count for confidence parameter $\delta/|\mathcal F|$.

**Proof.** Apply the sample-count ceiling estimate (`fourierEstimatorSampleCount_cast_le`) at the coefficient accuracy and the per-coefficient confidence selected for the whole family. It bounds the sample count by $4L$ divided by the square of that accuracy. By definition, the selected accuracy is $\varepsilon/(2|\mathcal F|)$; substituting this gives $4L/(\varepsilon/(2|\mathcal F|))^2=16|\mathcal F|^2L/\varepsilon^2$. The nonempty family and positive accuracy ensure the denominators used in this simplification are nonzero.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`.
