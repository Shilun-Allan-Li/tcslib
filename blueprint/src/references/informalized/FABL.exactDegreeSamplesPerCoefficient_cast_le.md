<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.exactDegreeSamplesPerCoefficient_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sample-count upper bound

**Claim.** For every $n$ and $k$, the prescribed samples per coefficient, viewed as a rational number, are at most four times the failure-bit count divided by the square of the accuracy parameter.

**Proof.** Apply the general upper bound for the estimator's sample count (FABL.fourierEstimatorSampleCount_cast_le) to the degree-$k$ accuracy and the confidence parameter assigned to the low-degree family. The definition of the prescribed per-coefficient count is exactly this sample-count function at those parameters, so substituting that definition gives the stated inequality.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`, `FABL.lowDegreeFourierFamily_nonempty`.
