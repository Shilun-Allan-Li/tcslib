<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaFourierScanWork_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Scan Work Bound

**Claim.** The rational cast of the Fourier scan work is at most the stated product involving the family-size bound, failure-bit count, accuracy, and cutoff.

**Proof.** First cast the family-size estimate `card_lowDegreeJuntaFourierFamily_le` to the rationals; this bounds the family size by $(r+1)(n+1)^r$. The sample-count cast estimate `fourierEstimatorSampleCount_cast_le` bounds the rational sample count by $4$ times the failure-bit count divided by the square of the accuracy. Replacing the two factors in the scan-work product by these upper bounds preserves the inequality, since all factors are nonnegative. Multiplying by the remaining cutoff factor gives the claimed bound.

**Key facts.** `FABL.card_lowDegreeJuntaFourierFamily_le`, `FABL.fourierEstimatorSampleCount_cast_le`.
