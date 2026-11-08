<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.singletonInfluenceSampleCount_cast_le_subsqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subsquare-Root Sample-Count Bound

**Claim.** Under the stated dimension, precision, and influence hypotheses, the sample count is at most $2560(n+1)2^{E(\sqrt{\operatorname{clog}_2(n+1)}+1)}$, with $E$ as defined in the statement.

**Proof.** Apply the sample-count estimate (`fourierEstimatorSampleCount_cast_le`) to bound the count by $4$ times the failure-bit count divided by the square of the accuracy. For the confidence parameter $1/(20(n+1))$, the failure-bit count is $\operatorname{clog}_2(40(n+1))$. This is at most $40(n+1)$: the general bound $m\le 2^m$ (`nat_self_le_two_pow`) gives the required logarithmic estimate. The regime hypothesis also gives the reciprocal-accuracy estimate (`one_div_singletonInfluenceAccuracy_sq_le`), bounding the inverse accuracy squared by $16\cdot 2^{E(\sqrt{\operatorname{clog}_2(n+1)}+1)}$. Multiplying these nonnegative bounds in the sample-count estimate yields the claimed factor $4\cdot40\cdot16=2560$.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`, `FABL.nat_self_le_two_pow`, `FABL.one_div_singletonInfluenceAccuracy_sq_le`, `FABL.singletonInfluenceFailureBits_eq`.
