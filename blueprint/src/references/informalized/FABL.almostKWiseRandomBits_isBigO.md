<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseRandomBits_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random Bits Big-O Bound

**Claim.** The number of random bits is big-O of the logarithmic scale defined for the input.

**Proof.** The pointwise estimate `almostKWiseRandomBits_le_logScale` bounds the random-bit count by twice the logarithmic scale. Since both quantities are nonnegative, the same estimate holds for their real-valued versions. Thus the constant $2$ witnesses the required big-O bound, including along the filter determined by inputs whose logarithmic scale tends to infinity.

**Key facts.** `FABL.almostKWiseRandomBits_le_logScale`.
