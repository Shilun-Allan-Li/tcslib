<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaNodeDecisionFromBatch_isCorrect_of_firstDetected_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Detected Frequency Gives a Relevant Coordinate

**Claim.** When the first detected frequency is a nonempty set, the batch decision correctly returns a relevant free coordinate for the restricted target.

**Proof.** Let $S$ be the nonempty frequency returned by the first-detected-frequency selector. The selector’s membership property places $S$ in the detected-frequency family. Under the accurate-estimates hypothesis, membership in that family implies that the true Fourier coefficient at $S$ is nonzero. Choose the least element $i$ of $S$, which exists because $S$ is nonempty. A nonzero Fourier coefficient at a set containing $i$ implies that $i$ is relevant to the reindexed restriction. Reindexing transfers this relevance to the corresponding free coordinate of the original restriction. The decision procedure returns exactly that relevant-coordinate decision in this case, so it is correct.

**Key facts.** `FABL.mem_detectedFrequencies_of_firstDetected_eq_some`, `FABL.fourierCoeff_ne_zero_of_mem_lowDegreeJuntaDetectedFrequencies`, `FABL.isRelevant_toReal_of_fourierCoeff_ne_zero`, `FABL.isRelevantJuntaRestriction_of_reindexed`.
