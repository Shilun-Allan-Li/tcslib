<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.isCorrelationImmune_of_no_lowDegreeJuntaDetection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlation Immunity from No Detected Frequency

**Claim.** Under the stated accuracy, junta dependence, and no-detection hypotheses, every nonempty Fourier coefficient of the reindexed restricted target on a set of size at most $\lfloor 3k/4\rfloor$ is zero; hence the restriction is correlation immune up to that cutoff.

**Proof.** To establish correlation immunity, take any nonempty frequency set $S$ whose size is at most the cutoff. The Fourier-coefficient vanishing result `fourierCoeff_eq_zero_of_no_lowDegreeJuntaDetection` applies to the given target, coordinate sets, fixed assignment, sample batch, and hypotheses: the junta has size at most $k$, the target depends only on that junta, all prescribed estimates are accurate, and the detector returns none. It therefore says that the Fourier coefficient of the reindexed restriction at $S$ is zero. This holds for every such $S$, which is the defining condition for correlation immunity at the cutoff.

**Key facts.** `FABL.fourierCoeff_eq_zero_of_no_lowDegreeJuntaDetection`.
