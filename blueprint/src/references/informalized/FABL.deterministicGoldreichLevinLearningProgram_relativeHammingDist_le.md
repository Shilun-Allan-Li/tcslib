<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinLearningProgram_relativeHammingDist_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning Error Guarantee

**Claim.** For every target whose Fourier 1-norm is at most the input bound, every hypothesis that occurs with positive probability under the deterministic Goldreich–Levin learner has relative Hamming distance from the target at most the requested learning parameter.

**Proof.** The execution theorem for the learner identifies its distribution with a point mass at the deterministic query program’s output and cost (`runWithCost_deterministicGoldreichLevinLearningProgram`). A point mass has only its distinguished outcome in its support, so the assumed supported outcome must equal that deterministic output-cost pair. The deterministic learner’s error guarantee (`deterministicGoldreichLevinLearner_relativeHammingDist_le`), applied using the Fourier-norm hypothesis, then gives the stated distance bound.

**Key facts.** `FABL.runWithCost_deterministicGoldreichLevinLearningProgram`, `FABL.deterministicGoldreichLevinLearner_relativeHammingDist_le`.
