<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinLearner_relativeHammingDist_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Fourier Learning Error

**Claim.** For a target whose Fourier $1$-norm is at most the given bound, the deterministic Goldreich–Levin learner returns a hypothesis whose relative Hamming distance from the target is at most the learning parameter.

**Proof.** Run the first stage of the learner and let its output state be the resulting query state. The concentrated-family theorem supplies a nonempty active family whose spectrum captures all but at most half the learning parameter of the target’s Fourier mass, and whose size is within the active cap (`deterministicGoldreichLevinProgram_concentrated_family`). The coefficient-estimation guarantee says that each coefficient estimated from the subsequent samples differs from the corresponding Fourier coefficient by at most the prescribed accuracy (`deterministicGoldreichLevinHypothesis_coefficients_le`). The analytic sparse-hypothesis theorem combines this concentration and coefficient accuracy to bound the relative Hamming distance of the hypothesis formed from those estimates by the learning parameter (`relativeHammingDist_sparseFourierHypothesis_of_coefficients_le`). Finally, the run-with-cost law for sequential programs identifies the learner’s second stage as the coefficient program on the first-stage output. The active family is present and within the cap, so that stage takes the coefficient-program branch; its execution returns exactly the hypothesis made from the target’s answers to the coefficient queries (`runWithCost_bind`, `DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram`). The analytic bound therefore applies to the learner’s returned hypothesis.

**Key facts.** `FABL.deterministicGoldreichLevinProgram_concentrated_family`, `FABL.deterministicGoldreichLevinHypothesis_coefficients_le`, `FABL.relativeHammingDist_sparseFourierHypothesis_of_coefficients_le`, `FABL.DeterministicQueryProgram.runWithCost_bind`, `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram`.
