<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.runWithCost_exactSparseSpectrumLearningProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Learner Outcome Law

**Claim.** For any target and parameter, the outcome law of the exact sparse-spectrum learning program is the point mass at the output and cost produced by running its deterministic query program against the target.

**Proof.** The exact sparse-spectrum learning program is defined by translating the deterministic learner into a learning program. The general translation law says that running any such translated program against a target yields the point mass at the output and cost of running the original deterministic program (`runWithCost_toLearningProgram`). Applying that law to the exact sparse-spectrum learner gives the claimed equality.

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_toLearningProgram`.
