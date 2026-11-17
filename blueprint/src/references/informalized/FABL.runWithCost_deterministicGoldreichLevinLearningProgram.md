<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.runWithCost_deterministicGoldreichLevinLearningProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic learner execution law

**Claim.** For any deterministic Goldreich–Levin input and Boolean target, running the corresponding learning program has the point-mass law at the output and cost obtained by running its deterministic query learner with that target as oracle.

**Proof.** The learning program is defined by translating the deterministic learner into a query-access learning program. The execution law of this translation is exactly the point mass at the deterministic program’s output and accumulated cost, by the execution correspondence for deterministic query programs (`runWithCost_toLearningProgram`). Applying that fact to the deterministic Goldreich–Levin learner gives the stated equality.

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_toLearningProgram`.
