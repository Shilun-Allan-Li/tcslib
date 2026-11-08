<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.DeterministicQueryProgram.runWithCost_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost preservation under mapping

**Claim.** Applying a function to the output of a deterministic query program changes its output to the function of the original output and leaves its learning cost unchanged.

**Proof.** Write the mapped program as a bind that takes the original output and returns it after applying the given function. The run-of-a-bind formula says that the first program runs with its original cost, and then the continuation runs with the cost of that first run added. Here the continuation is pure: it returns the transformed output and incurs zero additional cost. Thus the result is the function applied to the original output, with exactly the original cost (the run-of-a-bind formula, `runWithCost_bind`).

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_bind`.
