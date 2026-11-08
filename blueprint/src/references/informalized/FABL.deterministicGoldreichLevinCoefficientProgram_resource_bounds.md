<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinCoefficientProgram_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Program Resource Bounds

**Claim.** For any target and any finite family whose size is at most the active cap, the coefficient program makes no random-example calls, makes exactly its sample count of membership queries, and uses work at most its coefficient work budget.

**Proof.** The execution formula for this program ( `DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram`) identifies its cost as the sum of three charges: the initial construction work, one batch of membership queries of size equal to the sample count, and local estimation work equal to the family size times the per-coefficient local work. The query-batch cost contributes zero random-example calls. Thus the total random-example count is zero, and the query count is the sample count, which is exactly the stated query budget. Finally, multiplying the hypothesis that the family size is at most the active cap by the nonnegative per-coefficient work gives the required bound on local estimation work; adding the construction work and query-batch work yields the coefficient work budget.

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram`.
