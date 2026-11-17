<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaLearnerProgram_cost_le_totalBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Cost of the Junta Learner

**Claim.** For any outcome in the support of the learner's run, its random-example count is at most the total random-example budget, it makes no membership queries, and its local work is at most the total work budget.

**Proof.** Apply the pathwise cost bound for the learner (`lowDegreeJuntaLearnerProgram_cost_le`), which bounds the random-example count and local work by the number of calls times their respective uniform node bounds, and gives zero membership queries. By definition, those products are exactly the total random-example and total work budgets. Substituting these definitions yields the three asserted inequalities.

**Key facts.** `FABL.lowDegreeJuntaLearnerProgram_cost_le`.
