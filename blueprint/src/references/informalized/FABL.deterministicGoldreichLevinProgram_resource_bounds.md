<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinProgram_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Resource bounds for the deterministic program

**Claim.** The deterministic Goldreich–Levin program uses no random examples, and its query count and local work are bounded by the stated list query and list work budgets.

**Proof.** Apply the run-up-to resource bounds at the full dimension. They give zero random examples, at most the number of stages times the stage query budget in queries, and at most that many stages times the stage work budget in local work. The full program adds the restricted-weight construction work as an initial tick, which contributes no queries or random examples and adds exactly that amount to local work. Since the number of stages is the input dimension, the query estimate is the list query budget, and adding the initial construction cost gives the list work budget.

**Key facts.** `FABL.deterministicGoldreichLevinRunUpToProgram_randomExamples`, `FABL.deterministicGoldreichLevinRunUpToProgram_queries_le`, `FABL.deterministicGoldreichLevinRunUpToProgram_work_le`.
