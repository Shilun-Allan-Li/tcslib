<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinQueryRunUpTo_outerFailureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin failure bound

**Claim.** For every $k\le n$, the outer probability that the query algorithm run through stage $k$ has an inaccurate estimate in its trace is at most $k$ times the stage failure budget.

**Proof.** Induct on $k$. At stage zero, the initial trace is empty, so failure has probability zero. For the step to $k+1$, apply the outer-probability bound for a bind: the probability of eventual failure is at most the probability of failure already present plus the worst continuation failure probability when the current state has no failure (`outerEventProbability_bind_le_add`). The induction hypothesis bounds the first term by $k$ stage budgets. If the current state has no active family, the continuation returns it unchanged. If it has an active family exceeding the cap, the algorithm likewise stops; its existing trace has no failure. In the remaining case, one stage is run. Its failure probability equals the probability that the appended estimate records contain an inaccurate record (`outerEventProbability_goldreichLevinStageStepProgram_failure`), and is bounded by the stage estimator theorem by the number of candidates times the call confidence (`goldreichLevinStageEstimateProgram_outerFailureProbability_le`). The candidate count is at most twice the active-set size, which is at most twice the cap (`card_goldreichLevinCandidates_le_two_mul`). This yields the stage failure budget. Adding it to the induction bound proves the result for $k+1$.

**Key facts.** `FABL.LearningProgram.outerEventProbability_bind_le_add`, `FABL.outerEventProbability_goldreichLevinStageStepProgram_failure`, `FABL.goldreichLevinStageEstimateProgram_outerFailureProbability_le`, `FABL.card_goldreichLevinCandidates_le_two_mul`.
