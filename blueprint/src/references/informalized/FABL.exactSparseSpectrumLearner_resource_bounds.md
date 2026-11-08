<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumLearner_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Learner Resource Bounds

**Claim.** For every $n$, Boolean function $f$, and $k$, the exact sparse spectrum learner uses no random examples, makes at most the exact sparse spectrum query budget, and performs at most the exact sparse spectrum work budget.

**Proof.** Split into the cases $n>0$ and $n=0$.

1. If $n>0$, the learner is the positive-dimensional learner built from the corresponding deterministic Goldreich–Levin input. The resource bounds for that learner give zero random examples, and bound its queries and work by the Goldreich–Levin query and work budgets (`deterministicGoldreichLevinLearner_resource_bounds`). The exact sparse spectrum query budget unfolds to the former budget. Its work budget unfolds to the sum of the rounding work and the Goldreich–Levin work budget. The positive-dimensional learner adds precisely that rounding work; the cost of mapping its output through the rounding operation leaves its query count and other costs unchanged (`DeterministicQueryProgram.runWithCost_map`). Combining these facts yields all three bounds.

2. If $n=0$, the learner makes one query to the all-one cube and returns a constant hypothesis. Its run has the cost of a single query batch (`runWithCost_zeroDimensionExactSparseSpectrumLearner`): zero random examples, one query, and one unit of work. In this case both stated budgets are one, so the required bounds follow.

**Key facts.** `FABL.deterministicGoldreichLevinLearner_resource_bounds`, `FABL.DeterministicQueryProgram.runWithCost_map`, `FABL.runWithCost_zeroDimensionExactSparseSpectrumLearner`.
