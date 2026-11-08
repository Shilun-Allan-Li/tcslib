<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.bddBelow_of_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Range Lower Bound

**Claim.** If $g(i)\ge 0$ for every index $i$, then the range of $g$ is bounded below.

**Proof.** Take $0$ as a lower bound. Every element of the range has the form $g(i)$ for some index $i$, and the hypothesis gives $0\le g(i)$.
