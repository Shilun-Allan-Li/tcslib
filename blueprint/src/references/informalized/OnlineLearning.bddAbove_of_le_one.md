<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.bddAbove_of_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for a Function’s Range

**Claim.** If every value of $g:\iota\to\mathbb R$ is at most $1$, then the range of $g$ is bounded above.

**Proof.** Take $1$ as an upper bound. Every element of the range is $g(i)$ for some index $i$, and the hypothesis says precisely that $g(i)\le 1$. Thus every range value lies below the chosen bound.
