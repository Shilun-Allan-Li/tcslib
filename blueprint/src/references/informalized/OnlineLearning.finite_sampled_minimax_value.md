<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.finite_sampled_minimax_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimax Equality for a Sampled Game

**Claim.** The finite game obtained by evaluating the payoff on the given finite row and column samples has equal lower and upper values.

**Proof.** The hypotheses on the sampled payoffs make the sampled game a zero-sum game with payoffs in $[0,1]$. Apply the finite minimax equality theorem to this game; it yields equality of its lower and upper values (OnlineLearning.finite_minimax_value).

**Key facts.** `OnlineLearning.finite_minimax_value`.

**Caveat.** The supplied informal statement is about Sion's theorem, while the formal statement and proof concern minimax equality for the sampled finite game.
