<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: empiricalJoint_sum_prob_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payoff Averaging Identity

**Claim.** Averaging a function against the empirical joint distribution gives the time-average of its expected value in each round.

**Proof.** Insert the definition of the empirical profile probabilities into the left-hand side. For each fixed action profile, distribute multiplication by the function value across the time sum, then take the common divisor $T$ outside the action sums. Finally, interchange the time and action sums. The result is the stated time-average of the function evaluated against each round's product weights.
