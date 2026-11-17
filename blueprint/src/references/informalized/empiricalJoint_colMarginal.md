<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: empiricalJoint_colMarginal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical Column Marginal

**Claim.** For each column action, its marginal probability under the empirical joint distribution is the time-average of the column player's weight on that action.

**Proof.** Substitute the empirical profile probabilities into the column marginal and pull the common factor $1/T$ outside the finite sum over row actions. Interchange the row and time sums. For each round, factor out the column player's weight on the fixed action; the remaining sum of the row player's weights is $1$ because its mixed strategy has total mass one. The resulting sum over rounds, divided by $T$, is the claimed marginal.
