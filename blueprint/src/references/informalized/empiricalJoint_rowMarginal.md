<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: empiricalJoint_rowMarginal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical Row Marginal

**Claim.** For each row action, its marginal probability under the empirical joint distribution is the time-average of the row player's weight on that action.

**Proof.** Substitute the empirical profile probabilities into the row marginal, pull the common factor $1/T$ outside the sum over column actions, and interchange the column and time sums. In each round, factor out the row player's weight on the fixed action. The remaining sum of the column player's weights is $1$, since that round's column strategy has total mass one. This leaves the sum of the row weights over rounds, divided by $T$.
