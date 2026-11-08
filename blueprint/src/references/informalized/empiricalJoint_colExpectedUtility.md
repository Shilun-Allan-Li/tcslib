<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: empiricalJoint_colExpectedUtility -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical Joint Column Utility

**Claim.** The column player's expected utility under the empirical joint distribution equals the average, over rounds, of the per-round bilinear column payoffs.

**Proof.** Apply the finite-sum identity for empirical joint distributions (empiricalJoint_sum_prob_mul) to the function assigning to each profile its column payoff. The resulting left-hand side is precisely the expected column utility under the empirical distribution, and the right-hand side is the stated time average.

**Key facts.** `empiricalJoint_sum_prob_mul`.
