<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: prefixPotential_eq_potential -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Potential Agreement

**Claim.** The prefix potential at round $t$ equals the Hedge potential of the induced loss sequence at time $t$.

**Proof.** Both potentials sum the corresponding weights over all row actions. For each row, the prefix Hedge weight equals the induced-loss Hedge weight (prefixHedgeWeight_eq_hedgeWeight). Replacing each summand by its equal counterpart leaves the finite sum unchanged.

**Key facts.** `prefixHedgeWeight_eq_hedgeWeight`.
