<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: prefixPotential_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Prefix Potential

**Claim.** If there is at least one row action, the prefix potential is strictly positive.

**Proof.** The prefix potential is the finite sum of the prefix Hedge weights over all row actions. Each summand is strictly positive (prefixHedgeWeight_pos), and the set of row actions is nonempty because $M\ge 1$. A finite sum of positive terms over a nonempty finite set is positive.

**Key facts.** `prefixHedgeWeight_pos`.
