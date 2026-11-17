<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: prefixHedgeWeight_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Prefix Hedge Weight

**Claim.** Every prefix Hedge weight is strictly positive, for any learning rate, prefix of column actions, and row action.

**Proof.** The prefix Hedge weight is the exponential of a real number, namely $-\eta$ times the prefix cumulative loss. The real exponential is strictly positive at every real input, so the weight is positive.
