<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: pureVsPayoff_empiricalStrategy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payoff Against an Empirical Strategy

**Claim.** The payoff of a fixed row action against the empirical column strategy equals the average payoff over the observed sequence of column actions.

**Proof.** By the definition of the empirical strategy, each column action receives its number of occurrences in the sequence, divided by $T$. Thus the payoff is the sum over columns of the payoff at that column times its occurrence count, divided by $T$. Distribute the payoff across the occurrence sum, move the common denominator outside the column sum, and interchange the finite sums. For each time $t$, the indicator sum over columns has exactly one nonzero term, at the played action $a_t$, so it equals $G(i,a_t)$. The resulting expression is the stated average.
