<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/FiniteMinimax.lean :: regret_to_payoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Converting loss regret to payoff

**Claim.** In the finite zero-sum game, a cumulative loss-regret bound of $R$ implies that the row player's cumulative expected payoff is at least the best fixed row action's cumulative payoff minus $R$.

**Proof.** 1. For each round, the row distribution sums to one. Therefore its expected loss, weighted by $1-A_{i,j_t}$, is $1$ minus its expected payoff. Summing over the $T$ rounds makes the learner's total loss equal to $T$ minus its cumulative expected payoff.

2. For any fixed row action, its cumulative loss is likewise $T$ minus its cumulative payoff. Taking the infimum of these losses over the finite set of row actions gives $T$ minus the supremum of their cumulative payoffs. This follows because subtracting a quantity from the same constant reverses the order; finiteness ensures the extrema are bounded.

3. Substitute these two expressions into the assumed regret inequality. The constants $T$ cancel, leaving that the best fixed row payoff minus the learner's cumulative expected payoff is at most $R$. Rearranging gives the claimed payoff guarantee.
