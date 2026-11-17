<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: ZeroSumGame.toLossSeq_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of induced losses

**Claim.** The loss sequence induced by a zero-sum game with payoffs in $[0,1]$ is valid: each loss lies in $[0,1]$.

**Proof.** Fix a round $t$ and row action $i$. The corresponding loss is $1-G.payoff(i,colResponse(t))$. Since the payoff is at most $1$, subtracting it from $1$ gives a nonnegative loss. Since the payoff is nonnegative, the loss is at most $1$. Thus every loss lies in the required interval.
