<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/FiniteMinimax.lean :: avg_min_le_min_avg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimum of averages bounds average minimum

**Claim.** The average, over rounds, of the pointwise minimum is at most the minimum over choices of the average.

**Proof.** Fix any choice $j_0$. In each round $t$, the minimum of $f(t,j)$ over $j$ is at most $f(t,j_0)$. Summing these inequalities over $t$ and multiplying by the positive factor $1/T$ gives that the average of the minima is at most the average of $f(t,j_0)$. Since this holds for every $j_0$, the left side is at most the infimum of those averages, which is the stated minimum.
