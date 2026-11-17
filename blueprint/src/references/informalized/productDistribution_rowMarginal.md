<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: productDistribution_rowMarginal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row Marginal of a Product Distribution

**Claim.** For every row action $i$, the row marginal of the product distribution of $p$ and $q$ equals $p_i$.

**Proof.** By definition of the product distribution, its probability at $(i,j)$ is $p_iq_j$. Hence the row marginal is $\sum_j p_iq_j$. Factor out $p_i$ to get $p_i(\sum_j q_j)$. The weights of the mixed strategy $q$ sum to one, so this equals $p_i$.
