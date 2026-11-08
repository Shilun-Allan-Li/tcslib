<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: productDistribution_colMarginal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Column Marginal of a Product Distribution

**Claim.** For every column action $j$, the column marginal of the product distribution of $p$ and $q$ equals $q_j$.

**Proof.** By definition of the product distribution, its probability at $(i,j)$ is $p_iq_j$. Thus the column marginal is $\sum_i p_iq_j$. Factor out the constant $q_j$ to obtain $(\sum_i p_i)q_j$. Since $p$ is a mixed strategy, its weights sum to one, so this equals $q_j$.
