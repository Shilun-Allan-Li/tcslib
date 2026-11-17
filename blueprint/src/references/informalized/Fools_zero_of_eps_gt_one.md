<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: Fools_zero_of_eps_gt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-wise Independence at Large Error

**Claim.** If $\varepsilon>1$, then every distribution independent on sets of at most zero coordinates fools any set of Boolean circuits with error at most $\varepsilon$.

**Proof.** Fix such a distribution $\mu$ and a circuit $C$. Both acceptance probabilities lie between $0$ and $1$: nonnegativity follows from `Circuit.prob_nonneg`, and the upper bound follows from `Circuit.prob_le_one`. Thus each of the two differences $C.prob(\mu)-C.prob(U)$ and $C.prob(U)-C.prob(\mu)$ is at most $1$, where $U$ is uniform. By the characterization of absolute value bounds through these two inequalities, their absolute difference is at most $1$, hence at most $\varepsilon$. The independence hypothesis is not needed for this estimate.

**Key facts.** `Circuit.prob_nonneg`, `Circuit.prob_le_one`.
