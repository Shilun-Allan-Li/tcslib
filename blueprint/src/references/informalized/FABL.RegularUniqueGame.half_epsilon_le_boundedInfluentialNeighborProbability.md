<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.half_epsilon_le_boundedInfluentialNeighborProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influential Neighbor Probability Bound

**Claim.** If a coordinate has influence greater than $\epsilon$ in the averaged neighbor function, then a uniformly chosen neighbor has its corresponding permuted coordinate among the neighbor's influential coordinates with probability at least $\epsilon/2$.

**Proof.** The hypothesis says that the averaged neighbor function has influence strictly greater than $\epsilon$ in the chosen coordinate. By the influence bound for an averaged neighbor function (\texttt{influence_boundedAveragedNeighborFunction_le}), the average, over neighbors, of the influence in the corresponding permuted coordinate is therefore also strictly greater than $\epsilon$. Each such influence is nonnegative (\texttt{influence_nonneg}) and at most $1$ (\texttt{boundedCubeFunction_influence_le_one}), since the table functions take values in $[-1,1]$. The threshold probability bound (\texttt{half_lt_thresholdProbability_of_lt_expect}) now gives that the fraction of neighbors for which this influence is at least $\epsilon/2$ is strictly greater than $\epsilon/2$. This fraction is exactly the probability in the claim, so it is in particular at least $\epsilon/2$.

**Key facts.** `FABL.RegularUniqueGame.influence_boundedAveragedNeighborFunction_le`, `FABL.influence_nonneg`, `FABL.RegularUniqueGame.boundedCubeFunction_influence_le_one`, `FABL.RegularUniqueGame.half_lt_thresholdProbability_of_lt_expect`.
