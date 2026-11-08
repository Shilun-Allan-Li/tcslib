<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.half_epsilon_le_boundedNotableNeighborProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Notable Neighbor Probability Bound

**Claim.** If a coordinate has stable influence greater than $\epsilon$ in the averaged neighbor function at parameter $1-\epsilon$, then a uniformly chosen neighbor has the corresponding permuted coordinate among its notable coordinates with probability at least $\epsilon/2$.

**Proof.** Because $0\le\epsilon\le1$, the parameter $\rho=1-\epsilon$ lies in $[0,1]$. The assumed averaged stable influence is greater than $\epsilon$. The stable influence bound for an averaged neighbor function (\texttt{stableInfluence_boundedAveragedNeighborFunction_le}) implies that the mean, over neighbors, of the stable influences in the corresponding permuted coordinates is also greater than $\epsilon$. Each of these values lies in $[0,1]$: stable influence is nonnegative for $\rho\in[0,1]$ (\texttt{stableInfluence_nonneg}), and for a function taking values in $[-1,1]$ it is at most $1$ (\texttt{boundedCubeFunction_stableInfluence_le_one}). Applying the threshold probability bound (\texttt{half_lt_thresholdProbability_of_lt_expect}) shows that the fraction of neighbors whose corresponding stable influence is at least $\epsilon/2$ is strictly greater than $\epsilon/2$. That fraction is the stated probability, hence it is at least $\epsilon/2$.

**Key facts.** `FABL.RegularUniqueGame.stableInfluence_boundedAveragedNeighborFunction_le`, `FABL.stableInfluence_nonneg`, `FABL.RegularUniqueGame.boundedCubeFunction_stableInfluence_le_one`, `FABL.RegularUniqueGame.half_lt_thresholdProbability_of_lt_expect`.
