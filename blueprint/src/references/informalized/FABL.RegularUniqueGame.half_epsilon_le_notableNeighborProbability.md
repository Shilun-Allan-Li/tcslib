<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.half_epsilon_le_notableNeighborProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Notable Neighbor Probability Bound

**Claim.** If a coordinate has stable influence greater than $\epsilon$ in the averaged neighbor function at parameter $1-\epsilon$, then a uniformly chosen neighbor has the corresponding permuted coordinate among its notable coordinates with probability at least $\epsilon/2$.

**Proof.** Since $0\le\epsilon\le1$, the parameter $1-\epsilon$ belongs to $[0,1]$. The coordinate's stable influence in the averaged neighbor function exceeds $\epsilon$. By the stable influence bound for an averaged neighbor function (\texttt{stableInfluence_averagedNeighborFunction_le}), the mean of the corresponding stable influences over neighbors also exceeds $\epsilon$. For each neighbor, this stable influence is nonnegative by (\texttt{stableInfluence_nonneg}), and at most $1$ by the bounded-function stable influence estimate (\texttt{boundedCubeFunction_stableInfluence_le_one}); the Boolean function at that vertex is viewed as a bounded real-valued function. The threshold probability bound (\texttt{half_lt_thresholdProbability_of_lt_expect}) then says that the fraction of neighbors with stable influence at least $\epsilon/2$ is strictly greater than $\epsilon/2$. This fraction is the probability that the permuted coordinate is notable, proving the claimed weak lower bound.

**Key facts.** `FABL.RegularUniqueGame.stableInfluence_averagedNeighborFunction_le`, `FABL.stableInfluence_nonneg`, `FABL.RegularUniqueGame.boundedCubeFunction_stableInfluence_le_one`, `FABL.RegularUniqueGame.half_lt_thresholdProbability_of_lt_expect`.
