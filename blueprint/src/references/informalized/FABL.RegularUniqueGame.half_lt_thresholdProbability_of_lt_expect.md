<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.half_lt_thresholdProbability_of_lt_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Probability Lower Bound

**Claim.** For finitely many values in $[0,1]$, if their mean is strictly greater than $\epsilon\ge0$, then the fraction of values at least $\epsilon/2$ is strictly greater than $\epsilon/2$.

**Proof.** For each index, if its value is below $\epsilon/2$, it is bounded above by $\epsilon/2$. If it is at least $\epsilon/2$, it is bounded above by $\epsilon/2+1$, since every value is at most $1$. Thus pointwise each value is at most $\epsilon/2$ plus the indicator of the event that it reaches the threshold. Averaging this inequality bounds the mean by $\epsilon/2$ plus the fraction of indices reaching the threshold. Since the mean is strictly greater than $\epsilon$, rearranging gives that this fraction is strictly greater than $\epsilon/2$.
