<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LargeFourierCoefficient.lean :: FABL.card_lowDegreeSubsets_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for low-degree subsets

**Claim.** For a finite set $J$ and a nonnegative integer $k$, the number of subsets of $J$ having size at most $k$ is at most $(k+1)(|J|+1)^k$.

**Proof.** By the counting formula for subsets grouped by size (`card_lowDegreeSubsets_eq_sum_choose`), the number in question is $\sum_{j=0}^k\binom{|J|}{j}$. For each $j\le k$, the binomial coefficient is at most $(|J|+1)^j$, and this in turn is at most $(|J|+1)^k$, since $|J|+1\ge1$. There are $k+1$ terms, each bounded by that same quantity, so their sum is at most $(k+1)(|J|+1)^k$.

**Key facts.** `FABL.card_lowDegreeSubsets_eq_sum_choose`.
