<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LargeFourierCoefficient.lean :: FABL.card_lowDegreeSubsets_eq_sum_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting subsets by size

**Claim.** For a finite set $J$ and a nonnegative integer $k$, the number of subsets of $J$ having size at most $k$ is $\displaystyle\sum_{j=0}^{k}\binom{|J|}{j}$.

**Proof.** Group the subsets of size at most $k$ according to their cardinality $j$. The groups are disjoint, since a subset cannot have two different cardinalities. For each $j$ from $0$ through $k$, the group of subsets of cardinality $j$ has size $\binom{|J|}{j}$, by the usual counting formula for fixed-size subsets. Adding the sizes of these disjoint groups gives the stated sum.
