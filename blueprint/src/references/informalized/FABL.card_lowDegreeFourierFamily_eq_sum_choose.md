<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.card_lowDegreeFourierFamily_eq_sum_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Subsets by Size

**Claim.** The number of subsets of an $n$-element coordinate set having size at most $k$ is $\sum_{j=0}^{k}\binom{n}{j}$.

**Proof.** For each size $j$ from $0$ through $k$, the family of subsets of size $j$ has cardinality $\binom{n}{j}$. Families corresponding to distinct sizes are disjoint, since a subset cannot have two different cardinalities. The low-degree family is their union, so its cardinality is the sum of these cardinalities.
