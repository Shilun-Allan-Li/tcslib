<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.restrictSubsetTo_union_compl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction of a Union with a Disjoint Set

**Claim.** If $T\subseteq J$ and the ambient set $U$ lies in the complement of $J$, then restricting the union of the ambient copy of $T$ with $U$ back to $J$ gives $T$.

**Proof.** Check membership at an arbitrary $j\in J$. If $j$ lies in the union, it lies either in the lifted copy of $T$ or in $U$. In the first case, the lift identifies its preimage with $j$, so $j$ belongs to $T$. In the second case, the assumption $U\subseteq J^c$ contradicts $j\in J$, so this case is impossible. Conversely, each element of $T$ belongs to its ambient lift, hence to the union, and so appears in the restriction. The two sets therefore have exactly the same elements.
