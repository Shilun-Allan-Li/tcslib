<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.card_inter_eq_sum_memIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intersection cardinality as an indicator sum

**Claim.** For finite sets $U,J\subseteq\{0,\ldots,n-1\}$, the cardinality of their intersection, regarded as a real number, equals the sum over $i\in U$ of the indicator that $i$ belongs to $J$.

**Proof.** Filter $U$ to retain exactly those elements that also lie in $J$. This filtered set is precisely $U\cap J$, since membership in the filter means membership in both sets. Its cardinality is the sum over elements of $U$ of the indicator of membership in $J$: each retained element contributes $1$, and each other element contributes $0$.
