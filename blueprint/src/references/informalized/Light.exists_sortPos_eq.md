<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.exists_sortPos_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Every rank occurs as a sorting position

**Claim.** For every $q<N$, there is an index $j<N$ whose sorting position is $q$.

**Proof.** Consider the sorting-position map on the finite set of indices below $N$. Its values also lie below $N$, by the sorting-position bound (`sortPos_lt`). The map is injective by the injectivity theorem for sorting positions (`eq_of_sortPos_eq`). An injective map from this finite set to itself is surjective, since domain and codomain have the same cardinality. Thus the given rank $q<N$ is the sorting position of some index $j<N$.

**Key facts.** `Light.sortPos_lt`, `Light.eq_of_sortPos_eq`.
