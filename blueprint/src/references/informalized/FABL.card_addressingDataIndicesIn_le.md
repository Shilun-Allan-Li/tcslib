<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.card_addressingDataIndicesIn_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Data indices in a coordinate set

**Claim.** For a set $J$ of coordinates among the $m+2^m$ coordinates, the number of indices $j<2^m$ whose associated data coordinate lies in $J$ is at most $|J|$.

**Proof.** Map each counted index $j$ to its associated data coordinate. By definition of the counted set, every image lies in $J$. This coordinate map is injective: it is obtained by placing $j$ in the right summand of the finite-sum equivalence, whose inverse recovers that summand and its index. Therefore the image has the same cardinality as the counted indices. Since the image is contained in $J$, its cardinality is at most $|J|.
