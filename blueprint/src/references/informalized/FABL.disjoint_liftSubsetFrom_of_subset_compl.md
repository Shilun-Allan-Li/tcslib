<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.disjoint_liftSubsetFrom_of_subset_compl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjointness from a Complementary Subset

**Claim.** If $U$ is contained in the complement of $J$, then the image in the full coordinate set of any set of coordinates in $J$ is disjoint from $U$.

**Proof.** Suppose a coordinate belonged to both the lifted image of $T$ and $U$. Every coordinate in that lifted image belongs to $J$ (`liftSubsetFrom_subset`), while membership in $U$ and the inclusion $U\subseteq J^c$ say that it does not belong to $J$. This contradiction proves disjointness.

**Key facts.** `FABL.liftSubsetFrom_subset`.
