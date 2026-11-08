<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.sdiff_lift_union_compl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Difference After Adjoining a Disjoint Set

**Claim.** If $T\subseteq J$ and $U\subseteq J^c$, then $(T\cup U)\setminus J=U$, with $T$ understood as lifted into the ambient coordinate set.

**Proof.** Distributing set difference over the union gives $(T\cup U)\setminus J=(T\setminus J)\cup(U\setminus J)$. The lifted set $T$ lies inside $J$, so its difference with $J$ is empty. Since $U$ lies in the complement of $J$, it is disjoint from $J$, and therefore $U\setminus J=U$.

**Key facts.** `FABL.liftSubsetFrom_subset`.
