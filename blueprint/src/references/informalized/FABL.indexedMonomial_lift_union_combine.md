<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.indexedMonomial_lift_union_combine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial factorization across a split

**Claim.** For coordinate sets lifted from the coordinates in $J$ and outside $J$, the monomial of their union at the combined assignment factors as the product of the two corresponding indexed monomials.

**Proof.** The two lifted coordinate sets are disjoint (`disjoint_liftFreeFrequency_liftFixedFrequency`), so the product over their union factors into the product over each set. Reindex each product along its lift from the corresponding subtype. By the definition of the combined assignment, its restriction to coordinates in $J$ is $y$ and its restriction to coordinates outside $J$ is $z$. Thus the two reindexed products are precisely the indexed monomials of $y$ on $S$ and $z$ on $T$, respectively.

**Key facts.** `FABL.disjoint_liftFreeFrequency_liftFixedFrequency`.
