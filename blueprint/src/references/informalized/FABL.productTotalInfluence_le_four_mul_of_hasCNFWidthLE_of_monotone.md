<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.productTotalInfluence_le_four_mul_of_hasCNFWidthLE_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bound for monotone CNFs

**Claim.** A monotone sign-valued function represented by a CNF of width at most $w$ has total product influence at most $4w$ for every bias parameter $p\in(0,1)$.

**Proof.** By the influence bound from CNF width, the total influence is at most $4pw$. As $0<p<1$ and $w\ge0$, we have $4pw\le4w$. Combining these inequalities proves the stated bound.

**Key facts.** `FABL.productTotalInfluence_le_four_mul_bias_mul_of_hasCNFWidthLE_of_monotone`.
