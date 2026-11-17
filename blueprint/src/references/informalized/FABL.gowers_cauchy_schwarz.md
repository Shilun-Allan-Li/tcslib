<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowers_cauchy_schwarz -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gowers Cauchy–Schwarz inequality

**Claim.** For a positive integer $k$, the Gowers inner product of a family $F$ is at most the product of the order-$k$ Gowers norms of its member functions.

**Proof.** Apply the bound for the Gowers inner product after lifting a family along an embedding, using the identity embedding of the $k$ coordinates. This lift is just $F$ itself. The resulting bound is by the corresponding Cauchy–Schwarz bound; the identity expressing that bound as the product of the order-$k$ Gowers norms gives the stated inequality.

**Key facts.** `FABL.gowersInner_liftFamilyAlong_le_csBound`, `FABL.gowersCSBound_eq_prod_norm`.
