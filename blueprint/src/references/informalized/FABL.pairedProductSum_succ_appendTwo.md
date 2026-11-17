<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedProductSum_succ_appendTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired Product Sum Recursion

**Claim.** After appending two coordinates and applying the paired-coordinate equivalence at level $k+1$, the sum of the products over all $k+1$ designated pairs is the level-$k$ sum for $x$, plus $(a+\sum_i x_i)(b+\sum_i x_i)$, with arithmetic in $\mathbb F_2$.

**Proof.** Separate the sum over the $k+1$ pairs into the first $k$ pairs and the final pair. For each of the first $k$ indices, the successor-coordinate identities show that the transformed left and right coordinates agree with those obtained from $x$ at level $k$. Thus these terms sum to the original level-$k$ paired product sum. The last-coordinate identities give $a+\sum_i x_i$ and $b+\sum_i x_i$ for the final pair, whose product is the additional term. Combining the two parts proves the formula.

**Key facts.** `FABL.pairedCoordinateEquiv_succ_left_castSucc`, `FABL.pairedCoordinateEquiv_succ_right_castSucc`, `FABL.pairedCoordinateEquiv_succ_left_last`, `FABL.pairedCoordinateEquiv_succ_right_last`.
