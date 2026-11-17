<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/PairwiseIndependence.lean :: FABL.pairwiseIndependentMatrix_column -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Columns of the Pairwise Independent Matrix

**Claim.** For each index $j$, the $j$th column of the matrix, viewed as a vector, equals the vector assigned to $j$ by the enumeration of nonzero vectors.

**Proof.** By definition, the matrix entry in row $i$ and column $j$ is the $i$th coordinate of the vector assigned to $j$. Thus the column and that vector have identical coordinates at every row, so they are equal.
