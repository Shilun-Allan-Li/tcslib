<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.unflattenBinaryMatrix_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of matrix unflattening

**Claim.** For every $n$ and vectors $x,y\in(\mathbb F_2)^{n^2}$, unflattening their coordinatewise sum yields the sum of their associated $n\times n$ matrices.

**Proof.** Both sides are functions on pairs of row and column indices, so compare their entries at arbitrary $i,j$. The entry on the left is the $(i,j)$ coordinate of $x+y$, which is $x_{(i,j)}+y_{(i,j)}$. This is exactly the sum of the $(i,j)$ entries of the two unflattened matrices, proving equality entrywise.
