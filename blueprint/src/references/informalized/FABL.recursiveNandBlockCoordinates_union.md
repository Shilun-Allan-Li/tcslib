<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandBlockCoordinates_union -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Union of Recursive Block Coordinates

**Claim.** For every natural number $d$, the coordinates in the two blocks of size $2^d$ that partition a block of size $2^{d+1}$ have union equal to the full set of $2^{d+1}$ coordinates.

**Proof.** Take any coordinate $k$ in the larger block. Under the product-coordinate equivalence, its corresponding pair consists of a block index $i$ in $	ext{Fin }2$ and a within-block coordinate $j$ in $	ext{Fin }(2^d)$. The embedding of the block indexed by $i$ sends $j$ back to $k$. Since $i$ is either $0$ or $1$, the coordinate $k$ belongs to one of the two block-coordinate sets. Thus their union contains every coordinate, and so equals the full set.
