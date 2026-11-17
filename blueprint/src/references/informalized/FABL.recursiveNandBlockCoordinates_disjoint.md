<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandBlockCoordinates_disjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Recursive NAND Blocks

**Claim.** For every natural number $d$, the two sets of coordinates occupied by the two blocks of size $2^d$ in a vector with $2^{d+1}$ coordinates are disjoint.

**Proof.** Suppose a coordinate $k$ belonged to both blocks. Then it would be the image of some within-block coordinates $j_0$ and $j_1$ under the embeddings for block indices $0$ and $1$. Removing the common finite-index cast, the two images under the product-coordinate equivalence would be equal. Since that equivalence is injective, their first components would have to agree, giving $0=1$ in $	ext{Fin }2$, a contradiction. Hence the blocks have no coordinate in common.
