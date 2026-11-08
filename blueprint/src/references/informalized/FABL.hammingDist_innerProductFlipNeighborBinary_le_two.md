<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.hammingDist_innerProductFlipNeighborBinary_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance to an inner-product neighbor

**Claim.** For $m\ge 1$ and $z=(x,y)$ with $x,y\in\mathbb F_2^m$, the neighbor formed by replacing the zeroth coordinate of $x$ with $x_0y_0+1$ and that of $y$ with $1$ differs from $z$ in at most two coordinates.

**Proof.** Write $z$ in its two length-$m$ blocks, say $(x,y)$. The block representation is invertible, so $z$ is the concatenation of these blocks, and the neighbor is the concatenation of the blocks with only their zeroth entries updated. In the first block, every coordinate other than $0$ agrees before and after the update; the same is true in the second block. Hence any differing coordinate in the full vector must be either the zeroth position in the first block or the zeroth position in the second block. The differing-coordinate set is therefore contained in a two-element set, so its size is at most two.

**Key facts.** `FABL.joinF₂CubeBlocks_castAdd`, `FABL.joinF₂CubeBlocks_natAdd`.
