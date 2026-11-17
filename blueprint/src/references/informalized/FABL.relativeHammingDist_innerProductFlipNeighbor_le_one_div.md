<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.relativeHammingDist_innerProductFlipNeighbor_le_one_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance to the Inner-Product Flip Neighbor

**Claim.** For positive $m$ and a Boolean string $w$ of length $2m$, the relative Hamming distance from $w$ to its inner-product flip neighbor is at most $1/m$.

**Proof.** Encode the string as a vector $z$ over $\mathbb F_2$. The binary neighbor changes at most two coordinates, so the Hamming distance from $z$ to that neighbor is at most $2$ (\(\texttt{hammingDist\_innerProductFlipNeighborBinary\_le\_two}\)). The encoding carries the Boolean neighbor to this binary neighbor (\(\texttt{pcppBoolCubeEquiv\_innerProductFlipNeighbor}\)) and preserves relative Hamming distance (\(\texttt{relativeHammingDist\_pcppBoolCubeEquiv}\)). The original domain has $2m$ elements, so the distance is at most $2/(2m)=1/m$.

**Key facts.** `FABL.hammingDist_innerProductFlipNeighborBinary_le_two`, `FABL.pcppBoolCubeEquiv_innerProductFlipNeighbor`, `FABL.relativeHammingDist_pcppBoolCubeEquiv`.
