<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.relativeHammingDist_completeQuadraticFlipNeighbor_le_two_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance to a Quadratic Flip Neighbor

**Claim.** For $n\ge 2$ and a Boolean vector $w$ of length $n$, the relative Hamming distance from $w$ to its complete quadratic flip neighbor is at most $2/n$.

**Proof.** Encode $w$ as a vector $x$ over $\mathbb F_2$. The binary construction of the complete quadratic flip neighbor changes at most two coordinates, so its Hamming distance from $x$ is at most $2$ (\(\texttt{hammingDist\_completeQuadraticFlipNeighborBinary\_le\_two}\)). The coordinatewise encoding is a bijection and preserves relative Hamming distance (\(\texttt{relativeHammingDist\_pcppBoolCubeEquiv}\)), so the same bound on the numerator applies to the original Boolean vectors. Their domain has size $n$, and dividing the Hamming bound by this size gives the result.

**Key facts.** `FABL.hammingDist_completeQuadraticFlipNeighborBinary_le_two`, `FABL.relativeHammingDist_pcppBoolCubeEquiv`.
