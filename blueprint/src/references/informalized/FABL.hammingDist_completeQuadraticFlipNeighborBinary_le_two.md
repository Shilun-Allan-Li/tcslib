<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.hammingDist_completeQuadraticFlipNeighborBinary_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance to a quadratic flip neighbor

**Claim.** For $n\ge 2$ and $x\in\mathbb F_2^n$, the Hamming distance from $x$ to its complete quadratic flip neighbor is at most $2$.

**Proof.** Split according to the definition of the neighbor. If the complete quadratic bit of $x$ is $1$, the neighbor is $x$ itself, so the distance is zero. Otherwise, if some coordinate has derivative bit $1$, the neighbor is obtained by changing just that coordinate; the one-coordinate distance bound gives distance at most $1$, hence at most $2$ (\texttt{hammingDist\_add\_single\_le\_one}). In the remaining case, the definition changes the two coordinates $0$ and $1$. They exist because $n\ge 2$, and the two-coordinate distance bound gives distance at most $2$ (\texttt{hammingDist\_add\_two\_single\_le\_two}).

**Key facts.** `FABL.hammingDist_add_single_le_one`, `FABL.hammingDist_add_two_single_le_two`.
