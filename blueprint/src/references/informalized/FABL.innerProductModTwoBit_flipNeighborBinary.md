<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductModTwoBit_flipNeighborBinary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product flip under a neighbor map

**Claim.** For $m>0$, the designated modification of the first coordinates in the two blocks changes their inner product modulo two by adding $1$.

**Proof.** Write the blocks of $z$ as $x,y$, and let $q=x_0y_0$. The modified blocks replace $x_0$ by $q+1$ and $y_0$ by $1$. The inner product of the joined modified blocks is the dot product of those blocks (`innerProductModTwoBit_joinF₂CubeBlocks`). Every coordinate other than $0$ contributes the same term as before, while the new coordinate-zero contribution is $(q+1)\cdot1=q+1$. Thus the total is the original dot product with its old coordinate-zero contribution $q$ replaced by $q+1$, which adds $1$ in $\mathbb F_2$.

**Key facts.** `FABL.innerProductModTwoBit_joinF₂CubeBlocks`.
