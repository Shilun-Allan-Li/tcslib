<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductFlipNeighbor_isInnerProductModTwoOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Neighboring Word Has Inner Product One

**Claim.** If the original block inner product is not $1$ in $\mathbb F_2$, then the neighboring word constructed in the statement has block inner product $1$.

**Proof.** Translate the Boolean word into its pair of blocks over $\mathbb F_2$ using the Boolean-to-field equivalence. The original inner product is not $1$; since $\mathbb F_2$ has only the elements $0$ and $1$, it must be $0$. The neighbor construction changes the inner product by adding $1$ (`FABL.innerProductModTwoBit_flipNeighborBinary`), so its new inner product is $0+1=1$. The Boolean-to-field equivalence carries the constructed neighboring word to exactly this binary neighbor (`FABL.pcppBoolCubeEquiv_innerProductFlipNeighbor`), proving the claim for the original Boolean-word formulation.

**Key facts.** `FABL.pcppBoolCubeEquiv_innerProductFlipNeighbor`, `FABL.innerProductModTwoBit_flipNeighborBinary`.
