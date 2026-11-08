<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.innerProductModTwoBit_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product of joined blocks

**Claim.** For vectors $x,y\in\mathbb F_2^n$, the inner product modulo two of their concatenation is their dot product in $\mathbb F_2$.

**Proof.** The block decomposition of the concatenated vector recovers exactly the pair $(x,y)$. By the definition of the inner product modulo two on a two-block vector, its value is the dot product of the recovered blocks. Therefore it is the dot product of $x$ and $y$.
