<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/MaioranaMcFarlandPermutation.lean :: FABL.maioranaMcFarlandPermutation_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation construction on joined blocks

**Claim.** For $x,y\in\mathbb F_2^n$, the permutation construction evaluated on the joined blocks equals $\operatorname{binarySign}(\langle x,\pi(y)\rangle)\,g(y)$.

**Proof.** By definition, the construction first splits its input into two blocks and evaluates the binary sign of the dot product of the first block with the permutation of the second, then multiplies by the real sign value of $g$ at the second block. The joined-block map is the inverse of the block-splitting equivalence, so splitting the joined blocks $(x,y)$ recovers exactly $(x,y)$. Substitution therefore gives $\operatorname{binarySign}(\langle x,\pi(y)\rangle)\,g(y)$, as claimed.
