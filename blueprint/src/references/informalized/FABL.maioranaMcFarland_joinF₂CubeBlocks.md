<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.maioranaMcFarland_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maiorana–McFarland formula on joined blocks

**Claim.** For $x,y\in\mathbb F_2^n$, the Maiorana–McFarland function evaluated on the joined blocks equals $\operatorname{binarySign}(\langle x,y\rangle)g(y)$.

**Proof.** The function is the product of the real sign encoding of the inner product of the two blocks and the real sign value of $g$ at the second block. Joining $(x,y)$ and then splitting it recovers those same two blocks. The joined-block identity for the encoded inner product (FABL.innerProductModTwo_joinF₂CubeBlocks) identifies the first factor as $\operatorname{binarySign}(\langle x,y\rangle)$; the second factor is $g(y)$. Multiplying gives the formula.

**Key facts.** `FABL.innerProductModTwo_joinF₂CubeBlocks`.
