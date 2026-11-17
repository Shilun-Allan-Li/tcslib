<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.mem_tribesBlockCoordinates_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Corresponding Block

**Claim.** If $i$ is a coordinate among the $sw$ positions and $(a,b)$ is its pair of block and within-block indices, then $i$ belongs to the set of coordinates in block $a$.

**Proof.** Apply the block-membership result to the pair consisting of the block index $(	ext{tribesCoord}(w,s,i)).1$ and the within-block index $(	ext{tribesCoord}(w,s,i)).2$. It says that the position corresponding to this pair belongs to that block. By the defining inverse relationship between the pair-coordinate identification and $	ext{tribesCoord}$, that position is $i$ itself. Hence $i$ belongs to the coordinates of its corresponding block.

**Key facts.** `FABL.mem_tribesBlockCoordinates`.
