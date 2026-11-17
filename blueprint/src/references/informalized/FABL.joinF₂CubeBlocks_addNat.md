<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.joinF₂CubeBlocks_addNat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Block Coordinate

**Claim.** For $x,y\in\mathbb F_2^n$, the concatenation of $x$ and $y$ has value $y_i$ at the second-block position corresponding to $i$.

**Proof.** The index `Fin.addNat i n` is the same second-block position as `Fin.natAdd n i`. The second-block coordinate formula for concatenation (`FABL.joinF₂CubeBlocks_natAdd`) gives the value $y_i$ at that position, proving the claim.

**Key facts.** `FABL.joinF₂CubeBlocks_natAdd`.
