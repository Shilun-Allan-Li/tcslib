<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isSignValued_innerProductModTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner-Product Sign Is Sign-Valued

**Claim.** The inner-product sign function has absolute value $1$ at every input pair.

**Proof.** Fix an input in the doubled cube and split it into its two blocks $x$ and $y$. Reassemble these blocks to recover the original input, then express the function on this joined input as the binary sign of the dot product of the blocks (\(\texttt{innerProductModTwo\_joinF₂CubeBlocks}\)). The dot product belongs to $\mathbb F_2$, so it is either $0$ or $1$. Its binary sign is consequently $1$ or $-1$, respectively, and has absolute value $1$.

**Key facts.** `FABL.innerProductModTwo_joinF₂CubeBlocks`.
