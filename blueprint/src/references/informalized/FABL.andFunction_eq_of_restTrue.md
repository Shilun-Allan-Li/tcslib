<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.andFunction_eq_of_restTrue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# AND on a nearly negative block

**Claim.** If every coordinate in the chosen block except the selected coordinate is $-1$, then the block AND equals the selected sign $x_i$.

**Proof.** Let $(j,o)$ be the block and within-block coordinate corresponding to $i$. The block entry at offset $o$ is exactly $x_i$ (the coordinate identification `FABL.inputBlock_tribesCoord`). If all entries of the block are $-1$, this entry is $-1$, so the AND output and $x_i$ agree. Otherwise, suppose for contradiction that $x_i=-1$. The entry at offset $o$ is then also $-1$, while the hypothesis makes every other entry $-1$; this would make every block entry $-1$, contrary to the case assumption. Since $x_i$ is a sign, it must therefore be $1$, and in this case the AND output is also $1$.

**Key facts.** `FABL.inputBlock_tribesCoord`.
