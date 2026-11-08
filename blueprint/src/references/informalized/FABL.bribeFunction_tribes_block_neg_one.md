<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.bribeFunction_tribes_block_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Negative Tribes Block Forces Negative Output

**Claim.** Bribing every coordinate in block $i$ of the tribes function to $-1$ makes the function constantly $-1$.

**Proof.** Fix an input. Every coordinate of block $i$ is among the bribed coordinates, so after bribing, that entire block is the constant vector with value $-1$. The AND function on that block is consequently $-1$. The tribes function is the OR of the AND values of its blocks. Since one block has value $-1$, it is false that all block values equal $1$; by the definition of the OR function, its output is $-1$. This holds for every input.
