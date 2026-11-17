<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.inputBlock_tribesCoord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a coordinate from its block

**Claim.** If $(a,b)$ is the pair corresponding to coordinate $i$, then the $b$th entry of block $a$ equals $x_i$.

**Proof.** By definition, the $b$th entry of block $a$ is the value of $x$ at the coordinate paired with $(a,b)$. Here $(a,b)$ is the inverse image of $i$ under the coordinate-pairing equivalence. Applying the equivalence to its inverse image returns $i$, so this entry is $x_i$.
