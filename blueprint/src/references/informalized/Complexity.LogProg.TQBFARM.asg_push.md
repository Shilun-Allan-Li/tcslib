<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.asg_push -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pushing a Bit onto an Assignment

**Claim.** For natural numbers $k,S$ and a bit $b$, updating the assignment function at index $k$ to $b$ gives the assignment encoded by depth $k+1$ and stack value $2S+b$.

**Proof.** Compare the two functions at an arbitrary index $v$, splitting into $v<k$, $v=k$, and $v>k$. If $v<k$, the update leaves the old value in place. The exponent for the new stack is $k+1-1-v=(k-1-v)+1$, so its relevant bit is the bit of $(2S+b)/2$ at exponent $k-1-v$. Since $b$ is either $0$ or $1$, $(2S+b)/2=S$, and the depth condition remains true; this gives the old assignment value. If $v=k$, the updated function has value $b$. On the new encoding, the depth condition holds and the exponent is zero, so the tested bit is the parity of $2S+b$, which is $b$. Finally, if $v>k$, the update leaves the value unchanged, and both depth conditions are false, so the encoded assignment is false as well. The functions therefore agree at every index.
