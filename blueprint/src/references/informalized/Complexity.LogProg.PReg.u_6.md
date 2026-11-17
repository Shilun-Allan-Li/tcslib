<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_6 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Scratch Register

**Claim.** Replacing entry $6$ of the register vector of $(p,n,a,b,s,t,tmp,st,nx)$ by $z$ gives the register vector of the state obtained by replacing $tmp$ by $z$.

**Proof.** At coordinate $6$, both operations give the value $z$. For each other coordinate, the vector update and the state-field replacement leave the original value in place. This proves equality of the two vectors.
