<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Column Counter

**Claim.** Replacing entry $3$ of the register vector of $(p,n,a,b,s,t,tmp,st,nx)$ by $z$ gives the register vector of the state obtained by replacing $b$ by $z$.

**Proof.** Compare the vectors at each index from $0$ through $8$. At index $3$, both entries equal $z$. Every other coordinate retains its original value under both operations, so the vectors agree at all indices.
