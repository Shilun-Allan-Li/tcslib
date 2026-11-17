<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Row Counter

**Claim.** Replacing entry $2$ of the register vector of $(p,n,a,b,s,t,tmp,st,nx)$ by $z$ gives the register vector of the state obtained by replacing $a$ by $z$.

**Proof.** Compare the two vectors at each index from $0$ through $8$. At index $2$, both entries are $z$. At each of the other indices, the function update leaves the original coordinate unchanged, and replacing $a$ leaves the corresponding state entry unchanged. Hence the vectors agree coordinate by coordinate.
