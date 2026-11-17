<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_5 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Target Register

**Claim.** Replacing entry $5$ of the register vector of $(p,n,a,b,s,t,tmp,st,nx)$ by $z$ gives the register vector of the state obtained by replacing $t$ by $z$.

**Proof.** At index $5$, both vectors have entry $z$. At every other index, neither operation changes the corresponding original entry. The vectors thus agree coordinate by coordinate.
