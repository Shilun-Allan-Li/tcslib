<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_8 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Guessed Vertex Register

**Claim.** Replacing entry $8$ of the register vector of $(p,n,a,b,s,t,tmp,st,nx)$ by $z$ gives the register vector of the state obtained by replacing $nx$ by $z$.

**Proof.** At coordinate $8$, both operations produce $z$. At each other coordinate, both preserve the original entry. Hence the resulting register vectors agree at every index.
