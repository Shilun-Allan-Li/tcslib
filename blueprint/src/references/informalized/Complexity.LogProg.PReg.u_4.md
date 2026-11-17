<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_4 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Source Register

**Claim.** Replacing entry $4$ of the register vector of $(p,n,a,b,s,t,tmp,st,nx)$ by $z$ gives the register vector of the state obtained by replacing $s$ by $z$.

**Proof.** Check the entries coordinate by coordinate. At index $4$, each operation places $z$; at every other index, both operations preserve the original entry. Therefore the resulting register vectors are equal.
