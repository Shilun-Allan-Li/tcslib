<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_7 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Step Counter

**Claim.** Replacing entry $7$ of the register vector of $(p,n,a,b,s,t,tmp,st,nx)$ by $z$ gives the register vector of the state obtained by replacing $st$ by $z$.

**Proof.** Both resulting vectors have value $z$ at coordinate $7$. Every other coordinate is unchanged by each operation, so the vectors have the same value at every index.
