<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.rf_upd0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the First Coordinate

**Claim.** For natural numbers $i,p,t,u,a$, replacing the value at index $0$ of the register function $r(i,p,t,u)$ by $a$ gives $r(a,p,t,u)$.

**Proof.** Two functions on the four indices are equal if they agree at each index. At index $0$, the update assigns $a$; at indices $1,2,3$, it leaves the original values $p,t,u$ unchanged. These are exactly the coordinates of $r(a,p,t,u)$.
