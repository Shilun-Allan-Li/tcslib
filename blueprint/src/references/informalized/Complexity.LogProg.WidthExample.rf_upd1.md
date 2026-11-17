<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.rf_upd1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Second Coordinate

**Claim.** For natural numbers $i,p,t,u,a$, replacing the value at index $1$ of the register function $r(i,p,t,u)$ by $a$ gives $r(i,a,t,u)$.

**Proof.** Compare the two functions at each of the four indices. The update leaves index $0$ unchanged, assigns $a$ at index $1$, and leaves indices $2$ and $3$ unchanged. The resulting values are $i,a,t,u$, as claimed.
