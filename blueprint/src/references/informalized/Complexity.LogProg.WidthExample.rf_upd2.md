<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.rf_upd2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Third Coordinate

**Claim.** For natural numbers $i,p,t,u,a$, replacing the value at index $2$ of the register function $r(i,p,t,u)$ by $a$ gives $r(i,p,a,u)$.

**Proof.** Compare the two functions at each of the four indices. The update leaves indices $0$ and $1$ unchanged, assigns $a$ at index $2$, and leaves index $3$ unchanged. The resulting values are $i,p,a,u$, as claimed.
