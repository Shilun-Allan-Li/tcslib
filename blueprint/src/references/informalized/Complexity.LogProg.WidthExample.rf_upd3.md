<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.rf_upd3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Fourth Coordinate

**Claim.** For natural numbers $i,p,t,u,a$, replacing the value at index $3$ of $r(i,p,t,u)$ by $a$ gives $r(i,p,t,a)$.

**Proof.** To prove equality of the two functions, fix an index in $	ext{Fin }4$ and check its possible values. At indices $0,1,2$, the update leaves the original values unchanged; at index $3$, it replaces $u$ by $a$. These are exactly the four values of $r(i,p,t,a)$.
