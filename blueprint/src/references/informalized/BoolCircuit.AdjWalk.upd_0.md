<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.upd_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the First Coordinate

**Claim.** For natural numbers $k,V,U,W,q$, replacing the value of the register function $r(k,V,U,W)$ at index $0$ by $q$ gives $r(q,V,U,W)$.

**Proof.** Equality of the updated functions is proved by extensionality: fix an index and check the four possible values $0,1,2,3$ using `BoolCircuit.AdjWalk.fin4_cases`. At index $0$, the update gives $q$; at the other indices it leaves the original values $V,U,W$ unchanged. These are precisely the values of $r(q,V,U,W)$.

**Key facts.** `BoolCircuit.AdjWalk.fin4_cases`.
