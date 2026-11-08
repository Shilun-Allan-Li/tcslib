<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.upd_2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Third Coordinate

**Claim.** For natural numbers $k,V,U,W,q$, replacing the value of the register function $r(k,V,U,W)$ at index $2$ by $q$ gives $r(k,V,q,W)$.

**Proof.** Prove equality of the updated functions by fixing an index and checking the four cases $0,1,2,3$, which exhaust the domain by `BoolCircuit.AdjWalk.fin4_cases`. At index $2$, the update supplies $q$; at the other indices the values remain $k,V,W$. Hence the updated function agrees everywhere with $r(k,V,q,W)$.

**Key facts.** `BoolCircuit.AdjWalk.fin4_cases`.
