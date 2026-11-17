<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.upd_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Second Coordinate

**Claim.** For natural numbers $k,V,U,W,q$, replacing the value of the register function $r(k,V,U,W)$ at index $1$ by $q$ gives $r(k,q,U,W)$.

**Proof.** To prove equality of the updated functions, fix an index and check the four possibilities $0,1,2,3$ using `BoolCircuit.AdjWalk.fin4_cases`. The update changes the value at index $1$ to $q$ and leaves the values at the other indices equal to $k,U,W$. This agrees at every index with $r(k,q,U,W)$.

**Key facts.** `BoolCircuit.AdjWalk.fin4_cases`.
