<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.upd_3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Fourth Coordinate

**Claim.** For natural numbers $k,V,U,W,q$, replacing coordinate $3$ of $r(k,V,U,W)$ by $q$ yields $r(k,V,U,q)$.

**Proof.** It suffices to show that the two functions agree at every index. Fix an index in $\mathrm{Fin}(4)$ and split into its four possible values. At indices $0,1,2$, the update leaves the original values $k,V,U$ unchanged; at index $3$, it replaces $W$ by $q$. These are exactly the values of $r(k,V,U,q)$, so the functions agree pointwise.

**Key facts.** `BoolCircuit.AdjWalk.fin4_cases`.
