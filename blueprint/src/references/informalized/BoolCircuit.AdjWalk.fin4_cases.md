<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.fin4_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exhaustion of Four Registers

**Claim.** If a property holds for each of the four registers numbered $0,1,2,3$, it holds for every register among the four.

**Proof.** A register among the four is an element of $\mathrm{Fin}(4)$, so its index is one of $0,1,2,3$. In each case the corresponding hypothesis gives the property.
