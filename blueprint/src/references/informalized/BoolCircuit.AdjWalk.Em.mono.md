<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.Em.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Emission

**Claim.** If a configuration satisfies the emission property for a segment with postcondition $P$, and $P$ implies $Q$, then it satisfies the same emission property with postcondition $Q$.

**Proof.** The emission property has two clauses. Its halting clause does not involve the postcondition, so it is inherited unchanged. For the reachability clause, take the endpoint configuration supplied by the original property. It satisfies $P$, hence also $Q$ by the assumed implication, and the same bounded reach witnesses the required reachability. Thus both clauses hold with postcondition $Q$.
