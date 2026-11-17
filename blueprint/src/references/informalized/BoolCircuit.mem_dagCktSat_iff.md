<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.mem_dagCktSat_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# DAG Circuit Satisfiability Membership

**Claim.** A variable-count and Boolean DAG circuit pair belongs to the set of fan-in-two satisfiable DAG circuits exactly when its circuit is fan-in-two and satisfiable.

**Proof.** By definition, the set of fan-in-two satisfiable DAG circuits contains exactly those pairs whose circuit is fan-in-two and satisfiable. Thus membership and the displayed conjunction are the same proposition, giving the equivalence directly.
