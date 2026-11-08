<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.mem_cktSat_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Satisfiability Membership

**Claim.** A variable-count and circuit pair belongs to the set of satisfiable circuit trees exactly when its circuit component is satisfiable.

**Proof.** The set of satisfiable circuit trees is defined by requiring that the second component of the pair be satisfiable. Membership in this set is therefore equivalent immediately to satisfiability of that component.
