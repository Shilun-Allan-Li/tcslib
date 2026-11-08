<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.gatesAcyclic_tabPre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of the tabulation prefix

**Claim.** The list of gates for the two Boolean constants, the entries of $z$, and the $W$ additional false constants is acyclic relative to the $n$ input vertices.

**Proof.** Take any gate in the prefix. By the characterization of members of the tabulation prefix, every such gate is a constant gate (mem_tabPre). A constant gate has no input vertices, so there is no argument whose index could violate the acyclicity bound. This applies at every position in the list.

**Key facts.** `BoolCircuit.mem_tabPre`.
