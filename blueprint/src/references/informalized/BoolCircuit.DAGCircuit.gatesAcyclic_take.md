<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.DAGCircuit.gatesAcyclic_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of a gate prefix

**Claim.** The list of the first $k$ gates of $C$ is acyclic: each argument of its gate at position $i$ has index less than $n+i$.

**Proof.** Split the full gate list into its first $k$ gates followed by the remaining gates. The full list is acyclic by the circuit hypothesis. The append characterization of acyclicity says that this implies acyclicity of the first part (as well as the appropriately shifted condition on the second part) (`gatesAcyclic_append`). The first part is exactly the list of the first $k$ gates, proving the claim.

**Key facts.** `BoolCircuit.gatesAcyclic_append`.
