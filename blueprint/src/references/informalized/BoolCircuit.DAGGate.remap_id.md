<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGGate.remap_id -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity remapping of a gate

**Claim.** For every Boolean circuit gate $g$, remapping its argument indices by the identity function leaves $g$ unchanged.

**Proof.** A gate consists of its kind and its list of argument indices. Remapping by the identity preserves the kind and maps each argument index to itself, so the resulting gate is exactly $g$.
