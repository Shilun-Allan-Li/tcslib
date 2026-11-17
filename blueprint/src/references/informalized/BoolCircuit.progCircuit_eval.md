<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a compiled program circuit

**Claim.** For valid instruction and output positions, the compiled program circuit evaluates to the corresponding bit of the block computed by running the program on the input assignment.

**Proof.** Because $i$ and $j$ satisfy the circuit's output bounds, its output vertex is the vertex assigned to instruction $i$ and output bit $j$. The established values theorem for the first $|\mathrm{prog}|$ gate stages (BoolCircuit.progGates_values) states that every such earlier instruction vertex contains the corresponding bit of the program's computed block. Applying that theorem at $i,j$ gives the desired equality; unfolding circuit evaluation identifies its left side with the value at that output vertex.

**Key facts.** `BoolCircuit.progGates_values`.
