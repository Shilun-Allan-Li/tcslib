<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progVertex_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Program Output Vertex Bound

**Claim.** For an instruction index $i$ within the program and an output-bit index $j<w$, the vertex assigned to bit $j$ of instruction $i$ is strictly below the program base immediately after instruction $i$.

**Proof.** Because $j<w$, it indexes one of the gadgets associated with the kind of instruction $i$. The embedding-offset bound says that this gadget's offset is strictly less than the total width of all gadgets for that instruction (`embedOffset_lt`). The base immediately after instruction $i$ is the current base plus that instruction kind's width (`progBase_succ`). The assigned vertex is the current base plus the offset, so the offset bound gives the desired strict inequality.

**Key facts.** `BoolCircuit.embedOffset_lt`, `BoolCircuit.progBase_succ`.
