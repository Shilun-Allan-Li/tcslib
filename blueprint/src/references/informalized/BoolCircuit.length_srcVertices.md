<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.length_srcVertices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the source-vertex list

**Claim.** For every instruction index $i$, the list of source vertices associated with that instruction has length $m$.

**Proof.** The source-vertex list is formed by appending $m$ default input vertices to the mapped source list, then taking the first $m$ entries. The appended portion guarantees that this combined list has at least $m$ entries, so taking its first $m$ entries gives a list of length exactly $m$.
