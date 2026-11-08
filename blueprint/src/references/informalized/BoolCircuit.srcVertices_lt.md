<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.srcVertices_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Source list vertices precede the instruction block

**Claim.** Every vertex in the truncated source list for instruction $i$ is strictly below the base of that instruction block.

**Proof.** Take a vertex in the truncated list. It is also in the list before truncation, which is the mapped source list followed by $m$ copies of $n$. If it comes from the mapped source list, it is the assigned vertex of some source, so the preceding source-vertex bound (`srcVertex_lt`) applies. If it comes from the appended copies, it equals $n$; the base is at least $n+2$, so it too is strictly below the base.

**Key facts.** `BoolCircuit.srcVertex_lt`.
