<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.toBinary_maxFanin_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in bound after binary conversion

**Claim.** The maximum fan-in of the binary conversion of every circuit tree is at most $2$.

**Proof.** Proceed by structural induction. A literal’s conversion is still a literal, with maximum fan-in zero. At a node, the conversion combines the converted children. The combination bound (combine_maxFanin) says its maximum fan-in is at most the larger of $2$ and the maximum fan-in among those children. The induction hypotheses bound every converted child’s maximum fan-in by $2$; the list maximum estimate (maxFaninL_map_le) therefore bounds their maximum by $2$. The node conversion consequently has maximum fan-in at most $2$.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.combine_maxFanin`, `BoolCircuit.maxFaninL_map_le`.
