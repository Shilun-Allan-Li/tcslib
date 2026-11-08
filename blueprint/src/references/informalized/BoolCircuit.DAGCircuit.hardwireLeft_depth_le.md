<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwireLeft_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth after hardwiring left inputs

**Claim.** If $C$ has $m+n$ input bits and the first $m$ are fixed by an assignment $y$, then the circuit obtained by hardwiring those inputs has depth at most $\mathrm{depth}(C)+1$.

**Proof.** The proof compares the depth computation on the remapped original gates with the original depth computation, allowing an additive error of one at each corresponding vertex (`runWith_remap_rel`). The initial depth list for the hardwired circuit consists of $n$ zeros for the remaining inputs followed by $m$ ones for the newly inserted constant gates. Every entry of this list is at most one (`getD_le_one`), so at each old input vertex its depth is bounded by the corresponding original input depth plus one. The permutation of vertex indices preserves the order of gate outputs (`leftPerm_gate`) and sends every relevant vertex index into the range of the new initial list or gate outputs (`leftPerm_lt`). For each remapped gate, the gate-level depth comparison follows from the fact that remapping its arguments increases their available depths by at most one (`DAGGate.depth_remap_le`). Applying the run comparison to the original acyclic gate list therefore bounds the depth at the remapped output by the original output depth plus one. Finally, the inserted constant gates contribute precisely the appended block of depth-one vertices (`runWith_depth_constGates`), and processing the appended remapped gates after them follows the list concatenation rule for circuit evaluation (`runWith_append`). Together these identify the output depth of the hardwired circuit and yield the claimed inequality.

**Key facts.** `BoolCircuit.DAGCircuit.leftPerm_lt`, `BoolCircuit.DAGGate.depth_remap_le`, `BoolCircuit.getD_le_one`, `BoolCircuit.runWith_append`, `BoolCircuit.runWith_depth_constGates`, `BoolCircuit.runWith_remap_rel`.
