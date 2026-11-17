<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.TreeCircuit.toDAG_fanoutSpec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout properties of the DAG translation

**Claim.** For the gate list $G$ and output index $r$ of the DAG translation of $c$, fanout is zero on the original gate-index interval, at most one for every index at least $n$, and zero at the output when $r\ge n$. The output index is either below $n$ or at least $n+|G|$. Every index in the stated later interval other than the output has fanout exactly one.

**Proof.** Apply the compilation fanout theorem (BoolCircuit.compileTree_fanout) to $c$, starting from the empty gate list, which is acyclic. It yields an extension list of gates and all the stated fanout and output-index conditions for that compilation. Since the initial list is empty, the compiled gate list is exactly this extension. Thus those conditions hold for the DAG translation's gates and output.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.compileTree_fanout`.
