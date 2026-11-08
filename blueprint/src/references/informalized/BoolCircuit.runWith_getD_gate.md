<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_getD_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value produced by a gate

**Claim.** At position $|v|+i$ in the execution result, the value is the output of gate $g_i$ evaluated after the first $i$ gates have run.

**Proof.** Split the gate list just after its $i$th gate: it consists of the first $i$ gates, then $g_i$, then the remaining tail. The length of the first part is $i$. By the execution rule for concatenated lists (`runWith_append`), the full execution is the tail execution starting from the result of executing the first part and $g_i$. The value at the designated position is already present before the tail runs, since that intermediate list has length $|v|+i+1$; later execution preserves its earlier entries (`runWith_getD_of_lt`). The value there is therefore the value appended by $g_i$, namely its evaluation on the list produced by the first $i$ gates (`runWith_getD_last`).

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_getD_of_lt`, `BoolCircuit.runWith_getD_last`.
