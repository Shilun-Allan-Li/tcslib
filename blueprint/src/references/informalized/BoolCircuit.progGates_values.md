<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progGates_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values computed by program gates

**Claim.** After constructing the first $i$ stages of gates, every input and the two constant vertices have their prescribed values, and each earlier instruction's output vertices contain the corresponding computed block bits.

**Proof.** Proceed by induction on the number $i$ of completed stages. At stage zero, the gate list consists of the two constant gates; running them appends false and true to the input values. This gives the input and constant claims, while there are no earlier instruction outputs to check.

For the successor stage, assume the claims hold after $i$ stages and let $V$ be the resulting value list. Its length is the base offset for stage $i$, by the gate-length formula (BoolCircuit.length_progGates) together with the length formula for running gates (BoolCircuit.length_runWith). The next stage appends the embedded gadgets for instruction $i$ (BoolCircuit.runWith_append). Since these gadgets only append values, every vertex below $|V|$ retains its old value (BoolCircuit.runWith_getD_of_lt). Thus inputs, constants, and all earlier instruction outputs remain correct.

It remains to check the new instruction's output vertices. The source vertices map, under $V$, to the instruction's source bits evaluated from the full program blocks. For input sources this follows from the induction hypothesis on input values; for constants it follows from the two constant values; and for earlier-block sources it follows from the induction hypothesis on those blocks. Well-formedness ensures every source is of one of these valid forms. The source list has length $m$, so its values can be supplied as an $m$-bit assignment to the gadget (BoolCircuit.length_srcVertices and BoolCircuit.ofFn_getD_eq_map). The embedded-gadget evaluation theorem (BoolCircuit.runWith_embedAll_getD), followed by the fact that a gadget computes its defining function (BoolCircuit.gadget_eval), identifies the new vertex for bit $j$ with the $j$th output of $F$ applied to the evaluated sources. The program-step equation (BoolCircuit.progBlocks_getD) identifies this with bit $j$ of the block at instruction $i$.

These facts establish the invariant at stage $i+1$. For the statement about earlier outputs, an index below $i+1$ is either below $i$, when the preservation argument applies, or equals $i$, when the new-output argument applies. The location bounds use that the new output vertices lie below the next base offset (BoolCircuit.progVertex_lt), that base offsets are monotone (BoolCircuit.progBase_mono), and that source vertices lie within the current stage's base offset (BoolCircuit.srcVertices_lt).

**Key facts.** `BoolCircuit.runWith_eval_constGates`, `BoolCircuit.length_runWith`, `BoolCircuit.length_progGates`, `BoolCircuit.runWith_append`, `BoolCircuit.runWith_getD_of_lt`, `BoolCircuit.srcVertices_lt`, `BoolCircuit.length_srcVertices`, `BoolCircuit.ofFn_getD_eq_map`, `BoolCircuit.runWith_embedAll_getD`, `BoolCircuit.gadget_eval`, `BoolCircuit.progBlocks_getD`, `BoolCircuit.progVertex_lt`, `BoolCircuit.progBase_mono`.
