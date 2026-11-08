<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.instrOps_exec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of Instruction Operations

**Claim.** Executing the operations associated with a template yields the encoding of its evaluated source-copy gates, followed by the encoding of its fixed gates shifted by the evaluated base expression.

**Proof.** Expand the instruction-operation list into its two concatenated parts: one operation block for each template source, followed by one block for each fixed gate. The encoding of a mapped list splits into the corresponding concatenation of gate encodings (`gbits_map`), and flattening across the two lists preserves this order.

For each source expression, the operations encode an AND gate with that expression as its single argument. The fact that executing this operation block produces the encoding of the gate whose argument is the expression’s value is `flatMap_exec_sgOps`. Applying it to every source gives the encoding of the copy gates at the evaluated source positions.

For each fixed gate, the same execution fact gives its encoding with every argument replaced by the value of the corresponding linear expression. The base expression contributes a common offset to those argument values: evaluating the linear expression consisting of the base register terms plus the fixed offset equals the evaluated base expression plus that offset. Hence these gates are exactly the fixed gates shifted by the evaluated base expression. Combining the two blocks proves the claimed equality.

**Key facts.** `Complexity.UTab.gbits_map`, `Complexity.UTab.flatMap_exec_sgOps`.
