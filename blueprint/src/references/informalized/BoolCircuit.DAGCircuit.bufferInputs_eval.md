<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.DAGCircuit.bufferInputs_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after buffering inputs

**Claim.** Buffering the inputs according to $s$ preserves evaluation: on an assignment $x$ to the $n$ inputs, the buffered circuit evaluates to the value of $C$ on the assignment obtained by substituting the selected input values and constants.

**Proof.** First evaluate the buffer gates. The input-buffer value lemma (`inputBuffer_value`) identifies the value at buffered position $n+i$ with the substituted value assigned to original input $i$. Now apply the run-with-remapping relation (`runWith_remap_rel`) to the original gate list, using the index shift $v\mapsto n+v$. At each gate, remapping its arguments preserves its evaluation: this is the gate evaluation remapping identity (`DAGGate.eval_remap`), with the needed agreement of argument values supplied by the buffer values and the inductive relation for earlier gates. Hence the shifted output of the remapped gate list agrees with the original circuit's output on the substituted assignment. Finally, evaluating the concatenation of the buffer gates and the remapped gates is the same as running the remapped gates on the buffer's resulting values (`runWith_append`), which gives the claimed equality.

**Key facts.** `BoolCircuit.inputBuffer_value`, `BoolCircuit.DAGGate.eval_remap`, `BoolCircuit.runWith_remap_rel`, `BoolCircuit.runWith_append`.
