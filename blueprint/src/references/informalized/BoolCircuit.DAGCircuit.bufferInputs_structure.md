<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.DAGCircuit.bufferInputs_structure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Structure of the buffered circuit

**Claim.** The buffered circuit is well formed and has fan-in at most two, and its size is $n+\mathrm{size}(C)$.

**Proof.** Consider a gate in the buffered circuit. If it comes from the input buffer, it is either a one-argument input gate or a constant gate; both have distinct arguments, satisfy the negation condition, and have at most two arguments. The constant-gate case is covered by `constGate_faninTwo`. If it comes from the remapped original gate list, remapping the arguments by addition of $n$ preserves their distinctness, and it does not change either the gate kind or the argument count. Thus the original well-formedness and fan-in assumptions give the same properties for every remapped gate. Consequently every gate in the buffered circuit has fan-in at most two and is well formed, establishing both circuit properties. Its gate list consists of $m$ buffer gates followed by one remapped gate for each of the $|G|$ original gates, so its size is $n+m+|G|=n+\mathrm{size}(C)$.

**Key facts.** `BoolCircuit.constGate_faninTwo`.
