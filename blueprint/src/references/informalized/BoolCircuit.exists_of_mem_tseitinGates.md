<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.exists_of_mem_tseitinGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A clause occurs in one gate encoding

**Claim.** If a clause occurs in the concatenated Tseitin encodings of a finite list of gates, then it occurs in the encoding of one gate at its corresponding index.

**Proof.** Induct on the gate list, allowing the starting variable index $z$ to vary. For the empty list there are no clauses in the concatenated encoding, so the premise cannot hold. For a list beginning with $g$, its encoding is the concatenation of the encoding of $g$ at index $z$ and the encoding of the remaining gates starting at $z+1$. A clause in this concatenation lies in one of these two parts. In the first part, choose list index $0$. In the second, apply induction to obtain an index $i$ in the tail; in the original list this is index $i+1$. Its variable index agrees with the tail's index because $z+(i+1)=z+1+i$.
