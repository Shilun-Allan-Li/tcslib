<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.DAGCircuit.pairEncode_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size after pair encoding

**Claim.** The pair-encoded circuit has size $n+\operatorname{size}(C)$.

**Proof.** The pair-encoded circuit has $n$ input vertices. Its gates consist of the input buffer followed by the remapped gates of $C$. The buffer has one gate for each of the $2n+2+|r|$ wired inputs, while the remapped list has the same number of gates as $C$; using the size definition and simplifying the resulting count gives $n+\operatorname{size}(C)$.
