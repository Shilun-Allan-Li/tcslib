<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.getD_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entry After a List Drop

**Claim.** If dropping the first $p$ bits of $E$ yields a list beginning with $b$, then the bit of $E$ at position $p$, with out-of-range positions interpreted as false, is $b$.

**Proof.** The assumed equality says that the element at index zero of the dropped list is $b$. The list-indexing identity for a dropped list identifies that element with the element of $E$ at index $p$. Since the dropped list has an element at index zero, this index of $E$ is in range; consequently the default value in the out-of-range convention is not used, and $E.getD\,p\,false=b$.
