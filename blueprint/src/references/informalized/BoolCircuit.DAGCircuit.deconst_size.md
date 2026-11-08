<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.deconst_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size increase from eliminating constants

**Claim.** If $n>0$, eliminating constants increases the circuit size by exactly three.

**Proof.** The transformation adds a prefix of three gates and replaces each original gate by one transformed gate. Thus its gate count is $|G|+3$. Since the input count remains $n$, the new size is $n+(|G|+3)=(n+|G|)+3$, which is the original size plus three.
