<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.tabCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Tabulated Circuit

**Claim.** For every program and output indices, the tabulated circuit has size $n+2+|z|+W(|P|+1)$, where $W$ is the tabulation width.

**Proof.** Circuit size is the number of input vertices plus the number of gates. The gate list is the concatenation of the preliminary gates and the program gates. The preliminary list has length $2+|z|+W$ (BoolCircuit.length_tabPre), and the program list has length $W|P|$ (BoolCircuit.length_tabProgGates). Adding these lengths to $n$ and rearranging gives $n+2+|z|+W(|P|+1)$.

**Key facts.** `BoolCircuit.length_tabPre`, `BoolCircuit.length_tabProgGates`.
