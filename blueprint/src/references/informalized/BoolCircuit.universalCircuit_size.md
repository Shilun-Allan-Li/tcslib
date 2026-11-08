<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.universalCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Universal Circuit

**Claim.** For a Boolean function $f$ on assignments to $n$ variables, the universal circuit for $f$ has size $(n+1)$ times the number of assignments on which $f$ is true, plus one.

**Proof.** The circuit is an OR node with one minterm for each assignment on which $f$ is true. Each minterm has size $n+1$ (`minterm_size`), and the sum of the sizes of mapped list entries is the list length times their common size (`foldr_size_map`). The list of minterms therefore contributes $(n+1)$ times the number of such assignments; the OR node contributes one more. The list length equals the cardinality of the filtered set, yielding the stated formula.

**Key facts.** `BoolCircuit.minterm_size`, `BoolCircuit.foldr_size_map`.
