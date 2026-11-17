<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.length_to3SAT_toCNF_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for the 3-CNF encoding

**Claim.** For a Boolean circuit tree $C$ on $n$ variables, the number of clauses in the 3-SAT encoding of its Tseitin CNF is at most $13$ times the encoding length of $(n,C)$.

**Proof.** The 3-SAT conversion produces at most the flattened literal count of the input CNF plus twice its number of clauses (`SATTo3SAT.length_to3SAT_le`). For $C$’s Tseitin CNF, the flattened count is at most $7\,\mathrm{size}(C)$ (`BoolCircuit.toCNF_flatten_length_le`), and its clause count is at most $3\,\mathrm{size}(C)$ (`BoolCircuit.TreeCircuit.toCNF_length_le`). Thus the output has at most $(7+2\cdot3)\,\mathrm{size}(C)=13\,\mathrm{size}(C)$ clauses. Finally, the circuit size is at most the encoding length of $(n,C)$ (`BoolCircuit.size_le_length_encodeSigma`), giving the claimed bound.

**Key facts.** `SATTo3SAT.length_to3SAT_le`, `BoolCircuit.toCNF_flatten_length_le`, `BoolCircuit.TreeCircuit.toCNF_length_le`, `BoolCircuit.size_le_length_encodeSigma`.
