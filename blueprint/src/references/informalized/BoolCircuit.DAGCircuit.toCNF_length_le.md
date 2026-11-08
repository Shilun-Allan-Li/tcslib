<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGCircuit.toCNF_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF length bound by circuit size

**Claim.** The CNF formula obtained from the circuit has length at most $4\,\mathrm{size}(C)+1$.

**Proof.** The sharper gate-count bound gives $|C.toCNF|\le 4|C.gates|+1$ (`toCNF_length_le_gates`). Since $\mathrm{size}(C)=n+|C.gates|$ and $n\ge0$, this is at most $4\,\mathrm{size}(C)+1$.

**Key facts.** `BoolCircuit.DAGCircuit.toCNF_length_le_gates`.
