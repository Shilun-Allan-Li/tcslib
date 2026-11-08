<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.args_length_le_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate argument count bounded by circuit size

**Claim.** If every gate has distinct arguments and each NOT gate has exactly one argument, then each gate has at most $\mathrm{size}(C)$ arguments.

**Proof.** Fix a gate and choose its position $i$ in the gate list. Since its arguments are distinct, the number of arguments equals the cardinality of the set of its arguments. Acyclicity says every argument has index less than $n+i$, hence less than $n+\mathrm{length}(C.\mathrm{gates})=\mathrm{size}(C)$. Thus the set of arguments is contained in the set of indices below the circuit size, whose cardinality is $\mathrm{size}(C)$. This proves the bound.
