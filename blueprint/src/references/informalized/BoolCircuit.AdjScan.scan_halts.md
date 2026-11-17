<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.scan_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Halting of the circuit scan

**Claim.** For a finite acyclic Boolean circuit with gates in topological order, a valid task input, and an oracle returning the corresponding encoding bits, the scan machine halts within the encoding-length register bound. It returns the default answer when the target vertex is an input; otherwise it reports the specified property of the indexed gate, or false if the target is beyond the gate list.

**Proof.** Write $E$ for the circuit encoding. Its decomposition (`DAGCircuit.encode_eq`) begins with the unary encoding of the number of input vertices, followed by the encoded gate list and output encoding. Dropping the initial unary prefix and separator therefore leaves the gate-list encoding followed by the output encoding (`drop_add_of_drop`). The circuit-size bound (`DAGCircuit.size_le_length_encode`) supplies the required bound on the number of gates relative to the encoding length.

The initial configuration has all registers zero, which is precisely the assignment $(0,0,0)$ (`rg_init`). The start instruction validates the input and advances to the scan loop; validity ensures that this step reaches label $nA$ without changing the registers. One bounded machine step (`AHalt.step`) reduces the desired halting claim to the configuration at that label.

Apply the initial scan-loop result (`nloop`) with the encoding decomposition just established. If the target index is less than $n$, the scan returns the task’s default answer. Otherwise, the loop reaches the gate scan at the first gate position, with the relevant target and position registers initialized. The gate-loop result (`gloop`) then scans the encoded gate list, returning the task-specific answer for the gate at index $tv-n$ when that index exists, and false when it does not. Its register-bound hypotheses are provided by the encoding-length bound and the circuit-size estimate. Together these steps establish halting, the register bound throughout, and the stated answer.

**Key facts.** `BoolCircuit.DAGCircuit.size_le_length_encode`, `BoolCircuit.DAGCircuit.encode_eq`, `BoolCircuit.AdjScan.drop_add_of_drop`, `BoolCircuit.AdjScan.rg_init`, `Complexity.LogProg.AHalt.step`, `BoolCircuit.AdjScan.nloop`, `BoolCircuit.AdjScan.gloop`.

**Caveat.** The supplied proof invokes `gloop`, whose detailed proof and supporting facts are not included, so its scan behavior and register-bound verification cannot be independently expanded from the provided material.
