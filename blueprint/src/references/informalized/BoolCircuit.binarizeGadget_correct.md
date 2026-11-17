<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.binarizeGadget_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of gate binarization

**Claim.** Under the stated acyclicity, argument-index, NOT-arity, and length hypotheses, binarizing a gate extends the existing gate list and yields an acyclic circuit with an in-range output vertex computing the original gate's value. The resulting list and output depth satisfy the stated bounds, and every added gate is well formed with at most two arguments.

**Proof.** Write the gate as a kind $k$ with argument list $args$, and split into cases on its kind. If it is NOT, the argument-length hypothesis forces $args$ to contain exactly one vertex. Binarization appends the original gate to the existing list. The append preserves acyclicity because each argument index is less than $n+|gs|$ (\texttt{GatesAcyclic.snoc}). The appended gate's vertex is in range, and its value is the evaluation of that gate on the values already produced by $gs$ (\texttt{vertexValue_last}). Its single appended gate adds one to the length, within the stated cost bound. Its depth is one plus the depth of its sole argument, by the last-vertex depth formula (\texttt{vertexDepth_last}); this is bounded by one plus the maximum argument depth. The appended gate has one distinct argument, so it is well formed and has at most two inputs.

If $k$ is AND or OR, the separate AND/OR binarization result applies directly: its hypotheses are precisely the acyclicity, argument-index, and length bounds here, and it supplies the extension, correctness, size, depth, and fan-in conclusions. Together, the two cases establish the claimed specification for every gate kind.

**Key facts.** `BoolCircuit.GatesAcyclic.snoc`, `BoolCircuit.vertexValue_last`, `BoolCircuit.vertexDepth_last`, `BoolCircuit.binarizeGadget_andor`.
