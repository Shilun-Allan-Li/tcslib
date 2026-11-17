<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.runWith_copies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of Copy Gates

**Claim.** If every index in $v_s$ is less than the length of $V$, executing the copy gates for those indices from $V$ appends the corresponding entries of $V$, in the order specified.

**Proof.** Induct on the list of indices. The empty list performs no steps. For a list beginning with $v$, the first copy gate appends $V.getD(v, false)$ (`copyGate_eval` and `runWith_cons`). Apply the induction hypothesis to the remaining indices, which are still below the length of $V$. Their lookups are unchanged by the appended entry: each index is below the original length, so lookup in the extended list agrees with lookup in $V$. Thus the final list is $V$ followed by the requested values in order.

**Key facts.** `BoolCircuit.copyGate_eval`, `BoolCircuit.runWith_cons`.
