<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution Under Program Extension

**Claim.** Any execution of a statement under program $P$ remains an execution with the same initial state, final state, and cost under the concatenated program $P++R$. Consequently, its cost bound and postcondition are preserved.

**Proof.** Unpack the assumed execution-with-bound property to obtain a final state, a cost, an execution under $P$, the inequality that the cost is at most $T$, and the postcondition at the final state. The program-extension theorem for executions ( `Light.Exec.append`) carries that execution to $P++R$ without changing its states or cost. Retaining the same cost inequality and postcondition gives the required result.

**Key facts.** `Light.Exec.append`.
