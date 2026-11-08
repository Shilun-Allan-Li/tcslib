<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Exec.append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution under an extended program

**Claim.** Any execution under program $P$ remains an execution with the same state, depth, and cost under the concatenated program $P++R$.

**Proof.** Induct on the execution derivation. For skip, assignments, stores, and loop rules, the same execution rule applies under the extended program because those rules do not depend on the program list. For sequences and conditional branches, apply the induction hypothesis to each subexecution and rebuild the same rule. In a call, retain the call's safety and depth conditions and apply the induction hypothesis to its body execution. Its program lookup remains valid after appending $R$: an existing entry of $P$ is still present at the same index in $P++R$ (`getElem?_append_of_eq_some`). Thus the call rule reconstructs the execution with unchanged states and cost.

**Key facts.** `Light.getElem?_append_of_eq_some`.
