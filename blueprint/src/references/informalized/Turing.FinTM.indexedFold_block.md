<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.indexedFold_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed Transduction of a Complete Block

**Claim.** Sweeping through the indexed cells for $0,\ldots,k-1$ in increasing order gives, at each index, the first component of its local-rule value computed from the initial table, and returns the corresponding ordered list of second components.

**Proof.** Apply the duplicate-free indexed transduction result (`indexedFold`) to the list of all indices in the finite interval from $0$ to $k-1$. This list has no repetitions (`List.nodup_finRange k`), and every index in its domain occurs in it (`List.mem_finRange`). Consequently the conditional table assignment in that result always selects the local-rule value, with no indices left unchanged. Its output list is exactly the ordered block of indexed second components.

**Key facts.** `Turing.FinTM.indexedFold`.
