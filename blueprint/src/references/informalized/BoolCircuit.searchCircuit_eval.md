<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.searchCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the search circuit

**Claim.** For every input assignment, the search circuit outputs exactly the list produced by sequential bit search on the corresponding bit list.

**Proof.** The search-state evaluation theorem (`searchState_values`) identifies the values at the state’s listed output vertices with the sequentially computed search bits. The search circuit uses that state’s gate list and output list, so its evaluation is precisely those listed vertex values. Applying the theorem at stage $m$ gives the asserted equality.

**Key facts.** `BoolCircuit.searchState_values`.
