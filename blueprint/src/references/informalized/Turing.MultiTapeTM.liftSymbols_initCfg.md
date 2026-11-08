<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.MultiTapeTM.liftSymbols_initCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting the Initial Configuration

**Claim.** The initial configuration of the machine obtained by lifting a Boolean-symbol machine along an embedding $e$ on the input obtained by applying $e$ to each symbol of $x$ is the lift along $e$ of the original initial configuration on $x$.

**Proof.** Both configurations have the initial state, the same input-head position, zero work-head positions, and empty output. Their work-tape contents are also identically blank at every tape and position. The input lengths agree because applying the embedding to each symbol preserves the length of the word; hence the input-head positions are compared in the corresponding finite position types. Equality of all configuration components proves the result.
