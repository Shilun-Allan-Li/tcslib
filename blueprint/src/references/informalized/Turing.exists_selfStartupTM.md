<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SelfUniversal.lean :: Turing.exists_selfStartupTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-Description Startup

**Claim.** For every effective code system for one-work-tape binary machines, there is a finite-state deterministic machine with three additional work tapes that, for each code and every binary input, reaches the specified startup configuration after a code-dependent fixed number of steps, without reaching its exit state earlier or producing output, and with bounded space.

**Proof.** Apply the general startup theorem for machines with $k$ work tapes to the case $k=1$ and to the effective code system obtained from the given code system (`exists_selfStartupTMK`). It provides a machine whose tape at index $1$ contains the decoded machine's transition table and whose tape at index $2$ contains its initial state in unary, shifted by two cells. The identification of the decoded machine in the derived code system is given by `EffectiveMachineCode.toK_machine`. Reindexing the three work tapes shows that these are exactly the required tapes; all remaining tapes are blank. The general theorem already supplies the fixed startup time, exit-state avoidance, empty output, and space bound, which are preserved by this reindexing.

**Key facts.** `Turing.exists_selfStartupTMK`, `Turing.EffectiveMachineCode.toK_machine`.
