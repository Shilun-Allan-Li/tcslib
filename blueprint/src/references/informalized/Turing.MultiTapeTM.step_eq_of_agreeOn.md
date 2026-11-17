<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.MultiTapeTM.step_eq_of_agreeOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal Steps Under Transition Agreement

**Claim.** If two machines' transition actions agree at every state in $Q$ for every scanned input and work-tape symbols, then from any configuration whose state, when present, belongs to $Q$, their next configurations are equal.

**Proof.** Split according to whether the configuration is halted. If its state is empty, a halted configuration is fixed by one step (`Turing.MultiTapeTM.step_of_halt`), so both machines leave it unchanged. If its state is some $q$, the assumption on the configuration places $q$ in $Q$. The machines therefore have equal transition actions at $q$ for the symbols scanned in this configuration. Applying the same action to the same configuration yields the same next configuration.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`.
