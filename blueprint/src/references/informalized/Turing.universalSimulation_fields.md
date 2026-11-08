<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalSimulation_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting and Output at Simulation Checkpoints

**Claim.** At every universal simulation checkpoint, the interpreter configuration is halted exactly when the source configuration is halted, and its output equals the source output.

**Proof.** By definition, the checkpoint copies the source state into the interpreter state using the map that sends every state to the interpreter's main state and preserves absence of a state. Therefore the interpreter state is absent exactly when the source state is absent. The checkpoint definition also assigns the source output directly to the interpreter configuration, so their outputs are equal.
