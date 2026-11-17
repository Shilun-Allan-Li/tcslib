<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalEval_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpreter Administrative Step

**Claim.** Under the stated transition hypothesis, one interpreter step from the evaluation configuration produces the evaluation configuration with the prescribed control state, cursor movements, and optional state-tape update.

**Proof.** The work-tape reads in the evaluation configuration are exactly the four symbols displayed in the transition hypothesis (`Turing.universalEval_reads`). Thus that hypothesis identifies the interpreter's selected action as the administrative action. Applying it preserves the base configuration and table, moves the table and state cursors by their prescribed signs, and updates the state tape at the current cursor exactly when a write is specified. This is precisely the resulting evaluation configuration, by the administrative-action calculation (`Turing.universalAdmin_apply`).

**Key facts.** `Turing.universalEval_reads`, `Turing.universalAdmin_apply`.
