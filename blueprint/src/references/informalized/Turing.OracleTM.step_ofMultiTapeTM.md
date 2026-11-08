<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.step_ofMultiTapeTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step of an Embedded Multi-Tape Machine

**Claim.** For a configuration embedded into the oracle-machine configuration space, one step of the oracle machine constructed from a multi-tape machine agrees with embedding the result of one step of that multi-tape machine.

**Proof.** If the original configuration is halted, its embedding is also halted, so both machines leave it unchanged. Otherwise its state is some $q$, and the embedded state is the corresponding left-summand state. This cannot be the oracle machine's query state, which lies in the right summand, so the oracle transition branch is used. The embedded configuration presents the same input symbol as the original (`Turing.Cfg.embedOracle_inputSymbol`) and the same scanned symbols on the original work tapes (`Turing.Cfg.embedOracle_workTapeSymbols`). Hence the oracle machine's transition is the embedded extension of the original transition. Applying this action to the embedded configuration yields the embedding of the original action's result (`Turing.Cfg.embedOracle_apply`), as required.

**Key facts.** `Turing.Cfg.embedOracle_inputSymbol`, `Turing.Cfg.embedOracle_workTapeSymbols`, `Turing.Cfg.embedOracle_apply`.
