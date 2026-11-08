<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoice_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Oracle Choice Simulation

**Claim.** Given a choice word whose bits are read successively from the added tape, the deterministic oracle machine halts within $2|u|+2$ steps. Its output is the output of the nondeterministic run using $u$ if that run has halted, and otherwise that output followed by false.

**Proof.** Proceed by induction on the choice word, allowing the starting configuration and tape-head position to vary. If the word is empty, the exhaustion result says the simulator halts within two steps; it preserves the output when the simulated configuration is already halted and otherwise appends false (`oracleChoice_exhaust`). For a nonempty word $b::u$, first consider whether the simulated configuration is already halted. In that case its run with any remaining choices is unchanged (`OracleNDTM.runWith_of_halt`), and the simulator is already halted at time zero with the required output. Otherwise, the tape hypothesis says the scanned cell contains $b$. If the current state is the query state, the simulator uses two steps to perform the oracle transition with choice $b$ and advance its added-tape head; otherwise, one simulator step performs that transition and advances the head. These are the query-state and ordinary-state simulation facts (`oracleChoice_queryStep` and `oracleChoice_step`). The tape shifted to the new head position contains exactly the remaining word $u$, so apply the induction hypothesis to the resulting configuration. Adding the initial one or two steps to the inductive halting time gives a time at most $2+2|u|+2=2|b::u|+2$. The simulator's run over this combined time is the run from the intermediate configuration after the initial segment (`OracleTM.runFrom_add`), so the inductive halting and output conclusions give the result.

**Key facts.** `Turing.oracleChoice_exhaust`, `Turing.OracleNDTM.runWith_of_halt`, `Turing.oracleChoice_queryStep`, `Turing.oracleChoice_step`, `Turing.OracleTM.runFrom_add`.
