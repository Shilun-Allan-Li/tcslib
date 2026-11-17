<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.runWith_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Halted Configuration Remains Unchanged

**Claim.** If $c$ is in the halting state, then running on any finite choice sequence from $c$ leaves $c$ unchanged.

**Proof.** Induct on the choice sequence. The empty sequence leaves the configuration unchanged by definition. For a sequence $b::w$, expand the run into one step followed by the run on $w$ (`Turing.OracleNDTM.runWith_cons`). A halted configuration is fixed by a single step (`Turing.OracleNDTM.stepWith_of_halt`), so the remaining run starts again from $c$; the induction hypothesis says it also leaves $c$ unchanged.

**Key facts.** `Turing.OracleNDTM.runWith_cons`, `Turing.OracleNDTM.stepWith_of_halt`.
