<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.step_plainEmptyOracle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-oracle step agreement

**Claim.** For every configuration, stepping the plain machine obtained by eliminating the oracle with the empty language gives the same successor as stepping the oracle machine with the empty language.

**Proof.** Split according to whether the configuration is halted. If it is halted, both machines leave it unchanged. Otherwise, consider whether its state is the query state. In the query state, the empty language contains no query string, so the oracle step selects the negative-answer state and preserves all other fields. The plain machine's corresponding transition has the same effect, as seen by comparing the configuration fields. In any other state, both machines use the same transition action, and therefore produce the same configuration.
