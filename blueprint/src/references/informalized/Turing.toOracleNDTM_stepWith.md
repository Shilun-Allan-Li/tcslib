<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.toOracleNDTM_stepWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic–Nondeterministic Step Agreement

**Claim.** For every configuration, choice bit, and oracle, the nondeterministic machine obtained from a deterministic oracle machine makes the same step as the original machine.

**Proof.** Unfold both step definitions and split on the configuration’s state. If it is halting, both machines leave the configuration unchanged. If it is an ordinary state, the converted machine uses the transition function of the original machine, so both apply the same action to the same configuration. If it is the query state, both test the same query string for membership in the same oracle language and set the successor state to the corresponding yes or no state, leaving all other configuration data unchanged. Thus the resulting configurations agree in every case.
