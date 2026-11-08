<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleTM.toOracleNDTM_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic run agrees with deterministic run

**Claim.** For any finite list of Boolean choices and starting configuration, running the nondeterministic machine using those choices gives the same configuration as running the oracle machine for the length of the list.

**Proof.** Induct on the choice list, with the starting configuration arbitrary. For the empty list, the nondeterministic run leaves the configuration as it is, and the deterministic run takes zero steps, so the results agree. For a list with first choice $b$ and tail $w$, the nondeterministic run first takes the step selected by $b$ and then runs on $w$. The selected step agrees with the deterministic oracle step (`Turing.toOracleNDTM_stepWith`). Apply the induction hypothesis to the tail starting from that common successor; its length is the number of remaining deterministic steps. This yields the claimed agreement for the full list.

**Key facts.** `Turing.toOracleNDTM_stepWith`.
