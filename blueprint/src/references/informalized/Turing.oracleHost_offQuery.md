<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleHost_offQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle host simulation away from queries

**Claim.** If the empty-oracle run does not enter the query state during the first $t$ steps, then the host run for $t$ steps agrees with the oracle run on those steps, up to the side tag recording the query-head position's sign.

**Proof.** Instantiate the general off-query simulation theorem (`Turing.oracleOffQuery`) with the host as the simulating machine and the source-tape embedding as the placement of the oracle machine's tapes. The required agreement of transitions away from the query state follows from the host's source phase: its transition is the embedded shadow simulation of the empty-oracle machine, with the same simulated state and tape actions. The assumed sign condition supplies the initial side invariant, and the hypothesis that the empty-oracle run avoids the query state supplies the theorem's no-query condition. The theorem therefore gives a final side tag for which the query-head position has the corresponding sign, and identifies the host configuration with the stable encoding of the oracle run's endpoint.

**Key facts.** `Turing.oracleOffQuery`.
