<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitRetTM_visitedByTapeHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Positions in Return-State Simulation

**Claim.** For every tape index and time, the set of positions visited by that tape head in the return-state simulation equals the set visited by the simulation without the return state.

**Proof.** Use `Turing.embedReturn_visited`, which states that adding a distinguished return state preserves the visited-position set when the left-summand transitions reproduce the original transitions and the return state idles. For the embedded emitting machine and its return-state version, those transition identities hold by reflexivity from their definitions. Applying the lemma to the embedded initial configuration, at the specified time and tape index, yields the equality.

**Key facts.** `Turing.embedReturn_visited`.
