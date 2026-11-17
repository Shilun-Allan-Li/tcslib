<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleErase_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatch Return Step

**Claim.** When the first-tape head and bookmark are both at a nonzero position $p$ in the return configuration, one dispatch step reaches the local configuration at the same position, preserving input-head position and output, with state changed from $(back,verdict,side)$ to $(answer,verdict,side)$.

**Proof.** The return transition erases the nonzero bookmark marker while leaving the first tape and its head at $p$, and changes the state to the corresponding answer state. The marker-step fact packages this transition: once the transition row performs the specified marker-tape action, the resulting configuration is the local configuration with the requested state and unchanged input-head position and output (`oracleMarker_step`). The nonzero assumption ensures the marker is at a position distinct from the origin, so erasing it leaves the origin marker intact. Hence the resulting configuration is exactly the one claimed.

**Key facts.** `Turing.oracleMarker_step`.
