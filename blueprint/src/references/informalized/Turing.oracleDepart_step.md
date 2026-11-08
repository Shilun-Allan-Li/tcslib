<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleDepart_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Departure Step

**Claim.** From the departure configuration with bookmark $p$ and first-tape head at $p$, one step reaches the corresponding return phase, moving that head to $p+1$ for true side and to $p-1$ for false side, while preserving the input-head position and output.

**Proof.** The transition in the departure phase leaves the input head and output unchanged, leaves the tape contents unchanged, and moves the first-tape head by the sign determined by $side$: one cell to the right when true and one cell to the left when false. It also changes the state to the corresponding return phase with the same verdict and side. Substituting these prescribed movements and the unchanged configuration data gives the stated configuration.
