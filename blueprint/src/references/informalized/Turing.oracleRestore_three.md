<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleRestore_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Step Oracle Restoration

**Claim.** For nonzero $p$, three steps from the ready configuration containing the one-letter verdict in read state produce the back configuration with bookmark $1$ when $side$ is true and $-1$ otherwise, preserving the input-head position and output.

**Proof.** The first two steps produce the back configuration at bookmark zero in depart state, with the given side recorded; at nonzero $p$ its optional side is present (`Turing.oracleRestore_cell`). One more transition moves the bookmark one cell in the direction determined by the side and changes depart to back (`Turing.oracleDepart_step`). The run-successor identity converts this final transition into the stated three-step computation (`Turing.MultiTapeTM.runFrom_succ_eq_step'`).

**Key facts.** `Turing.oracleRestore_cell`, `Turing.oracleDepart_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
