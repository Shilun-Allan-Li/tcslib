<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleRestore_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle restoration at the origin

**Claim.** Running the oracle dispatch machine for three steps from the specified ready configuration at position $0$ restores the local tape content $f$ and position $0$, and reaches answer state $(\mathrm{verdict},\mathrm{true})$, preserving the input-head position and output.

**Proof.** The two-step restoration result (`oracleRestore_cell`) first carries the machine from the ready configuration to a back configuration: its state is `depart`, its first work tape has been restored to $f$, and its relevant heads are at the positions needed for the final marker step. Since the origin position is $0$, the side marker in that intermediate configuration is absent. The remaining step is supplied by the oracle marker transition (`oracleMarker_step`): at the origin it writes the origin marker and moves the machine into the requested answer state. Unfolding that transition and the definitions of the dispatch action and origin marker shows that the resulting configuration is exactly the local configuration with tape content $f$, position $0$, and unchanged input-head position and output. The three-step run is the two-step run followed by one machine step (`runFrom_succ_eq_step'`); the remaining equalities are the direct evaluation of the finite tape coordinates and their contents.

**Key facts.** `Turing.oracleRestore_cell`, `Turing.oracleMarker_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
