<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_jeqIn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-word equality simulation

**Claim.** For an input encoded as a unary prefix followed by a canonical payload, the compiled program reaches the successor selected by whether the register's binary expansion equals that payload, preserving the valuation and output; before the endpoint there is no pending call and all work-head positions lie in $[-1,W]$.

**Proof.** Validity of the input writes it as a unary prefix paired with a canonical word $w$. Apply the plain-payload equality run lemma (`Complexity.LogProg.jeqPlain_run`) to the compiled program's phases for skipping the prefix, comparing the register word with the payload, and returning to the starting head position. This lemma supplies a finite run branching according to whether $w$ equals the register's binary expansion; at every earlier time it gives a configuration with no pending call and head position between $-1$ and the binary-word length. The compiled transition and call identities (`Complexity.LogProg.armProg_tr` and `Complexity.LogProg.armProg_call`) establish that these phase transitions are those of the specified instruction and that no call is pending. The payload extraction identity (`Complexity.LogProg.plainWord_pairEncode`) identifies the input's plain word with $w$. Reversing the equality in the run's branch condition gives precisely the stated label. The seam configuration identities (`Complexity.LogProg.xCfg_aseam_self` and `Complexity.LogProg.xCfg_aseam`) identify the endpoints with the required initial and final configurations. The run-to-simulation result (`Complexity.LogProg.simTo_of_reachesB`), using the assumed length bound, yields the claimed simulation and head-position bound.

**Key facts.** `Complexity.LogProg.jeqPlain_run`, `Complexity.LogProg.plainWord_pairEncode`, `Complexity.LogProg.simTo_of_reachesB`.
