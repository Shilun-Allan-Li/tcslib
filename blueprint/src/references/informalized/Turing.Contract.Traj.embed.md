<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean :: Turing.Contract.Traj.embed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding a Trajectory Property

**Claim.** If a trajectory property holds for a contract on $m$ work tapes, then in the embedded contract it holds on the selected tapes and corresponding selected head positions; every unselected head position remains at its initial value.

**Proof.** Fix an embedded run and an admissible time. The run correspondence for an embedded machine (Turing.embedEmitTM_runFrom), together with the fact that selecting the embedded configuration recovers the original configuration (Turing.embedEmitCfg_select), identifies the current embedded configuration with the embedding of the original run at that time. At each selected tape, the embedded head position is exactly the corresponding original head position (Turing.embedEmitCfg_selected_pos). Thus the selected position vector is the original run's position vector, and the original trajectory hypothesis supplies the property. For any unselected tape, the embedding leaves its head position equal to the supplied initial head position (Turing.embedEmitCfg_unselected); here those supplied heads are the starting configuration's positions. This proves both parts of the conclusion.

**Key facts.** `Turing.embedEmitTM_runFrom`, `Turing.embedEmitCfg_select`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitCfg_unselected`.
