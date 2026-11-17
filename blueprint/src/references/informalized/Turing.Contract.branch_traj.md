<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.branch_traj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of a two-branch composition

**Claim.** Up to the first contract's endpoint time, the composed run agrees with the first machine's run embedded into the combined state space and does not halt. After the one-step transition, it follows the branch selected by the endpoint state, with that branch's states embedded in the combined space.

**Proof.** Rename the initial state to the first machine's entry state and apply the first contract's run equation and endpoint-exit property. Since the endpoint state is one of the two designated exits, the contract's cut property shows that neither exit occurs earlier. The seam-run facts then identify the composed machine with the first machine throughout the first phase, and, after the single transition, with the appropriate branch for every subsequent time (`Turing.seamCompTM₂_run_ofCfg`). The first run cannot halt at an earlier time: the run's state at the endpoint belongs to the exit set, so it is not `none`; persistence of nonhalting backwards through earlier times gives the required fact (`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`). The initial state renaming is reconciled with the original configuration by the state-map identity supplied by `Turing.Contract.mapState_const_inl_inl`. For the first-phase run identification, use the seam composition run formula under the established fact that the first exit state is not reached early (`Turing.seamCompTM_runFrom_left`).

**Key facts.** `Turing.Contract.mapState_const_inl_inl`, `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`, `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM₂_run_ofCfg`.
