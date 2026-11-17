<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.seq_traj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trajectory of Sequential Composition

**Claim.** Up to and including the first contract’s running time, the composed machine follows the first machine’s trajectory embedded in the sum of the state sets, and this trajectory never halts. After the seam step it follows the second machine from the first contract’s endpoint, with its nonhalting states relabeled by the second entry state and embedded in the sum; the relabeled endpoint has the second entry state.

**Proof.** Let $c$ be the first configuration with every state replaced by $e_1$. Its embedded relabeling is the original configuration $d$ (`Turing.Contract.mapState_const_inl`), and $c$ starts in state $e_1$ (`Turing.Contract.mapState_state`). The first contract’s run and exit properties say that its endpoint is at the prescribed time and has state $e_1'$. Since the exit set is the singleton containing that state, its cut property shows that no earlier source state is $e_1'$. The seam machine therefore agrees with the first machine through that time (`Turing.seamCompTM_runFrom_left`), after restoring the initial configuration as $d$. The first machine’s endpoint state is nonhalting, so the first-machine run is nonhalting at every earlier time as well (`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`). At the endpoint, the seam transition passes control to the second entry state; the seam-run theorem (`Turing.seamCompTM_run_ofCfg`) then identifies every subsequent composed configuration with the second-machine run from the constantly relabeled first endpoint, embedded into the sum. Finally, the endpoint belongs to the singleton exit set, so its state is $e_1'$; relabeling that state constantly gives $e_2$, and state relabeling followed by embedding yields the stated endpoint state.

**Key facts.** `Turing.Contract.mapState_const_inl`, `Turing.Contract.mapState_state`, `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`, `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM_run_ofCfg`.
