<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_exit_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Call Machine's Exit State Is Fixed

**Claim.** Every configuration of the call machine whose control state is the designated exit state $5$ is fixed by one computation step.

**Proof.** Extract from the given configuration the two work tapes selected for the finishing machine, together with the same input-head position, output, and tape contents at those selected positions. This gives a finishing-machine configuration in state $5$. Embedding the finishing machine back into the call machine recovers the original configuration: the selected tapes and head positions agree by the selected-tape and selected-position identities (\texttt{embedEmitCfg\_selected\_tape}, \texttt{embedEmitCfg\_selected\_pos}), and all unselected tapes and positions remain unchanged by the embedding frame property (\texttt{embedEmitTM\_frame}). In state $5$, the finishing machine takes the control action that keeps state $5$, makes no tape changes, and does not move its input head; the zero-move identity (\texttt{moveInputPos\_zero}) shows its configuration is fixed after one step. Finally, the run-simulation theorem for a state embedding (\texttt{Turing.MultiTapeTM.runFrom\_mapState\_of\_agreeOn}), together with the embedding run identity (\texttt{Turing.embedEmitTM\_runFrom}), transports this one-step fixed behavior to the call machine. Since the embedded configuration is the original one, its next configuration equals itself.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`, `Turing.embedEmitTM_runFrom`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`.
