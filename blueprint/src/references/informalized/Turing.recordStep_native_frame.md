<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_native_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Frame Preservation

**Claim.** If every transition of $R$ only moves the input head and changes its state, then every finite run leaves all work-tape contents, work-head positions, and the output unchanged.

**Proof.** Induct on the number of steps. At time zero, all three claimed equalities hold by reflexivity. For the successor step, express the run at time $t+1$ as one step from the configuration reached at time $t$, using `runFrom_succ_eq_step'`. If that configuration is halted, `step_of_halt` says it remains unchanged, so the induction hypothesis gives the result. If it has state $q$, the transition hypothesis identifies its action as an input-only move with successor state determined by `next`. The one-step characterization `step_of_inputMoveAction` shows that this changes only the state and input-head position. Hence the work tapes, work-head positions, and output remain those at time $t$, and the induction hypothesis identifies them with their initial values.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_of_halt`, `Turing.step_of_inputMoveAction`.
