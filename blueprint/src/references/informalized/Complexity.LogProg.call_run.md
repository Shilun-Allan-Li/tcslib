<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Call.lean :: Complexity.LogProg.call_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of a Decider Call

**Claim.** Under the stated initialization and clean-halting hypotheses for the selected decider, the compiled machine returns to the original program configuration, with its input head restored and its control state set according to the decider's output bit. Throughout the run, register heads stay in their prescribed regions and decider work heads stay within distance $B$ of zero.

**Proof.** Let $T$ be a time witnessing the decider's clean run. The proof first chooses $T_0$, the first time the decider halts. Since a halted machine remains in its halting configuration (`runFrom_of_halt`), its configuration at $T_0$ is the same as at $T$, so it has output $[b]$, blank work tapes, and work heads at zero. The initial compiled step enters simulation mode, shifts the heads of the argument registers left by one, and leaves the other registers and the decider tapes in their prescribed initial positions. The configuration is therefore related to the decider's initial configuration by the simulation relation.

Induction on time, using the one-step simulation theorem (`sim_step`), maintains this relation until the decider halts and identifies the corresponding compiled configuration as a return state. The clean output $[b]$ determines the returned bit. During the simulated segment, the relation bounds the register heads using the segment-position bound (`regPos_box`), while the decider's own head bound follows from the hypothesis on its run. The initial setup and the return phases also preserve the required head bounds.

After halting, the compiled machine first moves the input head left and then scans it back to its initial position (`ret2_run`). It then restores the argument-register heads, one argument at a time, using the register restoration result (`regs_run`). Pairwise distinctness of the argument registers ensures these restorations do not interfere. At the end, their head positions are restored, the tapes and output agree with the original configuration, and the control state is the successor selected by $b$. The run segments are concatenated using the run-concatenation property (`runFrom_add`); the final equality follows by comparing the resulting configuration with the definition of the seam.

**Key facts.** `Complexity.LogProg.seam_eq_mkCfg`, `Complexity.LogProg.apply_moves`, `Complexity.LogProg.sim_step`, `Complexity.LogProg.regPos_box`, `Complexity.LogProg.ret2_run`, `Complexity.LogProg.regs_run`, `Complexity.LogProg.runFrom_forall_append`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_add`.
