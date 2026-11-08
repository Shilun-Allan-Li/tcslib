<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamReleaseTM_runFrom_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seam-Release Machine Run

**Claim.** From a configuration in state $a$, every positive-time run of the seam-release machine from the left-renamed configuration equals the original machine's run with its state embedded on the right.

**Proof.** Write the positive time as $t+1$. The run-at-successor identity (`MultiTapeTM.runFrom_succ_eq_step`) expresses the seam-release run as a $t$-step run from its first step. Since the initial configuration is in state $a$, the fresh-state step identity (`seamReleaseTM_step_fresh`) identifies that first step with the original machine's first step, embedded on the right. Apply the run-at-successor identity to the original run as well. Finally, the step-commutation theorem (`MultiTapeTM.runFrom_comm_of_step`), using that every right-embedded configuration steps in the seam-release machine exactly as the original step followed by right embedding (`seamReleaseTM_step_inr`), carries this equality through the remaining $t$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.seamReleaseTM_step_fresh`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.seamReleaseTM_step_inr`.
