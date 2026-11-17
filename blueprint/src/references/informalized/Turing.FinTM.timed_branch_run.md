<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.timed_branch_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evolution in the selected branch phase

**Claim.** Running the timed conditional controller for $t$ steps from the branch-phase configuration yields the branch-phase configuration formed from the two-branch machine's configuration after $t$ steps, while the extra tape block and captured bit remain unchanged.

**Proof.** Use the one-step commutation principle for runs (`Turing.MultiTapeTM.runFrom_comm_of_step`): it suffices to show that one controller step from an encoded configuration is the encoding of one branch-machine step. If the branch-machine state is halting, both machines leave their configurations unchanged, so the identity follows directly. Otherwise, the encoded state is the controller's branch phase carrying the same branch state. The input symbol is unchanged by the encoding, and the work-tape symbols read from the branch's tape block are exactly those of the original configuration. Thus the controller consults the same transition as the branch machine. The action laws for adding fixed tape blocks (`Turing.FinTM.leftCfg_apply` and `Turing.FinTM.rightCfg_apply`) show that applying this transition updates the branch portion exactly as the branch machine does, while preserving the auxiliary tapes and heads. This proves the one-step commutation, and therefore the equality after any number $t$ of steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.FinTM.leftCfg_apply`, `Turing.FinTM.rightCfg_apply`.
