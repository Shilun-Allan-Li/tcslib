<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_save_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Saving-Machine Input Orbit

**Claim.** For each $r$ up to the initial input-head position, the saving machine remains false, moves left by $r$, and preserves output; one further step reaches true at position zero with output still unchanged.

**Proof.** Induct on $r$ for the claim up to the initial position $p$. At $r=0$ it is the assumed state and the identity of the run. For the successor step, the induction hypothesis puts the head at position $p-r$; when $r<p$, this position is positive and at most $|x|$, so the input head reads a symbol (`inputSymbolInner`). The machine's transition on a false state reading a symbol moves left, stays false, and emits nothing. A left move decreases the position by one (`moveInputPos_neg_val`), while emitting nothing preserves the output (`step_of_inputMoveAction`). At $r=p$ the induction conclusion puts the head at zero; there the input is blank, so the next transition enters true and stays at zero (`step_of_inputMoveAction`, `moveInputPos_zero`). That transition also emits nothing, proving output preservation at the final step.

**Key facts.** `Turing.inputSymbolInner`, `Turing.step_of_inputMoveAction`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.FinTM.moveInputPos_zero`.
