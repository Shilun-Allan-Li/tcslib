<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_prepare_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparing the First Cleanup Bank

**Claim.** If $M$ computes output $c$ from input $a$ in exactly $T$ steps, then for either emission mode the call machine reaches the frame with zero banks cleaned and the cleaner at its initial state by time $2T+|a|+4$.

**Proof.** The prepared-evaluation result supplies a time $t$ by which the evaluator has completed its computation and rightward scan, with $t\le 1+2T+|a|+2$, and with no earlier visit to the evaluator's return state (`Turing.FinTM.emCall_prepared_eval_first`). Its hypothesis that the source computes $c$ yields both halting at time $T$ and output $c$ (`Turing.FinTM.computesInTime_iff`). The call machine simulates the embedded evaluator up to this first return: before that point, its transition agrees with the embedded source transition on all states encountered, so the run simulation theorem identifies the two configurations at time $t$ (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, together with `Turing.embedEmitTM_runFrom`). The initial prepared configuration is the call machine's initial configuration (`Turing.FinTM.emCall_prepare_initial`), and the final prepared configuration is the frame with zero banks cleaned (`Turing.FinTM.emCall_prepare_final`), using the output equality just obtained. At the return state, one control transition enters the cleaner's initial state. The control action leaves tapes and output unchanged and keeps the input head fixed (`Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`). Hence the desired frame occurs at time $t+1$. Since $t+1\le 2T+|a|+4$, this gives the stated bound.

**Key facts.** `Turing.FinTM.emCall_prepared_eval_first`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.embedEmitTM_runFrom`, `Turing.FinTM.emCall_prepare_initial`, `Turing.FinTM.emCall_prepare_final`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
