<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_prepared_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffered Sequential Composition Bound

**Claim.** If the first machine halts with output $y$ after $T_1$ steps and the second computes $z$ from $y$ in time $T_2$, then the buffered composition halts with output $z$ within $T_1+|y|+2+T_2$ steps from the associated first-phase configuration.

**Proof.** First choose the earliest halting time $t\le T_1$ of the first machine. The first-halt fact (`Complexity.enumCont_first_halt`) ensures it remains live before $t$ and that its configuration at $t$ is the same as at $T_1$. Thus at $t$ its output is $y$. While the first machine is live, the buffered composition tracks its run (`Turing.FinTM.bufferedFirstCfg_run`). From the halted configuration, the composition rewinds its buffer and enters the second phase after $|y|+2$ steps (`Turing.FinTM.bufferedFirstCfg_rewind`). The second-phase simulation then tracks the second machine for $T_2$ steps, preserving the first machine's tapes and input-head position (`Turing.FinTM.bufferedSecondCfg_run`). The hypothesis that the second machine computes $z$ gives both that its time-$T_2$ state is halted and its output is $z` (`Turing.FinTM.computesInTime_iff`). Combining these phases with the run-addition law (`Turing.MultiTapeTM.runFrom_add`) yields a halted composition with output $z$ at time $t+(|y|+2)+T_2$. Since $t\le T_1$ and the first output is $y$, this time is at most the claimed bound.

**Key facts.** `Complexity.enumCont_first_halt`, `Turing.FinTM.bufferedFirstCfg_run`, `Turing.FinTM.bufferedFirstCfg_rewind`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`.
