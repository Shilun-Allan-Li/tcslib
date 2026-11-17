<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_comp_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed buffered composition

**Claim.** If finite binary Turing machines $F,G$ compute $y$ from $x$ within $s$ steps and $z$ from $y$ within $t$ steps, their buffered sequential composition computes $z$ from $x$ within $s+|y|+2+t$ steps.

**Proof.** The buffered startup result (`bufferedComp_start`) provides a time $a\le s+|y|+2$ at which the composed machine has reached a configuration representing the initial configuration of $G$ on $y$. The simulation result (`bufferedSecondCfg_run`) says that running this represented configuration for $t$ more steps tracks $G$’s run for those same $t$ steps. Since $G$ computes $z$ in time $t$, its run at that time is halted with output $z` (`computesInTime_iff`); the simulation transfers both facts to the composed machine. The run concatenation law (`runFrom_add`) identifies this as the composed run after $a+t$ steps. Finally $a+t\le s+|y|+2+t$, so monotonicity of computation time (`ComputesInTime.mono`) proves the result.

**Key facts.** `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
