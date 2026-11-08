<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_comp_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffered Composition Time Bound

**Claim.** If $F$ computes $y$ from $x$ in $s$ steps and $G$ computes $z$ from $y$ in $t$ steps, their buffered composition computes $z$ from $x$ in $s+|y|+2+t$ steps.

**Proof.** The buffered-start result places the composed machine, after some number $a$ of steps with $a\le s+|y|+2$, in a configuration representing the initial configuration of $G$ on $y$; this representation also preserves the data left by the first computation (`bufferedComp_start`). The simulation lemma for the second machine says that after $t$ further steps the composed machine represents exactly the configuration reached by running $G$ for $t$ steps (`bufferedSecondCfg_run`).

Because $G$ computes $z$ in time $t$, its run at that time is halted and has output $z$ (`computesInTime_iff`). The represented composed-machine configuration therefore has the same halted state and output. Splitting the run at time $a$ and then running for $t$ steps is justified by the run-addition law (`runFrom_add`), so the composition has computed $z$ by time $a+t\le s+|y|+2+t$. Monotonicity of computation time then gives the asserted exact bound (`ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
