<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.bufferedCompTM_computesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Time for Buffered Composition

**Claim.** If $M_1$ computes $y$ from $x$ in exactly $t_1$ steps and $M_2$ computes $o$ from $y$ in exactly $t_2$ steps, then their buffered sequential composition computes $o$ from $x$ in exactly $t_1+|y|+2+t_2$ steps.

**Proof.** The first machine's run reaches a halted configuration whose output is $y$. The buffered start lemma states that after some $a\le t_1+|y|+2$ steps, the composition is in the second-phase configuration representing the initial run of $M_2$ on $y$, with the physical input position and first machine's tape data retained (`Turing.FinTM.bufferedComp_start`). From this embedded configuration, the second-phase run lemma shows that after a further $t_2$ steps the composite configuration represents $M_2$ after $t_2$ steps (`Turing.FinTM.bufferedSecondCfg_run`). Because $M_2$ is halted then and has output $o$, the composite run at time $a+t_2$ is halted with output $o$: the equivalence between computation and these two run properties is `Turing.FinTM.computesInTime_iff`, and `Turing.MultiTapeTM.runFrom_add` combines the two run segments. Finally, $a+t_2\le t_1+|y|+2+t_2$, so persistence of a computation to later times (`Turing.FinTM.ComputesInTime.mono`) yields the claimed time bound.

**Key facts.** `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
