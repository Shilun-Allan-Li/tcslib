<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferedComp_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reaching the Second Phase

**Claim.** If $M_1$ computes $y$ from $x$ in $t_1$ steps, then the buffered composition reaches a second-phase configuration representing $M_2$'s initial configuration on $y$ after some time $a\le t_1+|y|+2$, with boundary tag true and the first machine's input position, tapes, and head positions recorded.

**Proof.** Among the times when $M_1$ is halted on input $x$, choose the least one, $t$. This exists because the given run halts at $t_1$, so $t\le t_1$. Let $c$ be the configuration at time $t$. The computation characterization shows that $M_1$ computes its output at time $t$; uniqueness of the output across computations of the same input (`Turing.FinTM.ComputesInTime.output_unique`) implies that $c$'s output is $y$. Run the buffered machine through the first phase for $t$ steps, then rewind and dispatch to the second phase. The first-phase run lemma identifies the composite configuration after the initial $t$ steps with the embedding of $c$ (`Turing.FinTM.bufferedFirstCfg_init`, `Turing.FinTM.bufferedFirstCfg_run`). The rewind lemma says that a halted first-phase configuration reaches the second-phase embedding of $M_2$'s initial configuration on its output after $|c.\mathrm{output}|+2$ additional steps, preserving the physical input position and first-block tape contents and head positions (`Turing.FinTM.bufferedFirstCfg_rewind`). Since $c.\mathrm{output}=y$, this yields the desired configuration at $a=t+|y|+2$. The inequality $t\le t_1$ gives $a\le t_1+|y|+2$.

**Key facts.** `Turing.FinTM.ComputesInTime.output_unique`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.bufferedFirstCfg_init`, `Turing.FinTM.bufferedFirstCfg_run`, `Turing.FinTM.bufferedFirstCfg_rewind`.
