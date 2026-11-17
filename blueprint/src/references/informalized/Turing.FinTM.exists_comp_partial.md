<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.exists_comp_partial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partial Sequential Composition

**Claim.** For any two finite Boolean Turing machines, a finite Boolean machine computes exactly the partial composition: it halts with output $w$ on $x$ precisely when the first machine halts on $x$ with some output $y$ and the second halts on $y$ with output $w$.

**Proof.** Take the buffered composite machine, which first runs the first machine and then starts the second on the output produced. For the forward implication, suppose the composite halts at time $t$. If the first machine never halted, the buffered first-configuration simulation would show that the composite was still in its first phase at time $t$, contradicting halting. Thus the first machine halts at some time $s$; let $y$ be its output then. The start lemma for the buffered composite places it in the second-machine phase after a finite administrative prefix of length $a$. The composite’s run can be extended to time $a+t$ because halting runs persist, and the second-phase simulation identifies this later configuration with the second machine run for $t$ steps on $y$. Its halting and output conditions therefore give the required computation of $w$. Conversely, if the two machines halt successively through some intermediate output $y$, the start lemma puts the composite into the second phase after $a$ steps, and the second-phase simulation carries it through the second machine’s halting run. At time $a+t$ it has halted with output $w$. In both directions, the characterization of computation in time reduces the claim to the run’s halting state and output; the total time bound is only existential.

**Key facts.** `Turing.FinTM.bufferedFirstCfg_run`, `Turing.FinTM.bufferedFirstCfg_init`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.MultiTapeTM.runFrom_add`.
