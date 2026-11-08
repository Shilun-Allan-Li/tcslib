<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.bufferedCompTM_computes_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Buffered Computation

**Claim.** The buffered composition computes $w$ from $x$ in some finite number of steps if and only if there is a word $y$ such that $M_1$ computes $y$ from $x$ in some finite number of steps and $M_2$ computes $w$ from $y$ in some finite number of steps.

**Proof.** For the forward implication, take a time $t$ at which the composition halts with output $w$. The first component must eventually halt: otherwise, the first-phase run lemma would keep the composite in a live first-phase configuration through time $t$, contradicting that the composite is halted (`Turing.FinTM.bufferedFirstCfg_run`). Let $s$ be the first time the run of $M_1$ halts, and let $y$ be its output then. The computation characterization gives a computation of $y$ by $M_1$ at time $s$ (`Turing.FinTM.computesInTime_iff`). The buffered-start lemma places the composition in the second phase after some time $a$, representing $M_2$'s initial configuration on $y$ (`Turing.FinTM.bufferedComp_start`). Extend the composite run to time $a+t$; this is permitted because computations persist to later times (`Turing.FinTM.ComputesInTime.mono`). Splitting the run at time $a$ using the run-addition law (`Turing.MultiTapeTM.runFrom_add`) and applying the second-phase run lemma (`Turing.FinTM.bufferedSecondCfg_run`) shows that $M_2$'s run from its initial configuration on $y$ is halted with output $w$. The computation characterization then gives the required computation by $M_2$.

Conversely, suppose such a word $y$ and finite computation times $s,t$ are given. The buffered-start lemma reaches the second-phase configuration for $M_2$ on $y$ after some time $a$. The second-phase run lemma identifies the composite's next $t$ steps with $M_2$'s run for $t$ steps. Since that run halts with output $w$, the computation characterization and the run-addition law show that the composite halts with output $w$ at time $a+t$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.bufferedFirstCfg_run`, `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.ComputesInTime.mono`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.bufferedSecondCfg_run`.
