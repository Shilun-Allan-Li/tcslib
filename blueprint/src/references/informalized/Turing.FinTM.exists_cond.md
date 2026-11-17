<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.exists_cond -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Machine Simulation

**Claim.** If a finite Boolean machine computes the one-symbol word $[p(x)]$ on every input, then a finite Boolean machine can simulate, on input $x$, precisely the machine selected by the value of $p(x)$.

**Proof.** Use the conditional machine that first runs $D$ to determine $p(x)$ and then enters the corresponding branch machine. Fix $x$, and let $a$ be the time at which the conditional-machine start lemma places it into the branch for $p(x)$. The run simulation for the right-hand component shows that, for every $t$, its configuration at time $a+t$ is the embedding of the selected branch machine’s configuration after $t$ steps, with the setup tapes carried along. If the conditional machine halts with output $w$, extend its run to time $a+t$ using persistence after halting. The simulation then shows that the selected branch has halted with output $w$; the branch-computation equivalence identifies this with the chosen machine’s computation. Conversely, if the chosen machine halts with output $w$ after $t$ steps, the same simulation shows that the conditional machine halts with that output at time $a+t$. The equivalence between timed computation and the run’s halting and output conditions makes both implications precise.

**Key facts.** `Turing.FinTM.condTM_start`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.rightCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.branchTM_computes`.
