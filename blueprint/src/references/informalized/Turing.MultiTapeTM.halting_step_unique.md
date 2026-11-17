<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.halting_step_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of the Halting Step

**Claim.** If a multi-tape Turing machine halts at step $t_1$ on an input and also halts at step $t_2$ on that input, then $t_1=t_2$.

**Proof.** It suffices to treat the case $t_1\le t_2$, since the other ordering follows by swapping the two times. Write $t_2=t_1+d$. If $d=0$, the times are equal. Otherwise, the configuration at step $t_1$ is halted by the first halting assumption. A halted configuration is fixed by every later run (`Turing.MultiTapeTM.runFrom_of_halt`), with the run-addition identity (`Turing.MultiTapeTM.runFrom_add`) expressing the run at step $t_2$ as a continuation from step $t_1$. Thus the configuration at step $t_2-1$ is also halted. But the definition of halting at step $t_2$ requires that the configuration at step $t_2-1$ is not halted, a contradiction. Therefore $d$ cannot be positive, and $t_1=t_2$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
