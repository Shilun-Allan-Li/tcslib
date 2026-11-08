<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockLoop.lean :: Complexity.TimeHierarchy.clockTM_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clock Machine Diagonal Specification

**Claim.** If $K$ halts on $x$ with output $s$ after $t_K$ steps, the clock machine halts with the negation of the proposition that $W$ halts on $x$ within $\operatorname{ctrVal}(s)$ steps with output $[true]$, at the stated time.

**Proof.** The setup lemma provides a time $a\le t_K+|s|+|x|+5$ at which the clock machine is in the decrement configuration with $W$ initialized and buffer $s` (`clockTM_setup`). The bounded simulation lemma then provides a further duration $t\le\operatorname{ctrBound}(s)$ at which it halts and outputs the one-bit word encoding the negation of whether the simulated computation has halted with output $[true]` (`clockTM_loop`). By the computation characterization (`computesInTime_iff`), that condition is exactly whether $W$ computes $[true]$ on $x$ in $\operatorname{ctrVal}(s)$ steps. Thus the clock machine has the required output after $a+t$ steps. A machine that has halted remains in its halting configuration, so its computation persists to the specified time (`ComputesInTime.mono`). Finally, unfolding the counter bound and using the two phase bounds yields $a+t\le t_K+4|s|+|x|+4\operatorname{ctrVal}(s)+6$.

**Key facts.** `Complexity.TimeHierarchy.clockTM_setup`, `Complexity.TimeHierarchy.clockTM_loop`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
