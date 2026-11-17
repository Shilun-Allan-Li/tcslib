<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.kCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step preservation of lifted configurations

**Claim.** When $K$ has a present state in $c$, one clock-machine step from the lift of $c$ is the lift of the configuration reached by one step of $K$.

**Proof.** Write the present state of $c$ as $q$. The clock transition rule (\texttt{clockTM_step_some}) says the clock machine applies its transition at state $\mathrm{kRun}(q)$. Its input symbol and the symbols under the $K$ work-tape heads agree with those seen by $K$ in $c$, so the transition action is exactly $K$'s action. The resulting input position and the $K$-tape block therefore agree on both sides. The counter tape stores the output produced so far: if the action emits a bit, appending that bit to the buffered output is precisely the tape update at the old output length, as expressed by the buffer-append identity (\texttt{bufferTape_append}); if it emits nothing, the buffer is unchanged. The $W$-tape block remains blank with heads at zero, and the external output remains empty. Thus every component of the resulting configurations agrees.

**Key facts.** `Complexity.TimeHierarchy.clockTM_step_some`, `Turing.FinTM.bufferTape_append`.
