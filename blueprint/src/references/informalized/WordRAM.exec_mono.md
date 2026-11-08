<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.exec_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of bounded execution

**Claim.** If executing the program from a configuration for $t$ steps returns $r$, then executing it from the same configuration for any $t'\ge t$ also returns $r$.

**Proof.** Proceed by induction on $t$, generalizing the configuration and the larger time bound. At $t=0$, zero-step execution returns `none` (`WordRAM.exec_zero`), contradicting the hypothesis that it equals `some r`; hence this case is impossible. For $t+1$, write $t'=t''+1$, which is possible since $t+1\le t'$. Inspect the first step from the configuration. If it halts with verdict $v$, the halting-step equation says execution for either positive time bound returns that verdict with the unchanged memory (`WordRAM.exec_succ_of_verdict`). The assumed result at time $t+1$ therefore identifies that result with $r$, and the same equation gives the result at time $t'$. If the first step continues at a configuration $c_1$, the continuing-step equation reduces execution at time $t+1$ to execution from $c_1$ for $t$ steps, and execution at time $t''+1$ to execution from $c_1$ for $t''$ steps (`WordRAM.exec_succ_of_step`). The original hypothesis supplies the induction hypothesis's result, while $t\le t''$ follows from $t+1\le t''+1$. Applying the induction hypothesis proves the desired equality.

**Key facts.** `WordRAM.exec_zero`, `WordRAM.exec_succ_of_verdict`, `WordRAM.exec_succ_of_step`.
