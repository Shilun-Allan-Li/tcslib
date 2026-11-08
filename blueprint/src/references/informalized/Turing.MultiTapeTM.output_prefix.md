<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.output_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Prefixes Along a Run

**Claim.** If $t\le t'$, then the output after $t$ steps from a configuration is a prefix of the output after $t'$ steps.

**Proof.** Write $t'=t+d$ for some $d\ge 0$. The run-addition identity (`Turing.MultiTapeTM.runFrom_add`) identifies the later configuration with the result of running for $d$ further steps from the configuration at time $t$. Induct on $d$. For $d=0$, the outputs are equal. In the successor case, the next step appends the list form of its output symbol to the current output (`Turing.MultiTapeTM.step_output`); the current output is therefore a prefix of the next one. By induction, the output at time $t$ is a prefix of the output before this last step, and prefixhood is transitive with prefixhood under appending. Thus it remains a prefix after all $d$ additional steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`.
