<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.windowRun_halts_on_last_transition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting on the Final Transition

**Claim.** If the machine halts at time $t+1$, emits $b$ on the transition from time $t$, and stays in the window through time $t+1$, then the windowed run with clock $t+2$ halts at time $t+1$ and its accumulator is the value of $\sigma$ on the time-$t$ output followed by $b$.

**Proof.** Apply the result for a window run through a halted configuration with clock $t+2$ and halting time $t+1$. Its strict clock inequality holds, and the stated window hypothesis supplies the required window condition. It returns the configuration at time $t+1$ and accumulator $\sigma$ of that configuration's output. The run identity `runFrom_succ_eq_step'` identifies this final configuration as the successor of the configuration at time $t$. By `step_output`, its output is the time-$t$ output followed by the optional symbol emitted at time $t$. Since that symbol is $b$, the output is exactly the time-$t$ output followed by $b$, giving the claimed accumulator.

**Key facts.** `Turing.windowRun_halted_of_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`.
