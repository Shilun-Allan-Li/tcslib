<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.exec_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step execution equation

**Claim.** For a configuration $c$, execution for $t+1$ steps returns the halted verdict with $c$'s memory if the next step halts; if it continues at a configuration $c_1$, execution returns the result of running for $t$ steps from $c_1$.

**Proof.** Unfold the definitions of bounded execution and of a single step, then consider the instruction at the current program counter. Each instruction that continues produces exactly the next configuration used by execution: arithmetic and memory instructions update the prescribed location and advance the counter, while the conditional branch chooses its target and leaves memory unchanged. Thus the recursive execution call agrees with execution for $t$ steps from that next configuration. The accept and reject instructions instead halt with their respective Boolean verdicts and preserve the current memory. These cases establish the stated equation.
