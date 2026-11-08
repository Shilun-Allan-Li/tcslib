<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MHalt.ret -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Immediate return halts

**Claim.** If the instruction at state $l$ is a return of $r$ and $G$ holds at the initial configuration with state $l$, registers $v$, no stored result, and memory $\mu$, then the machine halts with result $r$ from that configuration, with $G$ holding at every strictly earlier configuration.

**Proof.** Use $T=1$. By the definition of a memory-machine step, the return instruction changes the control state to halted and stores the answer $r$, leaving the registers and memory unchanged. Hence the run is halted with result $r$ at time $1$. The only natural number strictly below $1$ is $0$, and the time-zero configuration is the given initial configuration, where $G$ holds by hypothesis.
