<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After a Deterministic Instruction

**Claim.** If state $l$ executes deterministic instruction $i$, the guard holds at the current configuration, and all runs of length $N$ from the result of applying $i$ satisfy the halting and intermediate-guard conditions, then every run of length $N+1$ from the current configuration does too.

**Proof.** Choose any word of length $N+1$ and write it as its first bit followed by a suffix of length $N$. Because the instruction is deterministic, the first step is the same for either bit: it is the configuration obtained by applying $i$. The run decomposition law and the deterministic-step identity identify the full run with the suffix run from that configuration (`narun_cons`, `nastep_det`). The assumed length-$N$ property thus gives halting. For an intermediate time $t<N+1$, when $t=0$ the guard is the given initial guard. When $t=s+1$, the corresponding prefix run is the length-$s$ run from the post-instruction configuration. Since $s<N$, the assumed intermediate-guard property applies whenever that configuration is nonhalted.

**Key facts.** `Complexity.LogProg.narun_cons`, `Complexity.LogProg.nastep_det`.
