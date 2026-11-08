<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.of_det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After a Deterministic Step

**Claim.** If the instruction at $l$ is the deterministic instruction $i$, halting within $N+1$ steps from $(l,v,res)$ implies the stated halting property within $N$ steps from the configuration obtained by applying the fixed deterministic part of the machine.

**Proof.** Fix a word $\sigma$ of length $N$ for the successor configuration. Prepend an arbitrary choice bit, here chosen as false, and apply the assumed halting property to the resulting word of length $N+1$. Since the instruction at $l$ is deterministic, the first transition ignores that choice bit and agrees with the step of the machine whose choice instructions have been replaced by the fixed return value $\beta$ (`nastep_det`). The run decomposition (`narun_cons`) therefore identifies the endpoint with the run on $\sigma$ from the stated successor, proving it is halted. For each $t<N$, the prefix of length $t+1$ of the prefixed word yields the same configuration as the length-$t$ run from that successor. The guard condition at time $t+1$ in the original run gives the required condition whenever this configuration is live.

**Key facts.** `Complexity.LogProg.narun_cons`, `Complexity.LogProg.nastep_det`.
