<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.jodd_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-branch preservation

**Claim.** If the instruction at state $l$ branches to $l_1$ when register $r$ is odd and to $l_0$ otherwise, the current configuration satisfies the guard, $r$ is odd, and the configuration at $l_1$ has probabilistic semantics with acceptance probability $p$, then the configuration at $l$ has the same probabilistic semantics.

**Proof.** The deterministic-step preservation principle (`Complexity.LogProg.PSem.det`) transfers probabilistic semantics from the next configuration to the current guarded configuration. Because $v(r)\bmod 2=1$, the oddness test takes its positive branch. One step therefore reaches $(l_1,v,\text{no answer})$ with the registers and answer unchanged. The assumed semantics at that successor gives the result.

**Key facts.** `Complexity.LogProg.PSem.det`.
