<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.jodd_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-branch preservation

**Claim.** If the instruction at state $l$ branches to $l_1$ when register $r$ is odd and to $l_0$ otherwise, the current configuration satisfies the guard, $r$ is even, and the configuration at $l_0$ has probabilistic semantics with acceptance probability $p$, then the configuration at $l$ has the same probabilistic semantics.

**Proof.** The deterministic-step preservation principle (`Complexity.LogProg.PSem.det`) transfers probabilistic semantics from the next configuration to the current guarded configuration. Since $v(r)\bmod 2\ne 1$, the oddness test takes its negative branch. Thus one step reaches $(l_0,v,\text{no answer})$, leaving the registers and answer unchanged, and the assumed semantics there supplies the conclusion.

**Key facts.** `Complexity.LogProg.PSem.det`.
