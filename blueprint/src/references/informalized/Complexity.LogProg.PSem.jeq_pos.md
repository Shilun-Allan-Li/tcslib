<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.jeq_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal-branch preservation

**Claim.** If the instruction at state $l$ branches to $l_1$ when registers $r$ and $s$ are equal, the current configuration satisfies the guard, those registers have equal values, and the configuration at $l_1$ has probabilistic semantics with acceptance probability $p$, then the configuration at $l$ has the same probabilistic semantics.

**Proof.** The deterministic-step preservation principle (`Complexity.LogProg.PSem.det`) says that a guarded configuration inherits probabilistic semantics from the configuration obtained by executing its deterministic instruction. Here, the equality $v(r)=v(s)$ makes the equality test take its positive branch, so one step from $(l,v,\text{no answer})$ reaches $(l_1,v,\text{no answer})$ without changing the registers. The assumed semantics at that successor therefore gives the desired semantics at the current configuration.

**Key facts.** `Complexity.LogProg.PSem.det`.
