<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.jz_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-test preservation

**Claim.** If the instruction at state $l$ branches to $l_1$ when register $r$ is zero and to $l_0$ otherwise, the current configuration satisfies the guard, $r$ is zero, and the configuration at $l_1$ has probabilistic semantics with acceptance probability $p$, then the configuration at $l$ has the same probabilistic semantics.

**Proof.** The deterministic-step preservation principle (`Complexity.LogProg.PSem.det`) transfers probabilistic semantics from the next configuration to the current guarded configuration. Since $v(r)=0$, the zero test takes its positive branch. One step reaches $(l_1,v,\text{no answer})$ without changing the registers or answer, and the assumed semantics at that successor gives the result.

**Key facts.** `Complexity.LogProg.PSem.det`.
