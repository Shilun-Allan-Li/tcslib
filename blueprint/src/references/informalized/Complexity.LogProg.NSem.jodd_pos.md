<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.jodd_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Oddness Branch Semantics

**Claim.** If the instruction at state $l$ tests whether register $r$ is odd, the guard holds at the configuration at $l$, the register is odd, and the odd branch at $l_1$ has terminating semantics with acceptance equivalent to $P$, then the configuration at $l$ has the same semantics.

**Proof.** The deterministic-instruction preservation principle transfers terminating semantics and the acceptance equivalence from the successor of a deterministic instruction to the guarded configuration before that instruction (`NSem.det`). Since $v(r)\bmod 2=1$, the oddness test sends the machine to $l_1$ without changing the register values or answer record. The assumed semantics at $(l_1,v,\mathrm{none})$ is therefore exactly the semantics of this successor, so the preservation principle yields the result.

**Key facts.** `Complexity.LogProg.NSem.det`.
