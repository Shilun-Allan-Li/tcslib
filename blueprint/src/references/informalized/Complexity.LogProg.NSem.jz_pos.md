<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.jz_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Branch Semantics

**Claim.** If the instruction at state $l$ tests whether register $r$ is zero, the guard holds at the configuration at $l$, the register equals zero, and the zero branch at $l_1$ has terminating semantics with acceptance equivalent to $P$, then the configuration at $l$ has the same semantics.

**Proof.** The deterministic-instruction preservation principle transfers terminating semantics and the acceptance equivalence from the successor back to the guarded configuration (`NSem.det`). Since $v(r)=0$, the test selects the branch at $l_1$, leaving the valuation and answer record unchanged. Thus the one-step successor is $(l_1,v,\mathrm{none})$, and its assumed semantics supplies the premise for that principle.

**Key facts.** `Complexity.LogProg.NSem.det`.
