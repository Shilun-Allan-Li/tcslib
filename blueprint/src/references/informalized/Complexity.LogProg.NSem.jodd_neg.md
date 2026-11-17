<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.jodd_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Oddness Branch Semantics

**Claim.** If the instruction at state $l$ tests whether register $r$ is odd, the guard holds at the configuration at $l$, the register is not odd, and the even branch at $l_0$ has terminating semantics with acceptance equivalent to $P$, then the configuration at $l$ has the same semantics.

**Proof.** The deterministic-instruction preservation principle says that if the guard holds at a live configuration and the configuration reached by executing its deterministic instruction has terminating semantics with acceptance equivalent to $P$, then the original configuration does too (`NSem.det`). Here the test sends the machine to $l_0$ precisely when $v(r)\bmod 2\ne 1$. Thus the one-step successor is $(l_0,v,\mathrm{none})$, and the assumed semantics of that branch supplies the required successor semantics. Applying the preservation principle proves the claim.

**Key facts.** `Complexity.LogProg.NSem.det`.
