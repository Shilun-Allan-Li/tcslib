<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.jz_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Branch Semantics

**Claim.** If the instruction at state $l$ tests whether register $r$ is zero, the guard holds at the configuration at $l$, the register is nonzero, and the nonzero branch at $l_0$ has terminating semantics with acceptance equivalent to $P$, then the configuration at $l$ has the same semantics.

**Proof.** The deterministic-instruction preservation principle transfers the semantics of the one-step successor back to the guarded configuration (`NSem.det`). Because $v(r)\ne 0$, the zero test selects the nonzero branch at $l_0$; the valuation and answer record remain unchanged. Hence the successor is $(l_0,v,\mathrm{none})$, whose assumed semantics gives the needed premise. The preservation principle concludes the proof.

**Key facts.** `Complexity.LogProg.NSem.det`.
