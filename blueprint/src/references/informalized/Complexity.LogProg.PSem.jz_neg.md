<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.jz_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero-test preservation

**Claim.** If the instruction at state $l$ branches to $l_1$ when register $r$ is zero and to $l_0$ otherwise, the current configuration satisfies the guard, $r$ is nonzero, and the configuration at $l_0$ has probabilistic semantics with acceptance probability $p$, then the configuration at $l$ has the same probabilistic semantics.

**Proof.** The deterministic-step preservation principle (`Complexity.LogProg.PSem.det`) transfers probabilistic semantics from the next configuration to the current guarded configuration. Since $v(r)\ne 0$, the zero test takes its negative branch. The resulting configuration is $(l_0,v,\text{no answer})$, so the assumed probabilistic semantics there yields the conclusion.

**Key facts.** `Complexity.LogProg.PSem.det`.
