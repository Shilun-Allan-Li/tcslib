<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.rrun_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition of Run Times

**Claim.** For a register program $P$, oracle $\mathcal O$, configuration $c$, and natural numbers $a,b$, running for $a+b$ steps from $c$ gives the same configuration as running for $a$ steps and then for $b$ further steps.

**Proof.** The run is defined by iterating the one-step transition. Since addition counts the same total number of iterations in either order, the iterate-addition law gives the run for $a+b$ as the run for $b$ applied after the run for $a$.
