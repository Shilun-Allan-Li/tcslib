<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.ret -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Instruction Semantics

**Claim.** If the instruction at state $l$ returns $b$ and the guard holds at the configuration there, then that configuration terminates and accepts exactly when $b$ is true.

**Proof.** A configuration already in the halted state, with valuation $v$ and recorded answer $b$, has terminating semantics, and its acceptance condition is exactly $b=\mathrm{true}$ (`NSem.halted`). Executing the return instruction at $l$ produces precisely this halted configuration, namely $(\mathrm{none},v,\mathrm{some}\ b)$. The deterministic-instruction preservation principle then transfers this semantics back to the original configuration using the guard hypothesis (`NSem.det`).

**Key facts.** `Complexity.LogProg.NSem.halted`, `Complexity.LogProg.NSem.det`.
