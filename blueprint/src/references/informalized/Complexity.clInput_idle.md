<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clInput_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorbing Copy-Return Control

**Claim.** For every Boolean input word $x$ and every configuration $c$ of the input copier on $x$, if $c$ is in state $2$, then one machine step leaves the entire configuration unchanged.

**Proof.** In state $2$, the copier uses a control action that leaves the work tape, work head, and output unchanged and keeps the state equal to $2$. Its input-head movement is zero, which fixes the input-head position by the zero-movement identity (Turing.moveInputPos_zero). Consequently every component of the configuration is unchanged.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
