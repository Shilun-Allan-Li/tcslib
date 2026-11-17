<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_unary_mask -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission Schedule Under Unary Normalization

**Claim.** For a configuration $c$ on $x$, the length-$t$ emission schedule of the normalized machine from $c$ equals the schedule of $M$ from the unary reinterpretation of $c$.

**Proof.** Induct on $t$, allowing the starting configuration to vary. At length zero both schedules are empty. For the successor length, each schedule begins with whether the current configuration's transition emits a symbol, followed by the schedule from the one-step successor. The one-step correspondence (`Complexity.b2_unary_step`) identifies those successor configurations. For the initial emission, split according to whether $c$ is halted: if it is halted, neither machine emits; if it is active, the transition uses the same state and work-tape symbols, and the input read under unary reinterpretation is the original read with every present bit changed to true (`Complexity.b2_unary_read`). By definition of the normalized transition, this is exactly the input supplied to $M$'s transition. Thus the first emission indicators agree, and the induction hypothesis equates the remaining schedules.

**Key facts.** `Complexity.b2_unary_step`, `Complexity.b2_unary_read`.
