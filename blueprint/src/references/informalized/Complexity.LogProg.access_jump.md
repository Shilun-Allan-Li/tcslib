<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_jump -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary Transition Path

**Claim.** If every transition from state $s$ is the stationary action entering state $s'$, then the specified configuration reaches the corresponding configuration in state $s'$ by a finite safe path.

**Proof.** The initial configuration is safe: its work-tape heads are at zero, within the interval from $-1$ to the bit-length of $|y|+1$ (`Complexity.LogProg.accessCfg_safe`). The one-step path property for a safe configuration (`Complexity.LogProg.access_step`) therefore gives a path to the result of applying the transition from $s$. By hypothesis that transition is `goAct` entering $s'$. A stationary action leaves the input position, tape contents, work-tape heads, and output unchanged, and changes only the state; hence it produces exactly the target configuration (`Complexity.LogProg.access_go`).

**Key facts.** `Complexity.LogProg.accessCfg_safe`, `Complexity.LogProg.access_step`, `Complexity.LogProg.access_go`.
