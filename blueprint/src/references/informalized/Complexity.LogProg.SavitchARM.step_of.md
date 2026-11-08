<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.step_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a Reachability Step

**Claim.** If the registers of a state are bounded by $B$ and the configuration after one step from label $\ell$ is guard-reachable from $c$, then the configuration at $\ell$ is also guard-reachable from $c$.

**Proof.** The register bounds on $\mathrm{st}$ imply that the configuration at label $\ell$ satisfies the guard (the fact that bounded states satisfy the guard, `gb_of`). The reachability composition principle `AReach.step` then prepends this initial configuration to the given run from its one-step successor to $c$.

**Key facts.** `Complexity.LogProg.SavitchARM.gb_of`, `Complexity.LogProg.AReach.step`.
