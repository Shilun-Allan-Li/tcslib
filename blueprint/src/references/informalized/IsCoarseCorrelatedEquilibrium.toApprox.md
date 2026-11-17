<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: IsCoarseCorrelatedEquilibrium.toApprox -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Equilibrium Is Approximate

**Claim.** Every exact coarse correlated equilibrium is an $\varepsilon$-coarse correlated equilibrium for each $\varepsilon\ge 0$.

**Proof.** For each fixed row action, the equilibrium hypothesis bounds its deviation utility by the expected utility. Since $\varepsilon$ is nonnegative, the expected utility is at most itself plus $\varepsilon$, giving the required row inequality. The same reasoning applied to each column action gives the column inequality. Together these are the approximate equilibrium conditions.
