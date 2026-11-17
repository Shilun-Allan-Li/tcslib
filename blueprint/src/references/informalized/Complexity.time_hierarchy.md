<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.time_hierarchy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Time Hierarchy

**Claim.** If $g$ is time constructible and eventually dominates every constant multiple of $(f(n)+n+1)^2$, then $\mathrm{DTIME}(f)$ is a proper subset of $\mathrm{DTIME}(n\mapsto g(n)+1)$.

**Proof.** Apply the diagonal-simulator time-hierarchy theorem with the simulator's overhead function $\Phi(t,n)=(t+n+1)^2$. Its required overhead condition $t\le\Phi(t,n)$ is supplied by `le_sq_overhead`. With this choice, the assumed eventual domination is exactly the simulator theorem's growth hypothesis. Since $g$ is time constructible by assumption, all hypotheses of that theorem hold, and it yields the asserted proper inclusion (`DiagSimulator.time_hierarchy`).

**Key facts.** `Complexity.TimeHierarchy.le_sq_overhead`, `Complexity.TimeHierarchy.DiagSimulator.time_hierarchy`.
