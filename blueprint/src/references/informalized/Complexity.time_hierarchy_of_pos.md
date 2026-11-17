<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.time_hierarchy_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time Hierarchy for Positive Bounds

**Claim.** If $g$ is time constructible, is positive everywhere, and eventually dominates every constant multiple of $(f(n)+n+1)^2$, then $\mathrm{DTIME}(f)$ is a proper subset of $\mathrm{DTIME}(g)$.

**Proof.** Apply the positive-bound version of the diagonal-simulator time-hierarchy theorem with overhead $\Phi(t,n)=(t+n+1)^2$. The estimate $t\le\Phi(t,n)$ is `le_sq_overhead`; the assumed eventual growth is precisely the theorem's domination hypothesis for this overhead. The time-constructibility and pointwise positivity assumptions are already given. The theorem therefore gives the proper inclusion into $\mathrm{DTIME}(g)$ (`DiagSimulator.time_hierarchy_of_pos`).

**Key facts.** `Complexity.TimeHierarchy.le_sq_overhead`, `Complexity.TimeHierarchy.DiagSimulator.time_hierarchy_of_pos`.
