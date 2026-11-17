<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.DiagSimulator.time_hierarchy_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time Hierarchy for Positive Bounds

**Claim.** If $g$ is positive everywhere and satisfies the stated time-constructibility and growth assumptions, then DTIME$(f)$ is a proper subset of DTIME$(g)$.

**Proof.** First identify DTIME$(g+1)$ with DTIME$(g)$. The inclusion from DTIME$(g)$ to DTIME$(g+1)$ follows from monotonicity of time classes (`DTIME.mono`). Conversely, if a machine decides a language within $c(g(n)+1)$ steps, positivity gives $g(n)\ge1$, hence $g(n)+1\le2g(n)$. Its running time is therefore at most $2c g(n)$, so the same machine witnesses membership in DTIME$(g)$. The time bound on computations can be increased by monotonicity (`ComputesInTime.mono`). Now apply the deterministic time hierarchy theorem `time_hierarchy`, which gives DTIME$(f)\subsetneq$ DTIME$(g+1)$. Replacing DTIME$(g+1)$ by the equal class DTIME$(g)$ proves the claim.

**Key facts.** `Complexity.DTIME.mono`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.TimeHierarchy.DiagSimulator.time_hierarchy`.
