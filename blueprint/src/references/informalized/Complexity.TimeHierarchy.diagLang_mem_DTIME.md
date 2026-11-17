<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.diagLang_mem_DTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal Simulation Time Bound

**Claim.** For a time-constructible function $g$, the language of words on which the diagonal simulation does not halt at time $g(|x|)$ with output $1$ is decidable in time $c(g(n)+1)$ for some constant $c$.

**Proof.** Apply the diagonal language time-bound theorem (`diagLangOf_mem_DTIME`) to the machine `diagSim`. Its conclusion concerns `diagLangOf diagSim g`; by definition this is exactly `diagLang g`. Therefore the diagonal language belongs to the time class with bound $g(n)+1$.

**Key facts.** `Complexity.TimeHierarchy.diagLangOf_mem_DTIME`.
