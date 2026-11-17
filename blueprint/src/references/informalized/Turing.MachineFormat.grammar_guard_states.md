<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.grammar_guard_states -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound on state count

**Claim.** If $(4k+5)3^{k+1}(n+1)\le s$, then $n+1\le s$.

**Proof.** The coefficient $(4k+5)3^{k+1}$ is at least $1$: both factors are positive integers. Multiplying this inequality by $n+1$ gives $n+1\le (4k+5)3^{k+1}(n+1)$. Combining with the hypothesis yields $n+1\le s$.
