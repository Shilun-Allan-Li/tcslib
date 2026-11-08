<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.mem_workReadsK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of Work-Read Patterns

**Claim.** For every natural number $k$, every function $w:\mathrm{Fin}(k)\to\mathrm{Option}(\mathrm{Bool})$ occurs in the recursively defined list of all length-$k$ work-read patterns.

**Proof.** Proceed by induction on $k$. When $k=0$, there is only the empty-coordinate function, so $w$ is the unique function $[?]$; it is the sole entry in the list. For the successor case, the first coordinate $w(0)$ is one of the three possible values: absent, false, or true. The outer list enumerates all three choices, so this value occurs there. The remaining coordinates form the tail function, which occurs in the length-$k$ list by induction. The recursive construction pairs each first-coordinate choice with every tail pattern, and the resulting cons function is $w$. Thus $w$ occurs in the successor list.
