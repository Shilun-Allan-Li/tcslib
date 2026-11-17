<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MReach.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of reachability invariants

**Claim.** If the machine reaches $b$ from $a$ in finitely many steps with $G$ holding at every configuration strictly before reaching $b$, and $G$ implies $G'$, then it reaches the same $b$ with $G'$ holding at every such configuration.

**Proof.** Take a time $T$ witnessing the reachability hypothesis. Keep $T$ and the equality identifying the endpoint with $b$. At each $t<T$, the original condition gives $G$ at the run's configuration; the implication from $G$ to $G'$ gives the new invariant at that same configuration. Hence the unchanged run witnesses reachability with invariant $G'$.
