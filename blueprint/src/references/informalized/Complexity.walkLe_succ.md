<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.walkLe_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Bounded Walks

**Claim.** If there is a walk from $c$ to $t$ with bound $j$, then there is one with bound $j+1$.

**Proof.** Induct on $j$, allowing the starting vertex to vary. At bound zero, the walk is equality, which is also an allowed case at bound one. At a positive bound, equality remains an allowed case at the larger bound. Otherwise, the walk consists of an initial step to some $v<n$ following $E$, and a continuation from $v$ with bound $j$. Apply the induction hypothesis to that continuation to raise its bound by one; keeping the initial step gives a walk with bound $j+2$, as required for the original bound $j+1$.
