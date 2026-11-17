<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.walkLe_reach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Walks Give Restricted Reachability

**Claim.** If a walk from $c$ to $t$ has bound $j$ and $c<n$, then $t$ is reachable from $c$ by a finite sequence of steps whose endpoints are less than $n$ and whose steps follow $E$.

**Proof.** Induct on the bound $j$, allowing the starting vertex to vary. At bound zero, the walk condition says $c=t$, so reflexivity gives the required reachability. At a positive bound, either $c=t$, and reflexivity again suffices, or the walk begins with a step from $c$ to some $v<n$ satisfying $E(c,v)$, followed by a walk from $v$ to $t$ with bound one less. The induction hypothesis, using $v<n$, gives restricted reachability from $v$ to $t$. Prepending the step from $c$ to $v$ gives the desired sequence; its endpoints satisfy the restriction because $c<n$ and $v<n$.
