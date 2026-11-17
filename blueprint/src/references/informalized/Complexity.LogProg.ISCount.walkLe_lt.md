<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.walkLe_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound along a bounded walk

**Claim.** If $c<K$ and there is a bounded $R$-walk of length at most $j$ from $c$ to $t$, then $t<K$.

**Proof.** Induct on the allowed length $j$, keeping the starting vertex arbitrary. At length zero, the walk condition says $c=t$, so the conclusion follows from $c<K$. For length $j+1$, either the walk stays at its starting vertex, in which case the same bound holds immediately, or it first goes to some vertex $v<K$ and then follows a walk of length at most $j$ from $v$ to $t$. Apply the induction hypothesis to that remaining walk, using $v<K$, to conclude $t<K$.
