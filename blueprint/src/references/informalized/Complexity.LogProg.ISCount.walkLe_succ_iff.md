<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.walkLe_succ_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step walk decomposition

**Claim.** A bounded $R$-walk of length at most $j+1$ from $c$ to $t$ exists exactly when either a bounded walk of length at most $j$ already connects them, or there is a vertex $w$ reachable from $c$ within $j$ steps with $R(w,t)$ and $t<K$.

**Proof.** Proceed by induction on $j$, with the starting vertex arbitrary. For $j=0$, the definition of a walk of length at most one says either $c=t$, or there is a bounded vertex $v$ with $R(c,v)$ and $v=t$. In the latter case, take $w=c$: the length-zero walk from $c$ to itself, the edge $R(c,t)$, and the bound $t<K$ give the second alternative. Conversely, a length-zero walk from $c$ to $t$ gives the first alternative, while the second alternative at length zero has $w=c$; its edge and endpoint bound provide the one-step walk.

For the induction step, a walk of length at most $j+2$ either stays at $c$, or first moves to a bounded vertex $v$ and continues with a walk of length at most $j+1$ from $v$ to $t$. In the latter case, apply the induction hypothesis to the remaining walk. If it already reaches $t$ within $j$ steps, prepend the edge from $c$ to $v$ to obtain the first alternative at length $j+1$. If it reaches some $w$ within $j$ steps and then takes an edge to $t$, prepend that same first edge to the walk from $c$ to $w$; the final edge and bound on $t$ remain unchanged, yielding the second alternative. Conversely, a walk of length at most $j+1$ is also one of length at most $j+2$. If the second alternative holds, its walk to $w$ followed by the edge to $t$ gives the desired walk. In the induction hypothesis's subcase where the walk to $w$ is itself obtained by a final edge, use reflexivity of bounded walks to treat that last edge as the endpoint extension; these are precisely the reflexivity and extension properties of walks (`Complexity.walkLe_refl`, `Complexity.walkLe_succ`).

**Key facts.** `Complexity.walkLe_refl`, `Complexity.walkLe_succ`.
