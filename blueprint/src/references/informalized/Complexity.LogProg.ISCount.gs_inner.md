<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.gs_inner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner-Stage Condition on the Reachable Set

**Claim.** The recursive condition over $K$ stages, starting with position and counter zero, holds exactly when every element of the reachable set satisfies $u\ne v$ and fails $R(u,v)$.

**Proof.** Use the finite-set characterization of the recursive condition (`gs_iff`). Since there are $K$ stages starting at zero, its interval is exactly the numbers below $K$. In the forward direction, the characterization supplies a set $T$ of selected positions. The condition on selected positions says each lies in the reachable set and satisfies $u\ne v$ and $\neg R(u,v)$. Thus $T$ is a subset of the reachable set. The terminal condition says $|T|$ equals the cardinality of that reachable set; a subset of a finite set with the same cardinality is the whole set. Consequently every reachable element satisfies the required pair of properties. In the reverse direction, take $T$ to be the reachable set itself. Every member lies below $K$ by the bound on reachable vertices, and the assumed pointwise condition gives the selected-position requirements. There are no unselected positions in the interval that are reachable, so the alternative condition, which is always true, holds wherever required. The terminal counter equals the cardinality of the reachable set by construction.

**Key facts.** `Complexity.LogProg.ISCount.gs_iff`, `Complexity.LogProg.ISCount.mem_ball`, `Complexity.LogProg.ISCount.Mem.lt`.
