<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.walkLe_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of bounded walks

**Claim.** If $j\le k$ and there is a walk of length at most $j$ from $c$ to $t$ with the specified vertex bound and relation steps, then there is such a walk of length at most $k$.

**Proof.** Induct on the inequality $j\le k$. When the bounds are equal, the given walk already proves the result. For the successor step, apply the induction hypothesis to obtain a walk under the smaller bound, then use the fact that any walk allowed by a bound is also allowed by the next bound (\texttt{Complexity.walkLe_succ}). Repeating this one-step extension reaches the bound $k$.

**Key facts.** `Complexity.walkLe_succ`.
