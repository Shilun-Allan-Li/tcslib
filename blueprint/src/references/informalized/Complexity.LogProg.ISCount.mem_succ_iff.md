<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.mem_succ_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability After One Additional Step

**Claim.** A vertex is reachable within $L+1$ steps exactly when it is reachable within $L$ steps or is reached by one final $R$-step from a vertex reachable within $L$ steps, with the final vertex below $K$.

**Proof.** Unpack reachability by choosing an initial vertex below $K$ and a walk from it. The one-step extension characterization of walks (`walkLe_succ_iff`) says that such a walk either already has length at most $L$, or consists of a walk of length at most $L$ to some vertex $w$, followed by an $R$-step to $t$, with $t<K$. In the first case the same initial vertex witnesses reachability of $t$ within $L$ steps. In the second it witnesses reachability of $w$ within $L$ steps, giving the stated final-step alternative. Conversely, a witness for reachability within $L$ remains a witness within $L+1$ by extension of the walk (`walkLe_succ`). For the final-step alternative, combine the walk to $w$ with the step from $w$ to $t$ using the same one-step extension characterization; the resulting walk, together with its initial vertex, witnesses reachability of $t$ within $L+1$ steps.

**Key facts.** `Complexity.LogProg.ISCount.walkLe_succ_iff`, `Complexity.walkLe_succ`.
