<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean :: Complexity.LogProg.SavitchARM.reach_of_chain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Along a Chain

**Claim.** If every consecutive pair in a finite chain is related by $R$ and every chain element through index $T$ is below $K$, then any segment of length at most $2^i$ is reachable at level $i$, provided it stays within the chain.

**Proof.** Induct on the level $i$. At level zero, the allowed segment length satisfies $t\le1$. If $t=0$, the endpoints coincide; if $t=1$, the required relation is the assumed $R$-step. For the successor level, split the segment at offset $t_1=\min(t,2^i)$. The first piece has length at most $2^i$, and the remaining length $t-t_1$ is also at most $2^i$, because $t\le2^{i+1}$. Both pieces remain within the original chain, so the induction hypothesis gives reachability at level $i$ for each. The intermediate point $c_{j+t_1}$ is below $K$ by the chain bound, and the two reachability statements therefore combine to give reachability at level $i+1$.
