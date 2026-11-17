<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.card_filter_rcode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of the Bounded Reachability Set

**Claim.** If the cutoff $K$ is at least $2^{\kappa(N)(s+\ell(x)+1)}$, then the number of reachable codes below $K$ equals the number of reachable codes below that smaller cutoff.

**Proof.** The set $R_s$ is, by its definition, the codes satisfying the reachability relation below the smaller cutoff (\texttt{mem\_rset}). Every element of the filtered range below $K$ also satisfies that relation. Conversely, any code satisfying the relation is strictly below the smaller cutoff by the reachability bound (\texttt{rcode\_lt}), and therefore is below $K$ as well. Thus the two filtered sets have exactly the same elements, so their cardinalities agree.

**Key facts.** `Complexity.ExpBFS.mem_rset`, `Complexity.ExpBFS.rcode_lt`.
