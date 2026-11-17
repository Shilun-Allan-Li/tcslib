<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean :: Complexity.LogProg.ISGen.card_ball_eq_rset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Reachable and Ball Cardinalities

**Claim.** Under the stated exponential bound on $K$, the $K$-bounded ball at level $K$ has the same cardinality as the finite set of codes reachable from the initial configuration code within the stated code bound.

**Proof.** Write $R(t)$ for the assertion that the code $t$ is reachable. The cardinality comparison theorem for filtered ranges says that filtering the range below $K$ by $R$ gives the same cardinality as the reachable set (`card_filter_rcode`). It therefore suffices to identify the ball with that filtered range. For each $t$, membership in the ball is equivalent to $R(t)$ (`mem_ball_iff_rcode`). If $t$ is in the ball, this equivalence gives reachability, and the reachable-code bound (`rcode_lt`) puts $t$ below the exponential code bound, hence below $K$. Thus $t$ belongs to the filtered range. Conversely, membership in the filtered range already supplies $R(t)$, which by the same equivalence places $t$ in the ball. The two finite sets coincide, so their cardinalities agree.

**Key facts.** `Complexity.ExpBFS.card_filter_rcode`, `Complexity.LogProg.ISGen.mem_ball_iff_rcode`, `Complexity.ExpBFS.rcode_lt`.
