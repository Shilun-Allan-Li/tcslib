<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.lt_polyBudget_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict polynomial budget bound

**Claim.** For natural numbers $a'$, $k'$, $n$, and $m$ with $n\le m$, one has $a'(n+1)^{k'}<a'(m+1)^{k'}+1$.

**Proof.** From $n\le m$ we get $n+1\le m+1$, and raising both sides to the natural power $k'$ preserves the inequality. Multiplying by $a'\ge0$ gives $a'(n+1)^{k'}\le a'(m+1)^{k'}$. The right-hand side is a natural number, hence is strictly less than its successor, so the desired strict bound follows.
