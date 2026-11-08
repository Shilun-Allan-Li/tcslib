<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.exists_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalent Bounded Witnesses

**Claim.** If $R_1(a)$ and $R_2(a)$ do not both hold, then there is a common witness in the range $a+1\leq m<K$ exactly when there is one in the range $a\leq m<K$.

**Proof.** A witness with $a+1\leq m$ already satisfies $a\leq m$, so it gives a witness for the larger range. Conversely, take a witness with $a\leq m<K$. If $m=a$, its two predicate properties contradict the hypothesis that they do not both hold at $a$. Hence $m\ne a$, and the natural-number ordering forces $a<m$. This same witness therefore belongs to the range $a+1\leq m<K$.
