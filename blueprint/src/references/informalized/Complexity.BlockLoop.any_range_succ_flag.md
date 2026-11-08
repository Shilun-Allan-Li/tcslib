<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean :: Complexity.BlockLoop.any_range_succ_flag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Success on an Extended Range

**Claim.** For any Boolean-valued function $F$ on the natural numbers and any $i$, the indicator that $F(i)$ holds or that $F$ holds somewhere below $i$ equals the indicator that $F$ holds somewhere below $i+1$.

**Proof.** The range of natural numbers below $i+1$ consists of the range below $i$ followed by the single index $i$. Therefore its Boolean disjunction under $F$ is the disjunction of $(\mathrm{List.range}\ i).\mathrm{any}\ F$ and $F(i)$. If $F(i)$ is true, both sides are true. If it is false, the disjunction reduces to whether $F$ holds below $i$. This gives the stated equality of singleton Boolean lists.
