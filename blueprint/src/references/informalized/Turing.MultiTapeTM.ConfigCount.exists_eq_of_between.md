<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.ConfigCount.exists_eq_of_between -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainment of intermediate integer values

**Claim.** For an integer sequence starting at zero whose successive differences have absolute value at most one, every integer between zero and its value at time $t$ is attained at some index at most $t$.

**Proof.** Induct on $t$. At time zero, the only integer between zero and the sequence's value is zero, attained at index zero. For the successor step, let $y$ lie between zero and $p(t+1)$. If it also lies between zero and $p(t)$, the induction hypothesis supplies an index at most $t$, which is also at most $t+1$. Otherwise, the step bound $|p(t+1)-p(t)|\le1$ forces the endpoint $p(t+1)$ itself to equal $y$: an integer cannot pass from one side of $y$ to the other in a step of size at most one without landing on $y$. In that case index $t+1$ works.
