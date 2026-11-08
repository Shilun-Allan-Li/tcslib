<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.char_is_degree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characters have bounded degree

**Claim.** For every subset $S$ and every $d\ge 1$, the Walsh character $\chi_S$ has degree at most $d$ in the multiplicative derivative sense.

**Proof.** The proof starts with the degree-at-most-one case for the character (`char_is_degree_le_one`). It then inducts on $d$. The base case $d=0$ is impossible under the hypothesis $d\ge1$; when $d=1$, the result is exactly the starting case. For each subsequent value, the induction hypothesis gives degree at most the preceding bound, and degree-bound monotonicity (`degree_le_succ`) raises that bound by one to obtain the desired conclusion.

**Key facts.** `LowDegreeTest.char_is_degree_le_one`, `LowDegreeTest.degree_le_succ`.
