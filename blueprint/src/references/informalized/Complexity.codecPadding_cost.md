<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecPadding_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Encoding Cost Bound

**Claim.** For all natural numbers $\mathrm{first}$ and $L$, the cost of the padding CNF encoding is at most $2L$.

**Proof.** The padding encoding has one unit clause for each index in the range from $\mathrm{first}$ up to, but not including, $L$. Each unit clause has cost two, so the total cost is $2\max(L-\mathrm{first},0)$. Since this number of clauses is at most $L$, the cost is at most $2L$.
