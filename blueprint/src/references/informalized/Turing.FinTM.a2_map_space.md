<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bound for the mapped computation

**Claim.** Under the stated head-position and visited-cell assumptions, the simulator uses at most $S+2(2D+1)$ cells through time $t$.

**Proof.** For any simulator tape whose head lies in $[-D,D]$ at every time through $t$, every position in its visited-head set belongs to the integer interval $[-D,D]$. That interval has $2D+1$ elements, so each of the first two simulator tapes uses at most $2D+1$ cells. For each tape corresponding to a tape of $M$, the assumed inclusion of visited-head sets implies that its visited-cell count is at most the corresponding count for $M$. Summing these inequalities over the tapes of $M$ bounds their total contribution by $S$. Finally, split the simulator’s sum over all tapes into its first two tapes and the remaining $M.k$ tapes, using `a2_map_sum` twice. Combining the two bounds gives $S+2(2D+1)$.

**Key facts.** `Turing.FinTM.a2_map_sum`.
