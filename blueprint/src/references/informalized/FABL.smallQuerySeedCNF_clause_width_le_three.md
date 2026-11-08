<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.smallQuerySeedCNF_clause_width_le_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width bound for seed formula clauses

**Claim.** If $0<r<3$, every clause occurring in the padded seed CNF on $r+r2^r$ coordinates has width at most $3$.

**Proof.** Represent the clause by its position in the list defining the padded formula and split according to the construction's three branches. If the position indexes an existing seed acceptance clause, that clause belongs to the truth-table CNF, so its width is $r$ (`FABL.truthTableCNF_clause_width`). Lifting the clause preserves its width (`FABL.liftLocalClause_width`), and hence the padded clause has width $r<3$. If the position is beyond the existing list but that list is nonempty, the construction repeats its first clause; it too belongs to the truth-table CNF, and the same two facts give width $r<3$. If the seed acceptance CNF is empty, the construction uses the singleton filler clause, which has width $1\le3$. Each branch therefore gives the required bound.

**Key facts.** `FABL.truthTableCNF_clause_width`, `FABL.liftLocalClause_width`.
