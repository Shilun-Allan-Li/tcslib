<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.smallQuerySeedCNF_clause_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty clauses in the seed formula

**Claim.** Every clause occurring in the padded seed CNF on $r+r2^r$ coordinates has positive width, provided $r>0$.

**Proof.** Represent the occurring clause by its position in the list defining the padded formula, and consider the three branches in that definition. If the position indexes an existing clause of the seed acceptance CNF, that clause belongs to the truth-table CNF; every such clause has width $r$ (`FABL.truthTableCNF_clause_width`). Lifting a local clause preserves its width (`FABL.liftLocalClause_width`), so the padded clause has width $r>0$. If the position is beyond the existing list but the seed acceptance CNF is nonempty, the construction repeats its first clause. That clause also belongs to the truth-table CNF, so the same width argument gives width $r>0$. In the remaining branch, the construction uses the filler clause, whose width is $1$. Thus every occurring clause has positive width.

**Key facts.** `FABL.truthTableCNF_clause_width`, `FABL.liftLocalClause_width`.
