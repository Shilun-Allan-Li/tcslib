<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.truthTableCNF_size_le_threeQueryBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth-Table Size and Query Budget

**Claim.** For positive $r$, the truth-table CNF has at most $r2^r$ clauses.

**Proof.** The general truth-table size bound gives at most $2^r$ clauses. Since $r>0$, multiplying $2^r$ by $r$ can only increase it, so the size is at most $r2^r$ (`truthTableCNF_size_le`).

**Key facts.** `FABL.truthTableCNF_size_le`.
