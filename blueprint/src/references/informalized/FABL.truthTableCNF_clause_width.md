<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.truthTableCNF_clause_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth-Table Clause Width

**Claim.** Every clause in the truth-table CNF has width exactly $r$.

**Proof.** A clause in the formula is, by its construction, the excluding clause associated with some assignment in the truth table. The width theorem for an excluding clause states that its width is exactly the number of coordinates, namely $r$ (`excludingClause_width`).

**Key facts.** `FABL.excludingClause_width`.
