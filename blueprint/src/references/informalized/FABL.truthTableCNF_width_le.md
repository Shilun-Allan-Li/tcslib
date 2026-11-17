<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.truthTableCNF_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the truth-table CNF

**Claim.** For any Boolean function on $r$ coordinates, every clause in its truth-table CNF has width $r$, and hence the formula’s width is at most $r$.

**Proof.** Regard the CNF width as the maximum of the widths of its clauses, with the width characterized by the condition that every term has width at most the proposed bound (`DNFFormula.width_le_iff`). Each clause in this truth-table CNF is formed from an assignment and contains one literal for each of the $r$ coordinates, so its width is $r$ (`truthTableCNF_clause_width`). Thus every clause has width at most $r$, proving the bound.

**Key facts.** `FABL.DNFFormula.width_le_iff`, `FABL.truthTableCNF_clause_width`.
