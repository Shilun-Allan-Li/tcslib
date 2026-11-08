<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.truthTableCNF_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth-Table CNF Size Bound

**Claim.** The truth-table CNF has at most $2^r$ clauses.

**Proof.** The formula lists one excluding clause for each assignment in a filtered subset of the full sign cube. Its number of clauses is therefore the size of that subset, which is at most the number of assignments in the cube. Each of the $r$ coordinates has two choices, so the cube has $2^r$ assignments.
