<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.length_to3SATAux_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Encoding Length Bound

**Claim.** For a list of clauses $cs$ and starting index $idx$, the recursive encoding produces at most $cs.flatten.length+2\,cs.length$ 3-clauses.

**Proof.** We induct on the clause list, allowing any starting index. For the empty list, both the encoding and the stated bound are zero. For a nonempty list with first clause $c$ and remaining list $cs$, the encoding is the concatenation of the encoding of $c$ at index $idx$ and the recursive encoding of $cs$ at index $idx+1$. The single-clause bound says the first part has length at most $|c|+2$ (\texttt{SATTo3SAT.length\_transformClause\_le}); the induction hypothesis bounds the second part by the total number of literals in $cs$ plus twice its number of clauses. Since flattening adds the literal counts and the clause-list length increases by one, these bounds sum to the claimed expression.

**Key facts.** `SATTo3SAT.length_transformClause_le`.
