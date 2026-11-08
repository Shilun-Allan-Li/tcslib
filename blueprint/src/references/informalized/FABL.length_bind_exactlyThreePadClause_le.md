<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.length_bind_exactlyThreePadClause_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding clauses to three literals

**Claim.** For every finite list of DNF terms on $n$ variables, concatenating the exactly-three-literal padding lists produces a list of length at most eight times the number of original terms.

**Proof.** Induct on the list of terms. For the empty list, the concatenation is empty, so the bound holds. For a list with first term $C$ and remaining list $R$, its flattened padding list is the padding list of $C$ followed by the flattened padding list of $R$. The first has length at most eight (\texttt{exactlyThreePadClause_length_le_eight}), and by induction the second has length at most $8|R|$. Adding these bounds gives at most $8+8|R|=8(1+|R|)$, as required.

**Key facts.** `FABL.exactlyThreePadClause_length_le_eight`.
