<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.exactlyThreePadClause_length_le_eight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of padded clauses

**Claim.** For every clause, the list of clauses produced by padding it with three variables has length at most eight.

**Proof.** Split by the length of the clause's literal list. For zero literals the padding list has eight clauses; for one literal it has four; for two literals it has two; and for three literals it has one. In each of these cases, counting the displayed clauses gives the asserted bound. If the clause has at least four literals, the padding definition returns the empty list, whose length is zero. Thus every possible list length is at most eight.
