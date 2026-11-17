<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecInputEquality_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input equality formula evaluation

**Claim.** The input-equality CNF evaluates to true on the row-selected assignment exactly when the input fields of the two rows are equal.

**Proof.** Fix an input coordinate. Its two clauses require the two selected row bits to agree: if the bits differ, one of the clauses is false, and if they agree, both clauses are true. Thus this coordinate's CNF evaluates to true exactly when the two rows have the same bit there. The CNF evaluation rule for a concatenation (`Complexity.codecCnf_eval_flatMap`) says that the full formula is true exactly when every coordinate's two-clause check is true. Hence it is true precisely when the input functions agree at every coordinate, which is equivalent to equality of the input fields by function extensionality.

**Key facts.** `Complexity.codecCnf_eval_flatMap`.
