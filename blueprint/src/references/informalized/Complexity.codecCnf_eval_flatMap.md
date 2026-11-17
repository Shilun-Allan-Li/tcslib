<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecCnf_eval_flatMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a flattened CNF list

**Claim.** The concatenation of the CNFs assigned to the elements of a list evaluates to true under an assignment exactly when every assigned CNF for an element occurring in the list evaluates to true.

**Proof.** CNF evaluation requires every clause in the formula to evaluate to true. The clauses in the flattened list are precisely the clauses contributed by each element of the original list. Therefore all clauses in the flattened formula evaluate to true exactly when, for every element occurring in the list, all clauses of its assigned CNF evaluate to true—that is, when each such CNF evaluates to true.
