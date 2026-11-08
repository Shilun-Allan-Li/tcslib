<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecCnf_eval_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a mapped CNF clause list

**Claim.** The conjunction of the clauses obtained by mapping a list through $f$ evaluates to true exactly when every clause assigned to an element of the list evaluates to true.

**Proof.** CNF evaluation of a list of clauses is the requirement that every clause in that list evaluate to true. The mapped list contains exactly the clause $f(i)$ for each element $i$ of the original list, so this condition is equivalent to requiring that each such clause evaluate to true.
