<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: CNF.dual_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the De Morgan dual

**Claim.** For every input, the DNF obtained by interchanging conjunctions and disjunctions in a CNF and flipping each literal evaluates to the Boolean negation of the original CNF.

**Proof.** Write the CNF as a list of clauses. Its dual is the disjunction of the terms obtained by flipping every literal in each clause. Induct on the clause list. For the empty list, the CNF evaluates to true and its dual DNF to false, so the identity holds. For a clause followed by the remaining list, the original evaluation is the conjunction of the head clause's disjunction and the remaining CNF evaluation. By induction, the latter is the negation of the remaining dual DNF evaluation. De Morgan's law therefore turns the negation of the original evaluation into the disjunction of the negated head-clause evaluation and the remaining dual DNF evaluation. For the head clause, induct on its literals: the empty clause has value false, while adjoining a literal makes its evaluation a disjunction. Flipping that literal negates its value (`Literal.flipNeg_eval`), and De Morgan's law identifies the conjunction of the flipped literals with the negation of the clause evaluation. Together these inductions give the claimed equality.

**Key facts.** `Literal.flipNeg_eval`, `Term.eval_cons`, `Clause.eval_cons`.
