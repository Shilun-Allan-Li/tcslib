<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecValidity_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity Formula Characterization

**Claim.** For a finite-state Turing machine $M$, natural numbers $n,s$, and an assignment of Boolean values to every encoded bit, the validity CNF evaluates to true exactly when the assignment is the bit encoding of some codec row.

**Proof.** The proof identifies satisfaction of the validity CNF with the predicate that the assignment is valid, using the equivalence between valid bit assignments and encodings of codec rows (`codecBitsValid_iff`). To see the CNF side of this identification, split the formula into its concatenated components: the input-head and state one-hot formulas, the work-head one-hot formula for each tape, the work-cell clauses for each tape and cell, and the summary clause. Evaluation of concatenated CNFs reduces to satisfaction of every component. For the families indexed by tapes and cells, evaluation of a flat map is equivalent to satisfaction of each member (`codecCnf_eval_flatMap`), and evaluation of a mapped family of clauses is equivalent to satisfaction of every clause (`codecCnf_eval_map`). Each one-hot component holds exactly when there is a unique selected value, with the assignment equal to the corresponding equality indicator (`codecOneHot_eval`). The work-cell and summary clauses express their respective validity conditions directly by the definition of clause evaluation. Thus the whole formula holds precisely when the assignment is valid, and the cited equivalence gives exactly the existence of a codec row whose bit encoding is that assignment.

**Key facts.** `Complexity.codecBitsValid_iff`, `Complexity.codecCnf_eval_flatMap`, `Complexity.codecCnf_eval_map`, `Complexity.codecOneHot_eval`.
