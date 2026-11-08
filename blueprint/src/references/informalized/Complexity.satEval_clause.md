<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause Evaluation Pass

**Claim.** For a clause whose variable indices occur in the certificate word, the evaluator processes its doubled serialization in at most three times the serialization length, updating the clause accumulator to include the clause's truth value and returning to formula phase.

**Proof.** Proceed by induction on the clause. For the empty clause, its serialization is the single delimiter bit. The evaluator takes two steps to process that doubled bit, leaves the clause accumulator false, and returns to formula phase; this agrees with the empty clause's truth value. The bound follows from the resulting two steps.

For a clause with head literal $(v,b)$ and tail $C$, first split the doubled serialization into the doubled encoding of the head literal followed by the doubled serialization of $C$. The variable bound for the head follows from its membership in the whole clause, and the tail inherits the same bound. The literal-processing result (`Complexity.satEval_literal`) processes the head in $3v+8$ steps and changes the clause accumulator from $c$ to $c\vee(u_v=b)$. Apply the induction hypothesis to the tail with that updated accumulator, starting at the new input position. The run concatenation law (`Turing.MultiTapeTM.runFrom_add`) combines these consecutive runs. The clause evaluation recursion identifies the resulting accumulator with $c\vee C(u)$, and the serialization-length calculation shows the total time is at most three times the full clause-serialization length.

**Key facts.** `Complexity.satEval_literal`, `Turing.MultiTapeTM.runFrom_add`.
