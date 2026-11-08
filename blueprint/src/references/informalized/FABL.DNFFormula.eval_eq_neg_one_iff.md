<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Evaluation of a DNF

**Claim.** A DNF formula evaluates to $-1$ at a sign vector if and only if at least one of its terms evaluates to $-1$ there.

**Proof.** By definition, the formula returns $-1$ exactly when the list of terms contains an element satisfying the predicate that the term evaluates to $-1$. The characterization of the list's existential test gives precisely the stated equivalence.
