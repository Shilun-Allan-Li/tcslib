<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.eval_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty DNF Evaluation

**Claim.** The DNF formula with no terms evaluates to $1$ at every sign vector.

**Proof.** By definition, the formula evaluates to $-1$ precisely when at least one term evaluates to $-1$. The empty list has no such term, so the defining condition is false and the evaluation is $1$.
