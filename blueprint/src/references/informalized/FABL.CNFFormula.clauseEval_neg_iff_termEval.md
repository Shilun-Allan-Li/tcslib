<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.CNFFormula.clauseEval_neg_iff_termEval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause and term evaluations under negation

**Claim.** For a term $C$ and a sign-cube point $x$, the clause evaluation of $C$ at the coordinatewise negation of $x$ is $1$ exactly when the term evaluation of $C$ at $x$ is $-1$.

**Proof.** We prove both implications. Suppose first that the clause evaluation at $-x$ is $1$. Then no literal in $C$ evaluates to $-1$ there. Fix any literal in $C$. Its evaluation at $-x$ is therefore not $-1$, so the coordinate $-x_i$ at its index $i$ is not its required sign $s$. Since both $x_i$ and $s$ are signs, the only possibilities for $x_i$ are $s$ and $-s$; the exclusion $-x_i\ne s$ rules out $x_i=-s$. Hence $x_i=s$, by uniqueness of a sign among these two possibilities (`FABL.CNFFormula.sign_eq_of_ne_neg`). Thus every literal in $C$ has its required sign at $x$, which is equivalent to the term evaluating to $-1$ (`FABL.DNFTerm.eval_eq_neg_one_iff`).

Conversely, suppose the term evaluates to $-1$. Then every literal in $C$ has its required sign at $x$, by the same term characterization. At the negated input, each such literal evaluates to $1$: its indexed coordinate is the negative of its required sign, and a sign cannot equal its own negative. Therefore no literal evaluates to $-1$ at $-x$, so the clause evaluates to $1.

**Key facts.** `FABL.CNFFormula.sign_eq_of_ne_neg`, `FABL.DNFTerm.eval_eq_neg_one_iff`.
