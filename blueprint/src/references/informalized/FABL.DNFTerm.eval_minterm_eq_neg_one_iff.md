<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.eval_minterm_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a minterm

**Claim.** The minterm specifying the signs of $x$ evaluates to $-1$ at $y$ exactly when $y=x$.

**Proof.** By the characterization of term evaluation (FABL.DNFTerm.eval_eq_neg_one_iff), the minterm evaluates to $-1$ at $y$ exactly when every literal in it is satisfied. Its literals are precisely the pairs consisting of a coordinate $i$ and the sign $x_i$. Hence satisfaction says $y_i=x_i$ for every coordinate $i$, which is equality of the two sign vectors. Conversely, if $y=x$, each of these literals is satisfied.

**Key facts.** `FABL.DNFTerm.eval_eq_neg_one_iff`.
