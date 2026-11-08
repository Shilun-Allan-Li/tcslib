<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_finset_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for finite sums

**Claim.** If every function in a finite family has algebraic degree at most $r$, then their pointwise sum over $\mathbb F_2$ also has algebraic degree at most $r$.

**Proof.** Induct on the finite index set. The empty sum is the zero function, whose degree is at most $r$. In the inductive step, split off the newly inserted function. The degree of a sum is at most the maximum of the degrees of its summands (`functionAlgebraicDegree_add_le_max`). The new summand has degree at most $r$ by hypothesis, and the induction hypothesis gives the same bound for the remaining sum. Their maximum is therefore at most $r$.

**Key facts.** `FABL.functionAlgebraicDegree_add_le_max`.
