<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/Basic.lean :: FABL.monomial_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of a Sign Monomial

**Claim.** For every nonnegative integer $n$, every subset $S$ of the $n$ coordinates, and every sign vector $x\in\{\pm1\}^n$, the square of the monomial indexed by $S$ at $x$ is $1$.

**Proof.** Proceed by induction on the finite set $S$. For $S=\varnothing$, the product defining the monomial is empty and hence equals $1$, so its square is $1$. If $S$ is obtained by adjoining a coordinate $i$ to a set for which the claim holds, the product over $S$ factors as the sign at coordinate $i$ times the product over the smaller set. Squaring this factorization gives the product of their squares. The induction hypothesis makes the tail square equal to $1$, and every sign value is either $-1$ or $1$ (the fact `signValue_eq_neg_one_or_one`); in either case its square is $1$.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
