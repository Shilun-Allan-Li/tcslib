<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.anfEval_anfMul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of product coefficients

**Claim.** If the coefficient at $U$ is the sum of $c(S)d(T)$ over pairs with $S\cup T=U$, then its algebraic normal form evaluates to the product of the evaluations of $c$ and $d$.

**Proof.** Expand the evaluation using the definition of the product coefficients, then distribute the finite sums. Reorder the sums so that terms are grouped by a pair $(S,T)$. For each pair, the defining condition selects exactly the union $S\cup T$. The product of the two corresponding monomials is the monomial on that union (`FABL.anfMonomial_mul`). Thus each pair contributes $c(S)d(T)$ times the monomial indexed by $S\cup T$, exactly as in the expanded product of the two evaluations. Rearranging the finite sums proves the identity.

**Key facts.** `FABL.anfMonomial_mul`.
