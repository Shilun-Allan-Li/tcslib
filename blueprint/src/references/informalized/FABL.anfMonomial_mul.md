<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.anfMonomial_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of Boolean monomials

**Claim.** The product of the monomials indexed by $S$ and $T$ at $x$ equals the monomial indexed by $S\cup T$ at $x$.

**Proof.** Split into two cases. If every coordinate in $S\cup T$ has nonzero value, then each such value in $\mathbb F_2$ is $1$. All three products are therefore $1$. Otherwise, some coordinate $i\in S\cup T$ has value zero, so the product over $S\cup T$ is zero. If $i\in S$, the product over $S$ is zero and hence the product of the two monomials is zero; if $i\in T$, the same conclusion follows from the product over $T$. In either subcase that product agrees with the product over the union.
