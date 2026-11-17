<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.card_support_prod_one_add_X -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support size of a product polynomial

**Claim.** The polynomial $\prod_{i\in\mathrm{Fin}(n)}(1+X_i)$ has exactly $2^n$ monomials with nonzero coefficient.

**Proof.** For each subset $T\subseteq\mathrm{Fin}(n)$, let $e_T$ be the exponent vector that is $1$ on $T$ and $0$ elsewhere. Expanding the product by choosing either $1$ or $X_i$ in each factor gives one monomial with exponent vector $e_T$ for each subset $T$. Distinct subsets give distinct exponent vectors, since membership of each index is recovered from whether its exponent is $1$. Each resulting monomial has coefficient $1$, which is nonzero. Consequently, the support consists of exactly these distinct monomials, one for each subset of an $n$-element set, and hence has cardinality $2^n$.
