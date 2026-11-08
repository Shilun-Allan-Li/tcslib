<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Degree.lean :: BooleanAnalysis.GaussianSpace.totalDegree_finset_prod_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total degree of a finite product

**Claim.** For a finite set $S$ and nonzero real multivariate polynomials $P_i$ for each $i\in S$, the total degree of their product is the sum of their total degrees.

**Proof.** Proceed by induction on the finite set $S$. For the empty set, the product is $1$ and the sum of degrees is $0$, so the equality holds. For the inductive step, write $S=\{a\}\cup S'$ with $a\notin S'$. Every factor indexed by $S'$ is still nonzero, and the product over $S'$ is consequently nonzero. The total-degree formula for the product of two nonzero polynomials over a domain says that the degree of $P_a$ times this product is the sum of their degrees. The induction hypothesis evaluates the degree of the product over $S'$ as the sum of its factors' degrees; adding the degree of $P_a$ gives the desired sum over $S$.
