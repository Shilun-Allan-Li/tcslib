<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/DirectionalDerivatives.lean :: FABL.anfMonomial_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expansion of a monomial on a sum

**Claim.** The monomial indexed by $S$ at $x+y$ is the sum over $T\subseteq S$ of the monomial at $x$ indexed by $T$ times the monomial at $y$ indexed by $S\setminus T$.

**Proof.** At each coordinate $i$, the value of $x+y$ is $x_i+y_i$. Expanding the finite product of these sums by distributivity amounts to choosing, for each $i\in S$, whether its factor contributes $x_i$ or $y_i$. The coordinates chosen from the $x$ factors form a subset $T\subseteq S$, while the remaining coordinates form $S\setminus T$. Grouping the expansion by this choice gives exactly the stated sum.
