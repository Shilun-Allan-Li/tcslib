<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Contraction.lean :: BooleanAnalysis.Hypercontractivity.partialNoise_insert -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Insertion of a partial-noise coordinate

**Claim.** For a coordinate $i$ outside $J$, partial noise on $J\cup\{i\}$ equals applying the one-coordinate noise at rate $r_i$ to partial noise on $J$.

**Proof.** Fix an outcome $x$. In the one-coordinate noise formula, the only additional operation beyond the identity is the coordinate Laplacian, which subtracts the conditional expectation given all coordinates except $i$. Expand that conditional expectation of the partial-noise sum term by term; linearity of expectation over finite sums (`expect_sum_mul`) allows this, and conditioning a component on the coordinates other than $i$ leaves it unchanged when $i\notin S$ and gives zero when $i\in S$ (`condExp_component`). Thus the coordinate-noise expression has, for each set $S$, its original partial-noise contribution multiplied by the factor corresponding to whether $i$ belongs to $S$. If $i\in S$, then $i\notin J$ implies it is absent from $S\cap J$, so inserting $i$ into the new intersection contributes the factor $r_i$. If $i\notin S$, the intersection is unchanged. In both cases the resulting coefficient is exactly the coefficient in partial noise indexed by $J\cup\{i\}$. Summing over $S$ proves equality at every $x$, hence equality of the functions.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum_mul`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_component`.
