<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parseval Identity for Components

**Claim.** The expected square of a function on a finite product space equals the sum, over all coordinate subsets, of the expected squares of its components.

**Proof.** First compare two conditional expectations. Self-adjointness of conditional expectation moves one conditional expectation across the product inside the expectation; the composition rule then identifies the result with conditioning on the intersection. Thus, for subsets $A,B$, $\mathbb E[(\mathbb E[f\mid A])(\mathbb E[f\mid B])]=\mathbb E[f\,\mathbb E[f\mid A\cap B]]$. Expand the square of the component indexed by $S$ using its alternating sum over subsets of $S$. Distribute the expectation across these finite sums and use the preceding identity on each pair of terms. The resulting expression is the signed intersection energy of $S$ applied to the function $T\mapsto\mathbb E[f\,\mathbb E[f\mid T]]$. Now sum over all $S$. The signed powerset-intersection identity collapses this sum to the value at the full coordinate set. Conditioning on the full set leaves $f$ unchanged, so the result is $\mathbb E[f^2]$, as claimed.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_comp`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_selfAdjoint`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum`, `BooleanAnalysis.Hypercontractivity.sum_powerset_signed_inter`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.
