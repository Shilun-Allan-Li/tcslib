<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.generalized_small_set_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generalized Small-Set Expansion

**Claim.** For finite subsets $A,B$ of the Boolean cube, under the stated exponent and correlation hypotheses, their noise inner product is at most $\operatorname{vol}(A)^{(u-1)/u}\operatorname{vol}(B)^{1/p}$.

**Proof.** Apply the two-function hypercontractivity inequality `general_two_function_hypercontractivity` to the indicator functions of $A$ and $B$. It bounds their noise inner product by the corresponding absolute-moment norms. For either finite-set indicator, the absolute value is one on the set and zero outside it, so every positive power has expectation equal to the set's volume, by `expect_abs_indicator_rpow`. The required exponents $(u-1)/u$ and $1/p$ are positive under $p\leq u$ and $u\geq2$, so the indicator moment identity applies. Substituting these two volumes yields the claimed bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.general_two_function_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.expect_abs_indicator_rpow`.
