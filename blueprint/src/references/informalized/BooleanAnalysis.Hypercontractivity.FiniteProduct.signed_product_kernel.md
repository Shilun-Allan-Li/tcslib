<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/NoiseKernel.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.signed_product_kernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alternating Product Expansion

**Claim.** For a finite index set, the alternating sum over subsets of $S$ of the products selecting $a_i$ on each subset and $b_i$ elsewhere equals the product selecting $a_i-b_i$ on $S$ and $b_i$ outside it.

**Proof.** Rewrite the product on the right by separating indices in $S$ from those outside $S$, and expand each factor $a_i-b_i$ as $a_i+(-b_i)$. Distributing the product produces one term for each subset $T\subseteq S$: it selects $a_i$ on $T$, $b_i$ on $S\setminus T$, and $b_i$ outside $S$, with sign $(-1)^{|S\setminus T|}$. Since $T\subseteq S$, the exponent is $|S|-|T|$. The product factors over the disjoint regions involved, so this expansion is precisely the stated alternating sum.
