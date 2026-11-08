<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_norm_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gowers norm equality characterizes low degree

**Claim.** The normalized average of the order-$(d+1)$ Gowers products of the sign lift equals $1$ exactly when every such product is $1$.

**Proof.** Each Gowers product of the sign lift is either $1$ or $-1$ (`gowers_product_pm1`). Suppose some product, at a base point $x$ and directions $h_1,\ldots,h_{d+1}$, is not $1$; it must then be $-1$. Every other product is at most $1$, so the finite sum over all base points and directions is strictly less than the sum that would result if every summand were $1$. The hypercube has $2^n$ points (`card_hypercube`), and the space of direction tuples has $2^{n(d+1)}$ elements (`card_multi_hypercube`). Thus the normalizing denominator in the iterated expectation is exactly the number of summands, and the normalized average is strictly less than $1$. This proves that an average equal to $1$ forces every product to be $1$. Conversely, if every order-$(d+1)$ product is $1$, their normalized average is $1 directly. This is precisely the stated low-degree condition.

**Key facts.** `LowDegreeTest.gowers_product_pm1`, `BoolFourier.card_hypercube`, `LowDegreeTest.card_multi_hypercube`.
