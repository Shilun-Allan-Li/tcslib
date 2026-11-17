<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_norm_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gowers norm bound for sign lifts

**Claim.** For every order $k$, the power-form Gowers norm of the sign lift of a Boolean function is at most $1$.

**Proof.** The norm is the sum of the Gowers products over all base points and direction tuples, divided by the corresponding positive normalizing powers of $2$. Each product is either $1$ or $-1$ (`gowers_product_pm1`), so every summand is at most $1$. Summing this bound over the direction tuples and using that there are $2^{nk}$ such tuples (`card_multi_hypercube`) bounds the inner sum by its number of terms. Summing over the $2^n$ base points (`card_hypercube`) gives the same bound for the outer sum. Dividing by the positive normalization yields a value at most $1$.

**Key facts.** `LowDegreeTest.gowers_product_pm1`, `LowDegreeTest.card_multi_hypercube`, `BoolFourier.card_hypercube`.
