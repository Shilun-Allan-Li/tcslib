<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_sq_eq_sum_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared row sums and column pairs

**Claim.** For a real-valued array on finite sets $\alpha$ and $\beta$, the sum of the squared row sums equals the sum over ordered pairs of columns of their inner products.

**Proof.** First interchange the order of summation, writing the left side as the sum over $x\in\alpha$ of the square of its row sum. For each fixed $x$, expand that square as a product of two sums. The finite product-of-sums identity expresses it as $\sum_{(y,z)\in\beta\times\beta} f(x,y)f(x,z)$. Interchange the finite sums over $x$ and $(y,z)$; the result is $\sum_{(y,z)}\sum_x f(x,y)f(x,z)$, as required.
