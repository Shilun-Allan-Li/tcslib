<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_sq_mul_of_orthogonal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted orthogonality identity

**Claim.** If the columns of a real array on finite index sets are mutually orthogonal and each has squared length $c$, then the sum over rows of the squared weighted row sums is $c$ times the sum of the squared weights.

**Proof.** 1. Expand the squared row sums as a sum over ordered pairs of columns using the identity that a sum of squared row sums equals the sum of column-pair inner products (\texttt{sum\_sq\_eq\_sum\_prod}). Applying it to $f(x,y)=b(y)\phi(x,y)$, and factoring the weights out of each inner product (\texttt{sum\_mul\_mul}), rewrites the expression as $\sum_{(y,z)} b(y)b(z)\sum_x\phi(x,y)\phi(x,z)$. 
2. Substitute the assumed orthogonality relation. Every term with $y\ne z$ vanishes, while each diagonal term contributes $b(y)^2c$. The finite sum over pairs therefore reduces to $\sum_y b(y)^2c$, by the diagonal-sum identity (\texttt{sum\_mul\_ite\_eq\_diag}).

**Key facts.** `CommunicationComplexity.Functions.InnerProduct.sum_sq_eq_sum_prod`, `CommunicationComplexity.Functions.InnerProduct.sum_mul_mul`, `CommunicationComplexity.Functions.InnerProduct.sum_mul_ite_eq_diag`.
