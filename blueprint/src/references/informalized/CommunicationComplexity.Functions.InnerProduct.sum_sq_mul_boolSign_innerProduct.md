<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_sq_mul_boolSign_innerProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parseval identity for inner-product characters

**Claim.** For any real-valued function $b$ on the $n$-bit Boolean inputs, the sum over inputs $x$ of the squared character-weighted sums equals $2^n$ times the sum of $b(y)^2$ over inputs $y$.

**Proof.** Apply the weighted orthogonality identity to the array $\phi(x,y)=(-1)^{\langle x,y\rangle}$, with common squared column length $c=2^n$ and weights $b(y)$. Its required orthogonality condition is supplied by the character-sum computation: summing $\phi(x,y)\phi(x,z)$ over all $x$ gives $2^n$ when $y=z$ and zero otherwise (\texttt{sum\_boolSign\_innerProduct\_mul\_eq\_indicator}). The weighted orthogonality identity (\texttt{sum\_sq\_mul\_of\_orthogonal}) now gives $\sum_y b(y)^2 2^n$, which is the claimed right-hand side.

**Key facts.** `CommunicationComplexity.Functions.InnerProduct.sum_boolSign_innerProduct_mul_eq_indicator`, `CommunicationComplexity.Functions.InnerProduct.sum_sq_mul_of_orthogonal`.
