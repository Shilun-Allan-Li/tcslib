<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_mul_ite_eq_diag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal collapse of a finite sum

**Claim.** For a finite type $\alpha$, summing $h(y,z)$ weighted by $c$ on the diagonal and zero off the diagonal leaves precisely the diagonal terms $h(y,y)c$.

**Proof.** Rewrite the sum over pairs as an iterated sum, first over $z$ and then over $y$. For each fixed $y$, the factor is zero unless $z=y$, in which case it is $c$. Thus only the term $h(y,y)c$ remains in the inner sum; summing those terms over $y$ gives the result.
