<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.innerProduct_zero_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product with zero

**Claim.** For every Boolean input $x$, its mod-$2$ inner product with the all-zero input is false.

**Proof.** Unfold the inner product and the zero input. Each summand is $x_i\wedge 0$, which is false for either value of $x_i$. Thus every term in the finite sum is false, so the sum is false.
