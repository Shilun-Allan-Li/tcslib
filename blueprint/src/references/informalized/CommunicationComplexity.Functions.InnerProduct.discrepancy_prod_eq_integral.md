<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.discrepancy_prod_eq_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rectangle Discrepancy as an Iterated Integral

**Claim.** For any subsets $A,B$ of the $n$-bit Boolean inputs, the discrepancy of the mod-$2$ inner product on $A\times B$ equals the iterated integral of the indicator of $A$ times the inner integral of the indicator of $B$ times the sign of the inner product.

**Proof.** Write the discrepancy integral over pairs $(x,y)$. Membership in the product set $A\times B$ is equivalent to the two conditions $x\in A$ and $y\in B$, so its integrand is the product of the corresponding indicators and the sign of the inner product. The measure on the product space is the product of the two measures. Fubini's theorem applies because the space is finite, and rewrites the integral over pairs as an iterated integral. For each fixed $x$, the indicator of $A$ is constant in the inner variable and can be factored out, yielding the displayed formula.
