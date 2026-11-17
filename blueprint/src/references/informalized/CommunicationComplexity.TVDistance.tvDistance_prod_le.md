<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.tvDistance_prod_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Total Variation Bound

**Claim.** For the product measures of two pairs of probability measures, the total variation distance between the products is at most the sum of the two marginal total variation distances.

**Proof.** Write the singleton masses of μ₁, μ₂, ν₁, and ν₂ as a, b, c, and d, respectively. Rewriting all three distances as half-sums over singleton masses (`tvDistance_eq_half_sum`), the product-distance bound reduces to an inequality for the sums of absolute differences of product weights. The weights b and c are nonnegative and each sums to one. The product-weight inequality (`sum_prod_abs_le`) then bounds the sum of $|a(x)b(y)-c(x)d(y)|$ by the sum of the two marginal absolute-difference sums. Finally, singleton masses of product measures factor as products of the marginal singleton masses (`prod_measureReal_singleton`), so this inequality is precisely the desired bound after multiplying by one half.

**Key facts.** `CommunicationComplexity.TVDistance.tvDistance_eq_half_sum`, `CommunicationComplexity.TVDistance.sum_prod_abs_le`, `CommunicationComplexity.TVDistance.prod_measureReal_singleton`.
