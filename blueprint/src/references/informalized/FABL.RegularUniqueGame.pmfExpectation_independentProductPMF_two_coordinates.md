<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.pmfExpectation_independentProductPMF_two_coordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Coordinate Product Expectation

**Claim.** For distinct coordinates under independent coordinate laws, the expectation of a function of those two coordinates is the iterated expectation under their respective laws.

**Proof.** For each sample, write its value under the two-coordinate function as a finite sum over all pairs $(a,b)$, retaining only the pair equal to the sample's values at the two selected coordinates. More precisely, use the indicator of the event that both coordinates equal $(a,b)$; exactly one summand survives, so this sum recovers the original value. It remains to compute the expectation of each indicator. Factor that indicator as a product of coordinatewise indicators: at the first coordinate it tests equality with $a$, at the second it tests equality with $b$, and at all other coordinates the factor is $1$. The product-expectation formula for independent product laws (`pmfExpectation_independentProductPMF_prod`) therefore makes its expectation the product of the two marginal probabilities. The other coordinate factors have expectation $1$ (`pmfExpectation_const_one`), while the two selected factors have expectations $(\mu_j(a))_{\mathbb R}$ and $(\mu_k(b))_{\mathbb R}$ by the finite definition of expectation. Finally, interchange the finite sums with expectation (`pmfExpectation_sum`), pull the fixed value $F(a,b)$ out of each expectation (`pmfExpectation_mul_const`), and distribute the marginal probabilities across the iterated sum. The resulting expression is exactly the iterated expectation under the two marginal laws.

**Key facts.** `FABL.pmfExpectation_const_one`, `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_mul_const`.
