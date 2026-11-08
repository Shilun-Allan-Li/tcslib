<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.pmfExpectation_multilinearExtension_productLaw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multilinear Extension and Product Expectations

**Claim.** Under independent coordinate laws, the expectation of the predicate's multilinear extension evaluated at the sampled coordinate values equals that extension evaluated at the individual coordinate means.

**Proof.** Expand the multilinear extension as a sum over subsets $S$ of its Fourier coefficient times the corresponding product of coordinate values. Linearity of expectation (`pmfExpectation_sum`) reduces the claim to each such term, and the constant-multiple rule for expectation (`pmfExpectation_const_mul`) removes its fixed Fourier coefficient. For a fixed $S$, extend the product over $S$ to a product over every coordinate by assigning factor $g_i$ on coordinates in $S$ and the constant $1$ elsewhere. The product-expectation formula for independent laws (`pmfExpectation_independentProductPMF_prod`) factors its expectation into the product of the coordinate expectations. Each factor is the mean of $g_i$ on $S$, and is $1$ off $S$ by normalization (`pmfExpectation_const_one`). Thus this product is precisely the product of coordinate means over $S$. Substituting this into each term of the finite Fourier expansion gives the multilinear extension evaluated at the means.

**Key facts.** `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_const_one`.
