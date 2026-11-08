<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.e3LinPredicate_randomizedValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Value of a Three Sign Constraint

**Claim.** For means $$[0m$[0m$[0m$μ_i∈[-1,1]$, the randomized value of the three-sign equation constraint is $(1+\operatorname{signValue}(b)μ_0μ_1μ_2)/2$.

**Proof.** Let each coordinate be sampled independently from the sign distribution with mean $μ_i$, and let $Y_i$ denote its sampled sign. First, the expectation of the product $\prod_{i=0}^2\operatorname{signValue}(Y_i)$ factors, by independence, into the product of the coordinate expectations. Each coordinate expectation is $μ_i$, so this product expectation is $μ_0μ_1μ_2$. The indicator formula for a three-sign equation (`e3LinPredicate_indicator_eq`) expresses acceptance as $1/2+(\operatorname{signValue}(b)/2)\prod_i\operatorname{signValue}(Y_i)$. Taking expectations, the constant term remains $1/2$ (`pmfExpectation_const`), and the scaled product term is its coefficient times the product expectation (`pmfExpectation_const_mul`). Linearity of expectation (`pmfExpectation_add`) then gives the claimed value.

**Key facts.** `FABL.e3LinPredicate_indicator_eq`, `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_signPMFOfMean`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`.
