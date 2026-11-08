<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.mass_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalization of Product Mass

**Claim.** The sum of the product mass over all product outcomes is $1$.

**Proof.** Expand the sum over product outcomes of the product of coordinate weights. The finite product-sum identity factors this into the product, over coordinates, of the sums of their weights. Each coordinate weight sum is $1$ by the probability-space hypothesis, so their product is $1$.
