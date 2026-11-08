<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.randomization_norm_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-moment preservation

**Claim.** The second moment norm of the randomized expansion, averaged over outcomes and uniform Boolean sign vectors, equals the second moment norm of $f$.

**Proof.** Expand the square in the definition of the randomization norm. For each fixed outcome, the pointwise randomization Parseval identity says that averaging the square over Boolean signs equals the sum of the squared components. Thus the squared randomization norm reduces to the outcome expectation of that component sum. Interchanging the finite sum over components with the expectation (the expectation-of-a-finite-sum identity, `FiniteProduct.expect_sum`) gives the sum, over all components, of their individual squared expectations. The product Parseval identity (`FiniteProduct.parseval`) identifies this sum with the expectation of $f^2$. Both norms are the nonnegative square roots of these quantities, so they are equal.

**Key facts.** `BooleanAnalysis.Hypercontractivity.randomization_pointwise_parseval`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval`.
